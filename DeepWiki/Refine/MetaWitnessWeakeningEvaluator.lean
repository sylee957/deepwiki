/-! # Partial meta-level witness weakening

An executable, fuel-indexed evaluator models recursive witness weakening with distinct ready and
suspended states. Its product result records contravariant domain recursion and delays covariant
codomain recursion until the two endpoint arguments are supplied.
-/

namespace DeepWiki.Refine.MetaWitnessWeakeningEvaluator

/-- Untyped terms inspected by the partial witness-weakening evaluator. -/
inductive Term (Constant : Type) where
  /-- A de Bruijn variable or local name. -/
  | bound (index : Nat)
  /-- A registered global constant. -/
  | global (constant : Constant)
  /-- A flattened application with a separate head and argument list. -/
  | app (head : Term Constant) (arguments : List (Term Constant))
  /-- A lambda with its domain annotation and de Bruijn body. -/
  | lam (domain body : Term Constant)
  /-- A dependent product with its domain and de Bruijn codomain. -/
  | pi (domain codomain : Term Constant)
  /-- An application of the registered universe-relation family to two endpoints. -/
  | universeRelation (left right : Term Constant)
  deriving Repr

namespace Term

/-- Lift a variable renaming through one binder. -/
def upRenaming (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | index + 1 => ρ index + 1

/-- Rename every free de Bruijn variable of a term. -/
def rename (ρ : Nat → Nat) : Term Constant → Term Constant
  | .bound index => .bound (ρ index)
  | .global constant => .global constant
  | .app head arguments => .app (head.rename ρ) (arguments.map (rename ρ))
  | .lam domain body => .lam (domain.rename ρ) (body.rename (upRenaming ρ))
  | .pi domain codomain => .pi (domain.rename ρ) (codomain.rename (upRenaming ρ))
  | .universeRelation left right =>
      .universeRelation (left.rename ρ) (right.rename ρ)

/-- Lift a simultaneous substitution through one binder. -/
def upSubstitution (substitution : Nat → Term Constant) : Nat → Term Constant
  | 0 => .bound 0
  | index + 1 => (substitution index).rename Nat.succ

/-- Apply a simultaneous de Bruijn substitution to a term. -/
def substitute (substitution : Nat → Term Constant) : Term Constant → Term Constant
  | .bound index => substitution index
  | .global constant => .global constant
  | .app head arguments =>
      .app (head.substitute substitution) (arguments.map (substitute substitution))
  | .lam domain body =>
      .lam (domain.substitute substitution) (body.substitute (upSubstitution substitution))
  | .pi domain codomain =>
      .pi (domain.substitute substitution) (codomain.substitute (upSubstitution substitution))
  | .universeRelation left right =>
      .universeRelation (left.substitute substitution) (right.substitute substitution)

/-- Instantiate the outermost binder of a term. -/
def instantiate (body argument : Term Constant) : Term Constant :=
  body.substitute fun
    | 0 => argument
    | index + 1 => .bound index

/-- Form a flattened application, leaving an empty application unchanged. -/
def mkApp (head : Term Constant) (arguments : List (Term Constant)) : Term Constant :=
  match arguments with
  | [] => head
  | _ :: _ =>
      match head with
      | .app function existing => .app function (existing ++ arguments)
      | _ => .app head arguments

/-- Whether a term is a local variable or registered global head. -/
def isAtomicHead : Term Constant → Bool
  | .bound _ | .global _ => true
  | _ => false

end Term

/-- A ready meta-level function for transforming relation witnesses. -/
inductive WeakeningFunction (Constant : Type) where
  /-- The input witness is returned unchanged. -/
  | identity
  /-- A universe witness is projected from one relation-record shape to another. -/
  | universeProjection
      (sourceLeft sourceRight targetLeft targetRight : Term Constant)
  /-- A dependent product first weakens its domain backward and later its codomain forward. -/
  | dependentProduct
      (domainBackward : WeakeningFunction Constant)
      (sourceDomain sourceCodomain targetDomain targetCodomain : Term Constant)
  deriving Repr

/-- A completed witness transformer or a suspended pair of lambda bodies. -/
inductive Result (Constant : Type) where
  /-- A completed witness-transforming function. -/
  | wfun (function : WeakeningFunction Constant)
  /-- Two lambda bodies waiting for their respective endpoint arguments. -/
  | wsuspend (sourceBody targetBody : Term Constant)
  deriving Repr

/-- Ready and suspended evaluator states are disjoint. -/
theorem Result.wfun_ne_wsuspend (function : WeakeningFunction Constant)
    (sourceBody targetBody : Term Constant) :
    Result.wfun function ≠ Result.wsuspend sourceBody targetBody := by
  intro equality
  cases equality

/-- Fuel-indexed partial evaluation of witness weakening between two inspected types. -/
def evaluate : Nat → Term Constant → Term Constant → Option (Result Constant)
  | 0, _, _ => none
  | fuel + 1, source, target =>
      match source, target with
      | .universeRelation sourceLeft sourceRight,
          .universeRelation targetLeft targetRight =>
          some (.wfun (.universeProjection
            sourceLeft sourceRight targetLeft targetRight))
      | .pi sourceDomain sourceCodomain, .pi targetDomain targetCodomain =>
          match evaluate fuel targetDomain sourceDomain with
          | some (.wfun domainBackward) =>
              some (.wfun (.dependentProduct domainBackward
                sourceDomain sourceCodomain targetDomain targetCodomain))
          | _ => none
      | .app sourceHead sourceArguments, .app targetHead targetArguments =>
          if sourceHead.isAtomicHead then
            some (.wfun .identity)
          else
            match sourceArguments, targetArguments with
            | sourceArgument :: sourceTail, targetArgument :: targetTail =>
                match evaluate fuel sourceHead targetHead with
                | some (.wsuspend sourceBody targetBody) =>
                    evaluate fuel
                      (Term.mkApp (sourceBody.instantiate sourceArgument) sourceTail)
                      (Term.mkApp (targetBody.instantiate targetArgument) targetTail)
                | _ => none
            | _, _ => none
      | .lam _ sourceBody, .lam _ targetBody => some (.wsuspend sourceBody targetBody)
      | .bound _, _ | .global _, _ => some (.wfun .identity)
      | _, _ => none

/-- Resume the delayed codomain recursion stored by a dependent-product transformer. -/
def WeakeningFunction.resumeCodomain (fuel : Nat) :
    WeakeningFunction Constant → Term Constant → Term Constant →
      Option (WeakeningFunction Constant)
  | .dependentProduct _ _ sourceCodomain _ targetCodomain,
      sourceEndpoint, targetEndpoint =>
      match evaluate fuel
          (sourceCodomain.instantiate sourceEndpoint)
          (targetCodomain.instantiate targetEndpoint) with
      | some (.wfun codomainForward) => some codomainForward
      | _ => none
  | _, _, _ => none

/-- A proof-relevant trace of one successful evaluator run. -/
inductive Derivation :
    Nat → Term Constant → Term Constant → Result Constant → Type where
  /-- Universe-relation applications create a ready projection function. -/
  | universeRelation {fuel : Nat}
      {sourceLeft sourceRight targetLeft targetRight : Term Constant} :
      Derivation (fuel + 1)
        (.universeRelation sourceLeft sourceRight)
        (.universeRelation targetLeft targetRight)
        (.wfun (.universeProjection sourceLeft sourceRight targetLeft targetRight))
  /-- Products recurse from the target domain to the source domain. -/
  | product {fuel : Nat}
      {sourceDomain sourceCodomain targetDomain targetCodomain : Term Constant}
      {domainBackward : WeakeningFunction Constant}
      (domainDerivation : Derivation fuel targetDomain sourceDomain (.wfun domainBackward)) :
      Derivation (fuel + 1)
        (.pi sourceDomain sourceCodomain) (.pi targetDomain targetCodomain)
        (.wfun (.dependentProduct domainBackward
          sourceDomain sourceCodomain targetDomain targetCodomain))
  /-- Applications with a local or global source head immediately use identity. -/
  | atomicApplication {fuel : Nat} {sourceHead targetHead : Term Constant}
      {sourceArguments targetArguments : List (Term Constant)}
      (atomic : sourceHead.isAtomicHead = true) :
      Derivation (fuel + 1)
        (.app sourceHead sourceArguments) (.app targetHead targetArguments)
        (.wfun .identity)
  /-- A non-atomic application resumes only after its function exposes two lambda bodies. -/
  | resumeApplication {fuel : Nat} {sourceHead targetHead : Term Constant}
      {sourceArgument targetArgument sourceBody targetBody : Term Constant}
      {sourceTail targetTail : List (Term Constant)} {result : Result Constant}
      (nonAtomic : sourceHead.isAtomicHead = false)
      (functionDerivation :
        Derivation fuel sourceHead targetHead (.wsuspend sourceBody targetBody))
      (bodyDerivation : Derivation fuel
        (Term.mkApp (sourceBody.instantiate sourceArgument) sourceTail)
        (Term.mkApp (targetBody.instantiate targetArgument) targetTail) result) :
      Derivation (fuel + 1)
        (.app sourceHead (sourceArgument :: sourceTail))
        (.app targetHead (targetArgument :: targetTail)) result
  /-- A pair of lambdas suspends its two bodies without inspecting them. -/
  | lambda {fuel : Nat} {sourceDomain sourceBody targetDomain targetBody : Term Constant} :
      Derivation (fuel + 1)
        (.lam sourceDomain sourceBody) (.lam targetDomain targetBody)
        (.wsuspend sourceBody targetBody)
  /-- A local-variable source uses the identity fallback. -/
  | bound {fuel index : Nat} {target : Term Constant} :
      Derivation (fuel + 1) (.bound index) target (.wfun .identity)
  /-- A registered-global source uses the identity fallback. -/
  | global {fuel : Nat} {constant : Constant} {target : Term Constant} :
      Derivation (fuel + 1) (.global constant) target (.wfun .identity)

/-- Every proof-relevant trace is accepted by the executable evaluator. -/
theorem Derivation.sound
    (derivation : Derivation fuel source target result) :
    evaluate fuel source target = some result := by
  induction derivation with
  | universeRelation => rfl
  | product _ inductionHypothesis =>
      simp only [evaluate, inductionHypothesis]
  | atomicApplication atomic =>
      simp only [evaluate, atomic, if_true]
  | resumeApplication nonAtomic _ _ functionInduction bodyInduction =>
      simp [evaluate, nonAtomic, functionInduction, bodyInduction]
  | lambda => rfl
  | bound => rfl
  | global => rfl

/-- Successful derivations have a deterministic result. -/
theorem Derivation.output_unique
    (first : Derivation fuel source target firstResult)
    (second : Derivation fuel source target secondResult) :
    firstResult = secondResult := by
  have equality : some firstResult = some secondResult :=
    first.sound.symm.trans second.sound
  exact Option.some.inj equality

/-- Universe-relation weakening immediately yields its projection plan. -/
theorem evaluate_universeRelation (fuel : Nat)
    (sourceLeft sourceRight targetLeft targetRight : Term Constant) :
    evaluate (fuel + 1)
      (.universeRelation sourceLeft sourceRight)
      (.universeRelation targetLeft targetRight) =
      some (.wfun (.universeProjection
        sourceLeft sourceRight targetLeft targetRight)) := rfl

/-- Product evaluation reverses the domain request and records a forward codomain continuation. -/
theorem evaluate_pi (fuel : Nat)
    (sourceDomain sourceCodomain targetDomain targetCodomain : Term Constant) :
    evaluate (fuel + 1)
      (.pi sourceDomain sourceCodomain) (.pi targetDomain targetCodomain) =
      match evaluate fuel targetDomain sourceDomain with
      | some (.wfun domainBackward) =>
          some (.wfun (.dependentProduct domainBackward
            sourceDomain sourceCodomain targetDomain targetCodomain))
      | _ => none := rfl

/-- Product construction rejects a suspended result for its contravariant domain request. -/
theorem evaluate_pi_of_domainSuspended (fuel : Nat)
    (sourceDomain sourceCodomain targetDomain targetCodomain : Term Constant)
    (sourceBody targetBody : Term Constant)
    (domainSuspends :
      evaluate fuel targetDomain sourceDomain = some (.wsuspend sourceBody targetBody)) :
    evaluate (fuel + 1)
      (.pi sourceDomain sourceCodomain) (.pi targetDomain targetCodomain) = none := by
  rw [evaluate_pi, domainSuspends]

/-- Resuming a product plan weakens the instantiated source codomain toward the target codomain. -/
theorem WeakeningFunction.resumeCodomain_dependentProduct (fuel : Nat)
    (domainBackward : WeakeningFunction Constant)
    (sourceDomain sourceCodomain targetDomain targetCodomain : Term Constant)
    (sourceEndpoint targetEndpoint : Term Constant) :
    resumeCodomain fuel
      (.dependentProduct domainBackward
        sourceDomain sourceCodomain targetDomain targetCodomain)
      sourceEndpoint targetEndpoint =
      match evaluate fuel
          (sourceCodomain.instantiate sourceEndpoint)
          (targetCodomain.instantiate targetEndpoint) with
      | some (.wfun codomainForward) => some codomainForward
      | _ => none := rfl

/-- Product resumption rejects a suspended codomain result rather than treating it as ready. -/
theorem WeakeningFunction.resumeCodomain_rejectsSuspension (fuel : Nat)
    (domainBackward : WeakeningFunction Constant)
    (sourceDomain sourceCodomain targetDomain targetCodomain : Term Constant)
    (sourceEndpoint targetEndpoint sourceBody targetBody : Term Constant)
    (codomainSuspends :
      evaluate fuel
        (sourceCodomain.instantiate sourceEndpoint)
        (targetCodomain.instantiate targetEndpoint) =
        some (.wsuspend sourceBody targetBody)) :
    resumeCodomain fuel
      (.dependentProduct domainBackward
        sourceDomain sourceCodomain targetDomain targetCodomain)
      sourceEndpoint targetEndpoint = none := by
  rw [resumeCodomain_dependentProduct, codomainSuspends]

/-- A registered-global-headed application uses identity without inspecting its arguments. -/
theorem evaluate_globalApplication (fuel : Nat) (constant : Constant)
    (sourceArguments targetArguments : List (Term Constant)) (targetHead : Term Constant) :
    evaluate (fuel + 1)
      (.app (.global constant) sourceArguments) (.app targetHead targetArguments) =
      some (.wfun .identity) := rfl

/-- A local-variable-headed application uses identity without inspecting its arguments. -/
theorem evaluate_boundApplication (fuel index : Nat)
    (sourceArguments targetArguments : List (Term Constant)) (targetHead : Term Constant) :
    evaluate (fuel + 1)
      (.app (.bound index) sourceArguments) (.app targetHead targetArguments) =
      some (.wfun .identity) := rfl

/-- A bare registered global uses identity regardless of the target term. -/
theorem evaluate_global (fuel : Nat) (constant : Constant) (target : Term Constant) :
    evaluate (fuel + 1) (.global constant) target = some (.wfun .identity) := rfl

/-- A bare local variable uses identity regardless of the target term. -/
theorem evaluate_bound (fuel index : Nat) (target : Term Constant) :
    evaluate (fuel + 1) (.bound index) target = some (.wfun .identity) := rfl

/-- A lambda pair evaluates to a suspended pair of bodies. -/
theorem evaluate_lambda (fuel : Nat)
    (sourceDomain sourceBody targetDomain targetBody : Term Constant) :
    evaluate (fuel + 1)
      (.lam sourceDomain sourceBody) (.lam targetDomain targetBody) =
      some (.wsuspend sourceBody targetBody) := rfl

/-- Applying two lambdas resumes weakening after independently substituting both endpoints. -/
theorem evaluate_lambdaApplication (fuel : Nat)
    (sourceDomain sourceBody targetDomain targetBody : Term Constant)
    (sourceArgument targetArgument : Term Constant)
    (sourceTail targetTail : List (Term Constant)) :
    evaluate (fuel + 2)
      (.app (.lam sourceDomain sourceBody) (sourceArgument :: sourceTail))
      (.app (.lam targetDomain targetBody) (targetArgument :: targetTail)) =
      evaluate (fuel + 1)
        (Term.mkApp (sourceBody.instantiate sourceArgument) sourceTail)
        (Term.mkApp (targetBody.instantiate targetArgument) targetTail) := rfl

/-- A universe relation applied as a function is an unsupported composite head. -/
def unsupportedComposite : Term Unit :=
  .app (.universeRelation (.global ()) (.global ())) [.global ()]

/-- The evaluator explicitly rejects the unsupported composite at every fuel bound. -/
theorem evaluate_unsupportedComposite (fuel : Nat) :
    evaluate fuel unsupportedComposite unsupportedComposite = none := by
  cases fuel with
  | zero => rfl
  | succ remaining =>
      cases remaining <;> rfl

end DeepWiki.Refine.MetaWitnessWeakeningEvaluator
