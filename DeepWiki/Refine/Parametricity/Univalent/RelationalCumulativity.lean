import DeepWiki.Refine.Parametricity.Univalent.Typing

/-! # Relational cumulativity for univalent parametricity

Applied relation fibers preserve cumulative conversion after normalizing projected universe and
dependent-product packages. -/

namespace DeepWiki.Refine.DependentCalculus.UnivalentParametricity

/-- The three-binder body exposed by projecting a translated `pΠ` package. -/
def piRelationBody (domain : CoreTerm n) (codomain : CoreTerm (n + 1)) :
    Term (scopeSize n + 2) :=
  .pi ((original domain).weakenBy 2)
    (.pi ((primed domain).weakenBy 3)
      (.pi
        (Term.relationApplication
          (Term.rel ((termTranslation domain).weakenBy 4)) (.var 1) (.var 0))
        (Term.relationApplication
          (Term.rel ((termTranslation codomain).rename insertTwoAfterThree))
          (.app (.var 4) (.var 2))
          (.app (.var 3) (.var 1)))))

/-- The relation fiber after substituting a function's two endpoint copies. -/
def piRelationFiber (domain : CoreTerm n) (codomain : CoreTerm (n + 1))
    (function : CoreTerm n) : Term (scopeSize n) :=
  ((piRelationBody domain codomain).substitute
    (Substitution.lift (Substitution.single (original function)))).instantiate
      (primed function)

/-- Substitute a function's original and primed copies for the two outer binders. -/
def functionCopySubstitution (function : CoreTerm n) :
    Substitution (scopeSize n + 2) (scopeSize n) :=
  Substitution.comp (Substitution.single (primed function))
    (Substitution.lift (Substitution.single (original function)))

/-- Function-copy substitution sends the newest variable to the primed function. -/
@[simp] theorem functionCopySubstitution_zero (function : CoreTerm n) :
    functionCopySubstitution function 0 = primed function :=
  rfl

/-- Function-copy substitution sends the second variable to the original function. -/
@[simp] theorem functionCopySubstitution_one (function : CoreTerm n) :
    functionCopySubstitution function 1 = original function := by
  unfold functionCopySubstitution Substitution.comp
  change ((original function).rename
    DependentCalculus.Renaming.shift).instantiate
      (primed function) = original function
  exact Term.instantiate_rename_shift (original function) (primed function)

/-- Function-copy substitution preserves every older ambient variable. -/
@[simp] theorem functionCopySubstitution_succ_succ (function : CoreTerm n)
    (index : Fin (scopeSize n)) :
    functionCopySubstitution function index.succ.succ = .var index :=
  rfl

/-- Substituting function copies cancels a twofold weakening. -/
theorem substitute_functionCopies_weakenBy_two
    (term : Term (scopeSize n)) (function : CoreTerm n) :
    (term.weakenBy 2).substitute (functionCopySubstitution function) = term := by
  simp only [Term.weakenBy, Term.substitute_rename]
  calc
    term.substitute
        (fun index => functionCopySubstitution function
          (DependentCalculus.Renaming.shift
            (DependentCalculus.Renaming.shift index))) =
      term.substitute Substitution.identity := by
        apply Term.substitute_congr
        funext index
        rfl
    _ = term := Term.substitute_identity term

/-- Removing two function binders commutes with surrounding binders. -/
theorem substitute_lifted_functionCopies_weakenBy
    (term : Term (scopeSize n)) (function : CoreTerm n) (amount : Nat) :
    ((term.weakenBy 2).weakenBy amount).substitute
        (Substitution.liftBy (functionCopySubstitution function) amount) =
      term.weakenBy amount := by
  induction amount with
  | zero => exact substitute_functionCopies_weakenBy_two term function
  | succ amount inductionHypothesis =>
      simpa only [Term.weakenBy, Substitution.liftBy,
        Term.substitute_rename_shift_lift] using
          congrArg (fun value => value.rename
            DependentCalculus.Renaming.shift) inductionHypothesis

/-- Removing function binders cancels insertion behind the three relation binders. -/
theorem substitute_lifted_functionCopies_insertTwoAfterThree
    (term : Term (scopeSize n + 3)) (function : CoreTerm n) :
    (term.rename insertTwoAfterThree).substitute
        (Substitution.liftBy (functionCopySubstitution function) 3) = term := by
  rw [Term.substitute_rename]
  rw [show
      (fun index =>
        Substitution.liftBy (functionCopySubstitution function) 3
          (insertTwoAfterThree index)) = Substitution.identity by
    funext index
    refine Fin.cases rfl ?_ index
    intro oneOrOlder
    refine Fin.cases rfl ?_ oneOrOlder
    intro twoOrOlder
    refine Fin.cases rfl ?_ twoOrOlder
    intro older
    rfl]
  exact Term.substitute_identity term

/-- Sequential endpoint beta substitutions compose into function-copy substitution. -/
theorem piRelationFiber_eq_substitute (domain : CoreTerm n)
    (codomain : CoreTerm (n + 1)) (function : CoreTerm n) :
    piRelationFiber domain codomain function =
      (piRelationBody domain codomain).substitute
        (functionCopySubstitution function) := by
  unfold piRelationFiber functionCopySubstitution Term.instantiate
  exact Term.substitute_comp _ _ _

/-- Codomain relation before substituting an argument triple. -/
def applicationRelationBody (function : CoreTerm n)
    (codomain : CoreTerm (n + 1)) : Term (scopeSize n + 3) :=
  Term.relationApplication
    (typeTranslation codomain)
    (.app ((original function).weakenBy 3) (.var 2))
    (.app ((primed function).weakenBy 3) (.var 1))

/-- Explicit beta-normal relation fiber of a translated dependent product. -/
def piRelationFiberNormal (domain : CoreTerm n) (codomain : CoreTerm (n + 1))
    (function : CoreTerm n) : Term (scopeSize n) :=
  .pi (original domain)
    (.pi ((primed domain).weakenBy 1)
      (.pi (Term.relatedDomain (termTranslation domain))
        (applicationRelationBody function codomain)))

/-- The substitution presentation of a product fiber equals its explicit normal form. -/
theorem piRelationFiber_eq_normal (domain : CoreTerm n)
    (codomain : CoreTerm (n + 1)) (function : CoreTerm n) :
    piRelationFiber domain codomain function =
      piRelationFiberNormal domain codomain function := by
  have originalDomain := substitute_lifted_functionCopies_weakenBy
    (original domain) function 0
  change ((original domain).weakenBy 2).substitute
    (functionCopySubstitution function) = original domain at originalDomain
  have primedDomain := substitute_lifted_functionCopies_weakenBy
    (primed domain) function 1
  change ((primed domain).weakenBy 3).substitute
    (Substitution.lift (functionCopySubstitution function)) =
      (primed domain).weakenBy 1 at primedDomain
  have domainRelation := substitute_lifted_functionCopies_weakenBy
    (termTranslation domain) function 2
  change ((termTranslation domain).weakenBy 4).substitute
    (Substitution.lift (Substitution.lift (functionCopySubstitution function))) =
      (termTranslation domain).weakenBy 2 at domainRelation
  have codomainRelation :=
    substitute_lifted_functionCopies_insertTwoAfterThree
      (termTranslation codomain) function
  change ((termTranslation codomain).rename insertTwoAfterThree).substitute
    (Substitution.lift
      (Substitution.lift
        (Substitution.lift (functionCopySubstitution function)))) =
      termTranslation codomain at codomainRelation
  have originalFunction :
      Substitution.lift
          (Substitution.lift
            (Substitution.lift (functionCopySubstitution function))) 4 =
        (original function).weakenBy 3 := by
    change (((functionCopySubstitution function 1).rename
      DependentCalculus.Renaming.shift).rename
      DependentCalculus.Renaming.shift).rename
      DependentCalculus.Renaming.shift =
        (original function).weakenBy 3
    rw [functionCopySubstitution_one]
    rfl
  have primedFunction :
      Substitution.lift
          (Substitution.lift
            (Substitution.lift (functionCopySubstitution function))) 3 =
        (primed function).weakenBy 3 := by
    change (((functionCopySubstitution function 0).rename
      DependentCalculus.Renaming.shift).rename
      DependentCalculus.Renaming.shift).rename
      DependentCalculus.Renaming.shift =
        (primed function).weakenBy 3
    rw [functionCopySubstitution_zero]
    rfl
  have domainOriginalVariable :
      Substitution.lift (Substitution.lift (functionCopySubstitution function)) 1 =
        (.var 1 : Term (scopeSize n + 2)) :=
    rfl
  have domainPrimedVariable :
      Substitution.lift (Substitution.lift (functionCopySubstitution function)) 0 =
        (.var 0 : Term (scopeSize n + 2)) :=
    rfl
  have codomainOriginalVariable :
      Substitution.lift
          (Substitution.lift
            (Substitution.lift (functionCopySubstitution function))) 2 =
        (.var 2 : Term (scopeSize n + 3)) :=
    rfl
  have codomainPrimedVariable :
      Substitution.lift
          (Substitution.lift
            (Substitution.lift (functionCopySubstitution function))) 1 =
        (.var 1 : Term (scopeSize n + 3)) :=
    rfl
  rw [piRelationFiber_eq_substitute]
  unfold piRelationBody piRelationFiberNormal applicationRelationBody
  simp only [Term.substitute, Term.relatedDomain, Term.relationApplication,
    typeTranslation, Term.rel]
  rw [originalDomain, primedDomain, domainRelation, codomainRelation,
    originalFunction, primedFunction, domainOriginalVariable,
    domainPrimedVariable, codomainOriginalVariable, codomainPrimedVariable]
  rfl

/-- Apply a weakened core function to the newest source variable. -/
def fiberApplication (function : CoreTerm n) : CoreTerm (n + 1) :=
  .app (function.rename DependentCalculus.Renaming.shift) (.var 0)

/-- The fiber application's related type is the product relation's codomain body. -/
theorem relatedTermType_fiberApplication (function : CoreTerm n)
    (codomain : CoreTerm (n + 1)) :
    relatedTermType (fiberApplication function) codomain =
      applicationRelationBody function codomain := by
  unfold fiberApplication relatedTermType applicationRelationBody
  simp only [original, primed, RawParametricity.original, RawParametricity.primed,
    DependentCalculus.Term.rename, Term.ofCore]
  rw [show
    Term.ofCore
        ((function.rename DependentCalculus.Renaming.shift).rename
          (RawParametricity.originalRenaming (n + 1))) =
      (original function).weakenBy 3 by
        exact (original_rename (RawParametricity.relationalShift n) function).trans
          (weakenBy_three_eq_rename_translatedShift (original function)).symm]
  rw [show
    Term.ofCore
        ((function.rename DependentCalculus.Renaming.shift).rename
          (RawParametricity.primedRenaming (n + 1))) =
      (primed function).weakenBy 3 by
        exact (primed_rename (RawParametricity.relationalShift n) function).trans
          (weakenBy_three_eq_rename_translatedShift (primed function)).symm]
  rfl

/-- Projecting and applying translated `pΠ` beta-reduces to its relation fiber. -/
theorem relatedTermType_pi_beta (function domain : CoreTerm n)
    (codomain : CoreTerm (n + 1)) :
    Convertible (relatedTermType function (.pi domain codomain))
      (piRelationFiber domain codomain function) := by
  unfold relatedTermType typeTranslation
  rw [termTranslation_pi]
  refine .trans
    ((Convertible.beta
      (BetaStep.dependentProductProjection
        (original domain) (primed domain)
        (originalCodomain codomain) (primedCodomain codomain)
        (termTranslation domain) (termTranslation codomain))).appFunction.appFunction)
    ?_
  unfold Term.dependentProductRelation piRelationFiber piRelationBody
  refine .trans (.beta (.appFunction (.beta _ _ _))) ?_
  exact .beta (.beta _ _ _)

namespace Cumulative

/-- Related universe fibers are cumulative exactly through package-type level monotonicity. -/
theorem relatedTermType_sort (term : CoreTerm n) {lower upper : Nat}
    (levelOrder : lower ≤ upper) :
    Cumulative (relatedTermType term (.sort lower))
      (relatedTermType term (.sort upper)) :=
  .trans (.conversion (relatedTermType_sort_convertible term lower))
    (.trans (.packageType levelOrder (original term) (primed term))
      (.conversion (relatedTermType_sort_convertible term upper).symm))

/-- Fiberwise codomain cumulativity and convertible domains lift through products. -/
theorem relatedTermType_pi (term : CoreTerm n)
    {domain domain' : CoreTerm n}
    {codomain codomain' : CoreTerm (n + 1)}
    (domainEqual : DependentCalculus.Convertible domain domain')
    (codomainCumulative : ∀ output : CoreTerm (n + 1),
      Cumulative (relatedTermType output codomain)
        (relatedTermType output codomain')) :
    Cumulative (relatedTermType term (.pi domain codomain))
      (relatedTermType term (.pi domain' codomain')) := by
  have outputCumulative := codomainCumulative (fiberApplication term)
  rw [relatedTermType_fiberApplication term codomain,
    relatedTermType_fiberApplication term codomain'] at outputCumulative
  have originalDomainEqual := Convertible.original domainEqual
  have primedDomainEqual := (Convertible.primed domainEqual).weakenBy 1
  have relationDomainEqual :=
    (termTranslation_convertible domainEqual).relatedDomain
  have normalCumulative :
      Cumulative (piRelationFiberNormal domain codomain term)
        (piRelationFiberNormal domain' codomain' term) := by
    unfold piRelationFiberNormal
    exact .pi originalDomainEqual
      (.pi primedDomainEqual
        (.pi relationDomainEqual outputCumulative))
  have sourceBeta := relatedTermType_pi_beta term domain codomain
  rw [piRelationFiber_eq_normal] at sourceBeta
  have targetBeta := relatedTermType_pi_beta term domain' codomain'
  rw [piRelationFiber_eq_normal] at targetBeta
  exact .trans (.conversion sourceBeta)
    (.trans normalCumulative (.conversion targetBeta.symm))

end Cumulative

/-- Relational cumulativity compares every substituted applied relation fiber. -/
def IsRelationallyCumulative (left right : CoreTerm n) : Prop :=
  ∀ {target : Nat}
    (mapping : DependentCalculus.Substitution n target)
    (term : CoreTerm target),
    Cumulative (relatedTermType term (left.substitute mapping))
      (relatedTermType term (right.substitute mapping))

namespace IsRelationallyCumulative

/-- Source conversion induces univalent relational-fiber cumulativity. -/
theorem of_convertible {left right : CoreTerm n}
    (conversion : DependentCalculus.Convertible left right) :
    IsRelationallyCumulative left right := fun mapping _ =>
  .conversion (relatedTermType_convertible _ (conversion.substitute mapping))

/-- Universe order induces univalent relational-fiber cumulativity. -/
theorem sort {lower upper : Nat} (levelOrder : lower ≤ upper) :
    IsRelationallyCumulative (.sort lower : CoreTerm n) (.sort upper) :=
  fun _ term => Cumulative.relatedTermType_sort term levelOrder

/-- Relational-fiber cumulativity is transitive. -/
theorem trans {first second third : CoreTerm n}
    (firstSecond : IsRelationallyCumulative first second)
    (secondThird : IsRelationallyCumulative second third) :
    IsRelationallyCumulative first third := fun mapping term =>
  .trans (firstSecond mapping term) (secondThird mapping term)

/-- Convertible domains and cumulative codomain fibers induce cumulative product fibers. -/
theorem pi {domain domain' : CoreTerm n}
    {codomain codomain' : CoreTerm (n + 1)}
    (domainEqual : DependentCalculus.Convertible domain domain')
    (codomainCumulative : IsRelationallyCumulative codomain codomain') :
    IsRelationallyCumulative (.pi domain codomain) (.pi domain' codomain') :=
  fun mapping term => Cumulative.relatedTermType_pi term
    (domainEqual.substitute mapping)
    (codomainCumulative (DependentCalculus.Substitution.lift mapping))

/-- Relational cumulativity specializes to the original scope. -/
theorem apply {left right : CoreTerm n}
    (subtype : IsRelationallyCumulative left right) (term : CoreTerm n) :
    Cumulative (relatedTermType term left) (relatedTermType term right) := by
  simpa only [DependentCalculus.Term.substitute_identity] using
    subtype DependentCalculus.Substitution.identity term

end IsRelationallyCumulative

/-- Every source cumulative conversion preserves all substituted univalent relation fibers. -/
theorem isRelationallyCumulative_of_cumulative {left right : CoreTerm n}
    (subtype : DependentCalculus.Cumulative left right) :
    IsRelationallyCumulative left right := by
  induction subtype with
  | conversion equal => exact IsRelationallyCumulative.of_convertible equal
  | sort level => exact IsRelationallyCumulative.sort level
  | pi domainEqual _ codomainInduction =>
      exact IsRelationallyCumulative.pi domainEqual codomainInduction
  | trans _ _ firstInduction secondInduction =>
      exact IsRelationallyCumulative.trans firstInduction secondInduction

/-- Source cumulativity preserves the applied univalent related-term type. -/
theorem relatedTermType_cumulative (term : CoreTerm n)
    {left right : CoreTerm n}
    (subtype : DependentCalculus.Cumulative left right) :
    Cumulative (relatedTermType term left) (relatedTermType term right) :=
  IsRelationallyCumulative.apply
    (isRelationallyCumulative_of_cumulative subtype) term

end DeepWiki.Refine.DependentCalculus.UnivalentParametricity
