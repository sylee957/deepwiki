import DeepWiki.Refine.CCOmega.Syntax

/-! # Univalent parametricity syntax

Intrinsically scoped terms, contexts, renamings, substitutions, and structural
laws for the object calculus extended with univalent relation-package primitives. -/

namespace DeepWiki.Refine.DependentCalculus.UnivalentParametricity

/-- Terms of the underlying intrinsically scoped `CCω` calculus. -/
abbrev CoreTerm := DependentCalculus.Term

/-- Renamings between intrinsically scoped univalent-parametricity terms. -/
abbrev Renaming := DependentCalculus.Renaming

/-- `CCω` terms extended by the package primitives used in univalent parametricity. -/
inductive Term : Nat → Type where
  /-- A universe in the predicative hierarchy. -/
  | sort {n : Nat} (level : Nat) : Term n
  /-- An intrinsically scoped de Bruijn variable. -/
  | var {n : Nat} (index : Fin n) : Term n
  /-- Application of one extended term to another. -/
  | app {n : Nat} (function argument : Term n) : Term n
  /-- A lambda abstraction with an explicit domain. -/
  | lam {n : Nat} (domain : Term n) (body : Term (n + 1)) : Term n
  /-- A dependent product with one bound variable in its codomain. -/
  | pi {n : Nat} (domain : Term n) (codomain : Term (n + 1)) : Term n
  /-- The level-indexed family of univalent relation-package types. -/
  | packageFamily {n : Nat} (level : Nat) : Term n
  /-- The canonical package relating two copies of a universe. -/
  | universePackage {n : Nat} (level : Nat) : Term n
  /-- The package relating dependent products, with all endpoint data explicit. -/
  | dependentProductPackage {n : Nat}
      (leftDomain rightDomain : Term n)
      (leftCodomain rightCodomain : Term (n + 1))
      (domainPackage : Term n) (codomainPackage : Term (n + 3)) : Term n
  /-- Projection of the binary-relation field from a univalent relation package. -/
  | relationProjection {n : Nat} (package : Term n) : Term n
  deriving DecidableEq, Repr

namespace Term

/-- Rename every free variable, lifting through ordinary and relational binders. -/
def rename (mapping : Renaming source target) : Term source → Term target
  | .sort level => .sort level
  | .var index => .var (mapping index)
  | .app function argument => .app (rename mapping function) (rename mapping argument)
  | .lam domain body =>
      .lam (rename mapping domain)
        (rename (DependentCalculus.Renaming.lift mapping) body)
  | .pi domain codomain =>
      .pi (rename mapping domain)
        (rename (DependentCalculus.Renaming.lift mapping) codomain)
  | .packageFamily level => .packageFamily level
  | .universePackage level => .universePackage level
  | .dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage =>
      .dependentProductPackage
        (rename mapping leftDomain) (rename mapping rightDomain)
        (rename (DependentCalculus.Renaming.lift mapping) leftCodomain)
        (rename (DependentCalculus.Renaming.lift mapping) rightCodomain)
        (rename mapping domainPackage)
        (rename (Renaming.liftBy mapping 3) codomainPackage)
  | .relationProjection package => .relationProjection (rename mapping package)

/-- Extensionally equal renamings act identically on an extended term. -/
theorem rename_congr {left right : Renaming source target} (equal : left = right)
    (term : Term source) : rename left term = rename right term := by
  cases equal
  rfl

/-- Renaming by the identity leaves every extended term unchanged. -/
@[simp] theorem rename_identity (term : Term n) :
    rename DependentCalculus.Renaming.identity term = term := by
  induction term with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [rename, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [rename, domainInduction,
        DependentCalculus.Renaming.lift_identity, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [rename, domainInduction,
        DependentCalculus.Renaming.lift_identity, codomainInduction]
  | packageFamily => rfl
  | universePackage => rfl
  | dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage leftDomainInduction rightDomainInduction
      leftCodomainInduction rightCodomainInduction domainPackageInduction
      codomainPackageInduction =>
      simp only [rename, leftDomainInduction, rightDomainInduction,
        DependentCalculus.Renaming.lift_identity,
        leftCodomainInduction, rightCodomainInduction, domainPackageInduction,
        Renaming.liftBy_identity, codomainPackageInduction]
  | relationProjection package packageInduction =>
      simp only [rename, packageInduction]

/-- Successive renamings act as their composition. -/
theorem rename_comp (term : Term source) (inner : Renaming source middle)
    (outer : Renaming middle target) :
    rename outer (rename inner term) =
      rename (DependentCalculus.Renaming.comp outer inner) term := by
  induction term generalizing middle target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [rename, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [rename, domainInduction, bodyInduction,
        DependentCalculus.Renaming.lift_comp]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [rename, domainInduction, codomainInduction,
        DependentCalculus.Renaming.lift_comp]
  | packageFamily => rfl
  | universePackage => rfl
  | dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage leftDomainInduction rightDomainInduction
      leftCodomainInduction rightCodomainInduction domainPackageInduction
      codomainPackageInduction =>
      simp only [rename, leftDomainInduction, rightDomainInduction,
        leftCodomainInduction, rightCodomainInduction, domainPackageInduction,
        codomainPackageInduction,
        DependentCalculus.Renaming.lift_comp,
        Renaming.liftBy_comp]
  | relationProjection package packageInduction =>
      simp only [rename, packageInduction]

/-- Embed a core `CCω` term into the univalent-parametricity syntax. -/
def ofCore : CoreTerm n → Term n
  | .sort level => .sort level
  | .var index => .var index
  | .app function argument => .app (ofCore function) (ofCore argument)
  | .lam domain body => .lam (ofCore domain) (ofCore body)
  | .pi domain codomain => .pi (ofCore domain) (ofCore codomain)

/-- Embedding commutes with every core renaming. -/
@[simp] theorem ofCore_rename (term : CoreTerm source)
    (mapping : Renaming source target) :
    ofCore (term.rename mapping) = rename mapping (ofCore term) := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DependentCalculus.Term.rename, ofCore, rename,
        functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [DependentCalculus.Term.rename, ofCore, rename,
        domainInduction, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [DependentCalculus.Term.rename, ofCore, rename,
        domainInduction, codomainInduction]

/-- Weaken an extended term by any finite number of fresh variables. -/
def weakenBy (term : Term n) : (amount : Nat) → Term (n + amount)
  | 0 => term
  | amount + 1 => (weakenBy term amount).rename
      DependentCalculus.Renaming.shift

/-- Weakening after renaming agrees with renaming lifted under the fresh binders. -/
theorem weakenBy_rename (term : Term source) (mapping : Renaming source target)
    (amount : Nat) :
    weakenBy (term.rename mapping) amount =
      (weakenBy term amount).rename (Renaming.liftBy mapping amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [weakenBy, inductionHypothesis, rename_comp, Renaming.liftBy]
      apply rename_congr
      funext index
      rfl

end Term

/-- A substitution replaces source variables by extended target terms. -/
abbrev Substitution (source target : Nat) := Fin source → Term target

namespace Substitution

/-- Regard a renaming as its variable-only extended substitution. -/
def ofRenaming (mapping : Renaming source target) : Substitution source target :=
  fun index => .var (mapping index)

/-- The identity substitution on extended terms. -/
def identity : Substitution n n :=
  ofRenaming DependentCalculus.Renaming.identity

/-- Substitute one term for the newest variable and leave older variables unchanged. -/
def single (argument : Term n) : Substitution (n + 1) n :=
  Fin.cases argument Term.var

/-- Single substitution sends the newest variable to its argument. -/
@[simp] theorem single_zero (argument : Term n) : single argument 0 = argument :=
  rfl

/-- Single substitution leaves every older variable unchanged. -/
@[simp] theorem single_succ (argument : Term n) (index : Fin n) :
    single argument index.succ = .var index :=
  rfl

/-- Lift an extended substitution beneath one binder. -/
def lift (mapping : Substitution source target) :
    Substitution (source + 1) (target + 1) :=
  Fin.cases (.var 0)
    (fun index => (mapping index).rename
      DependentCalculus.Renaming.shift)

/-- Lifting fixes the newest variable. -/
@[simp] theorem lift_zero (mapping : Substitution source target) :
    lift mapping 0 = .var 0 :=
  rfl

/-- Lifting weakens every substituted older variable. -/
@[simp] theorem lift_succ (mapping : Substitution source target) (index : Fin source) :
    lift mapping index.succ =
      (mapping index).rename DependentCalculus.Renaming.shift :=
  rfl

/-- Lift an extended substitution beneath any number of binders. -/
def liftBy (mapping : Substitution source target) :
    (amount : Nat) → Substitution (source + amount) (target + amount)
  | 0 => mapping
  | amount + 1 => lift (liftBy mapping amount)

/-- Lifting a renaming substitution agrees with lifting its renaming. -/
@[simp] theorem lift_ofRenaming (mapping : Renaming source target) :
    lift (ofRenaming mapping) =
      ofRenaming (DependentCalculus.Renaming.lift mapping) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Lifting the identity substitution gives the identity substitution. -/
@[simp] theorem lift_identity : lift (identity : Substitution n n) = identity := by
  simpa only [identity,
    DependentCalculus.Renaming.lift_identity] using
    lift_ofRenaming (DependentCalculus.Renaming.identity : Renaming n n)

/-- Lifting commutes with precomposition by a renaming. -/
theorem lift_precomp (substitute : Substitution middle target)
    (mapping : Renaming source middle) :
    lift (fun index => substitute (mapping index)) =
      fun index => lift substitute
        (DependentCalculus.Renaming.lift mapping index) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Repeated substitution lifting agrees with repeated renaming lifting. -/
@[simp] theorem liftBy_ofRenaming (mapping : Renaming source target) (amount : Nat) :
    liftBy (ofRenaming mapping) amount = ofRenaming (Renaming.liftBy mapping amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [liftBy, Renaming.liftBy, inductionHypothesis, lift_ofRenaming]

/-- Repeated lifting commutes with precomposition by a repeatedly lifted renaming. -/
theorem liftBy_precomp (substitute : Substitution middle target)
    (mapping : Renaming source middle) (amount : Nat) :
    liftBy (fun index => substitute (mapping index)) amount =
      fun index => liftBy substitute amount (Renaming.liftBy mapping amount index) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [liftBy, Renaming.liftBy, inductionHypothesis]
      exact lift_precomp _ _

/-- Embed a core substitution pointwise into the extended syntax. -/
def ofCore (mapping : DependentCalculus.Substitution source target) :
    Substitution source target :=
  fun index => Term.ofCore (mapping index)

/-- Lifting commutes with pointwise embedding of a core substitution. -/
@[simp] theorem lift_ofCore
    (mapping : DependentCalculus.Substitution source target) :
    lift (ofCore mapping) =
      ofCore (DependentCalculus.Substitution.lift mapping) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  exact (Term.ofCore_rename (mapping older)
    DependentCalculus.Renaming.shift).symm

end Substitution

namespace Term

/-- Perform capture-avoiding simultaneous substitution on an extended term. -/
def substitute (mapping : Substitution source target) : Term source → Term target
  | .sort level => .sort level
  | .var index => mapping index
  | .app function argument =>
      .app (substitute mapping function) (substitute mapping argument)
  | .lam domain body =>
      .lam (substitute mapping domain) (substitute (Substitution.lift mapping) body)
  | .pi domain codomain =>
      .pi (substitute mapping domain) (substitute (Substitution.lift mapping) codomain)
  | .packageFamily level => .packageFamily level
  | .universePackage level => .universePackage level
  | .dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage =>
      .dependentProductPackage
        (substitute mapping leftDomain) (substitute mapping rightDomain)
        (substitute (Substitution.lift mapping) leftCodomain)
        (substitute (Substitution.lift mapping) rightCodomain)
        (substitute mapping domainPackage)
        (substitute (Substitution.liftBy mapping 3) codomainPackage)
  | .relationProjection package => .relationProjection (substitute mapping package)

/-- Extensionally equal substitutions act identically on an extended term. -/
theorem substitute_congr {left right : Substitution source target} (equal : left = right)
    (term : Term source) : substitute left term = substitute right term := by
  cases equal
  rfl

/-- Substitution along a renaming agrees with direct renaming. -/
theorem substitute_ofRenaming (term : Term source) (mapping : Renaming source target) :
    substitute (Substitution.ofRenaming mapping) term = rename mapping term := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [substitute, rename, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [substitute, rename, domainInduction, Substitution.lift_ofRenaming,
        bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [substitute, rename, domainInduction, Substitution.lift_ofRenaming,
        codomainInduction]
  | packageFamily => rfl
  | universePackage => rfl
  | dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage leftDomainInduction rightDomainInduction
      leftCodomainInduction rightCodomainInduction domainPackageInduction
      codomainPackageInduction =>
      simp only [substitute, rename, leftDomainInduction, rightDomainInduction,
        leftCodomainInduction, rightCodomainInduction, domainPackageInduction,
        codomainPackageInduction, Substitution.lift_ofRenaming,
        Substitution.liftBy_ofRenaming]
  | relationProjection package packageInduction =>
      simp only [substitute, rename, packageInduction]

/-- Substitution by the identity leaves every extended term unchanged. -/
@[simp] theorem substitute_identity (term : Term n) :
    substitute Substitution.identity term = term := by
  simpa only [Substitution.identity, rename_identity] using
    substitute_ofRenaming term
      (DependentCalculus.Renaming.identity : Renaming n n)

/-- Substitution after renaming precomposes the substitution by that renaming. -/
theorem substitute_rename (term : Term source) (mapping : Renaming source middle)
    (substitute : Substitution middle target) :
    (term.rename mapping).substitute substitute =
      term.substitute (fun index => substitute (mapping index)) := by
  induction term generalizing middle target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [rename, Term.substitute, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [rename, Term.substitute, domainInduction, bodyInduction]
      apply congrArg (Term.lam _)
      apply substitute_congr
      exact (Substitution.lift_precomp substitute mapping).symm
  | pi domain codomain domainInduction codomainInduction =>
      simp only [rename, Term.substitute, domainInduction, codomainInduction]
      apply congrArg (Term.pi _)
      apply substitute_congr
      exact (Substitution.lift_precomp substitute mapping).symm
  | packageFamily => rfl
  | universePackage => rfl
  | dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage leftDomainInduction rightDomainInduction
      leftCodomainInduction rightCodomainInduction domainPackageInduction
      codomainPackageInduction =>
      simp only [rename, Term.substitute, leftDomainInduction,
        rightDomainInduction, leftCodomainInduction, rightCodomainInduction,
        domainPackageInduction, codomainPackageInduction]
      congr 1
      · apply substitute_congr
        exact (Substitution.lift_precomp substitute mapping).symm
      · apply substitute_congr
        exact (Substitution.lift_precomp substitute mapping).symm
      · apply substitute_congr
        exact (Substitution.liftBy_precomp substitute mapping 3).symm
  | relationProjection package packageInduction =>
      simp only [rename, Term.substitute, packageInduction]

/-- Embedding commutes with every core substitution. -/
@[simp] theorem ofCore_substitute (term : CoreTerm source)
    (mapping : DependentCalculus.Substitution source target) :
    ofCore (term.substitute mapping) =
      substitute (Substitution.ofCore mapping) (ofCore term) := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DependentCalculus.Term.substitute, ofCore, substitute,
        functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [DependentCalculus.Term.substitute, ofCore, substitute,
        domainInduction, Substitution.lift_ofCore, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [DependentCalculus.Term.substitute, ofCore, substitute,
        domainInduction, Substitution.lift_ofCore, codomainInduction]

/-- Substitute one extended argument for the newest variable. -/
def instantiate (body : Term (n + 1)) (argument : Term n) : Term n :=
  body.substitute (Substitution.single argument)

/-- Instantiating the newest variable returns the substituted argument. -/
@[simp] theorem instantiate_var_zero (argument : Term n) :
    (Term.var (0 : Fin (n + 1))).instantiate argument = argument :=
  rfl

/-- Instantiating an older variable leaves that variable unchanged. -/
@[simp] theorem instantiate_var_succ (argument : Term n) (index : Fin n) :
    (Term.var index.succ).instantiate argument = .var index :=
  rfl

end Term

namespace Substitution

/-- Lifting commutes with postcomposition by a renaming. -/
theorem lift_postrename (substitute : Substitution source middle)
    (mapping : Renaming middle target) :
    lift (fun index => (substitute index).rename mapping) =
      fun index => (lift substitute index).rename
        (DependentCalculus.Renaming.lift mapping) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  simp only [lift_succ, Term.rename_comp]
  apply Term.rename_congr
  funext element
  rfl

/-- Repeated lifting commutes with postcomposition by a repeatedly lifted renaming. -/
theorem liftBy_postrename (substitute : Substitution source middle)
    (mapping : Renaming middle target) (amount : Nat) :
    liftBy (fun index => (substitute index).rename mapping) amount =
      fun index => (liftBy substitute amount index).rename
        (Renaming.liftBy mapping amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [liftBy, Renaming.liftBy, inductionHypothesis]
      exact lift_postrename _ _

end Substitution

namespace Term

/-- Renaming after substitution postcomposes every substituted term by the renaming. -/
theorem rename_substitute (term : Term source) (substitute : Substitution source middle)
    (mapping : Renaming middle target) :
    (term.substitute substitute).rename mapping =
      term.substitute (fun index => (substitute index).rename mapping) := by
  induction term generalizing middle target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [Term.substitute, rename, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [Term.substitute, rename, domainInduction, bodyInduction]
      apply congrArg (Term.lam _)
      apply substitute_congr
      exact (Substitution.lift_postrename substitute mapping).symm
  | pi domain codomain domainInduction codomainInduction =>
      simp only [Term.substitute, rename, domainInduction, codomainInduction]
      apply congrArg (Term.pi _)
      apply substitute_congr
      exact (Substitution.lift_postrename substitute mapping).symm
  | packageFamily => rfl
  | universePackage => rfl
  | dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage leftDomainInduction rightDomainInduction
      leftCodomainInduction rightCodomainInduction domainPackageInduction
      codomainPackageInduction =>
      simp only [Term.substitute, rename, leftDomainInduction,
        rightDomainInduction, leftCodomainInduction, rightCodomainInduction,
        domainPackageInduction, codomainPackageInduction]
      congr 1
      · apply substitute_congr
        exact (Substitution.lift_postrename substitute mapping).symm
      · apply substitute_congr
        exact (Substitution.lift_postrename substitute mapping).symm
      · apply substitute_congr
        exact (Substitution.liftBy_postrename substitute mapping 3).symm
  | relationProjection package packageInduction =>
      simp only [Term.substitute, rename, packageInduction]

/-- Weakening after substitution equals repeatedly lifted substitution after weakening. -/
theorem weakenBy_substitute (term : Term source)
    (mapping : Substitution source target) (amount : Nat) :
    (term.substitute mapping).weakenBy amount =
      (term.weakenBy amount).substitute (Substitution.liftBy mapping amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [weakenBy, inductionHypothesis, Substitution.liftBy]
      rw [rename_substitute, substitute_rename]
      apply substitute_congr
      funext index
      rfl

end Term

namespace Substitution

/-- Compose substitutions by substituting the outer mapping into each inner image. -/
def comp (outer : Substitution middle target) (inner : Substitution source middle) :
    Substitution source target :=
  fun index => (inner index).substitute outer

/-- The identity substitution is a left identity for composition. -/
@[simp] theorem identity_comp (mapping : Substitution source target) :
    comp identity mapping = mapping := by
  funext index
  exact Term.substitute_identity (mapping index)

/-- The identity substitution is a right identity for composition. -/
@[simp] theorem comp_identity (mapping : Substitution source target) :
    comp mapping identity = mapping := by
  funext index
  rfl

/-- Lifting preserves composition of substitutions. -/
theorem lift_comp (outer : Substitution middle target)
    (inner : Substitution source middle) :
    lift (comp outer inner) = comp (lift outer) (lift inner) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  simp only [lift_succ, comp, Term.substitute_rename, Term.rename_substitute]
  apply Term.substitute_congr
  funext element
  rfl

/-- Repeated lifting preserves composition of substitutions. -/
theorem liftBy_comp (outer : Substitution middle target)
    (inner : Substitution source middle) (amount : Nat) :
    liftBy (comp outer inner) amount =
      comp (liftBy outer amount) (liftBy inner amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [liftBy, inductionHypothesis, lift_comp]

end Substitution

namespace Term

/-- Successive substitutions act as their composition. -/
theorem substitute_comp (term : Term source) (inner : Substitution source middle)
    (outer : Substitution middle target) :
    (term.substitute inner).substitute outer =
      term.substitute (Substitution.comp outer inner) := by
  induction term generalizing middle target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [substitute, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [substitute, domainInduction, bodyInduction, Substitution.lift_comp]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [substitute, domainInduction, codomainInduction,
        Substitution.lift_comp]
  | packageFamily => rfl
  | universePackage => rfl
  | dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage leftDomainInduction rightDomainInduction
      leftCodomainInduction rightCodomainInduction domainPackageInduction
      codomainPackageInduction =>
      simp only [substitute, leftDomainInduction, rightDomainInduction,
        leftCodomainInduction, rightCodomainInduction, domainPackageInduction,
        codomainPackageInduction, Substitution.lift_comp,
        Substitution.liftBy_comp]
  | relationProjection package packageInduction =>
      simp only [substitute, packageInduction]

/-- Renaming commutes with instantiation under a lifted renaming. -/
theorem rename_instantiate (body : Term (source + 1)) (argument : Term source)
    (mapping : Renaming source target) :
    (body.instantiate argument).rename mapping =
      (body.rename
        (DependentCalculus.Renaming.lift mapping)).instantiate
        (argument.rename mapping) := by
  simp only [instantiate, rename_substitute, substitute_rename]
  apply substitute_congr
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Instantiating a weakened term cancels the weakening. -/
@[simp] theorem instantiate_rename_shift (term : Term n) (argument : Term n) :
    (term.rename DependentCalculus.Renaming.shift).instantiate argument =
      term := by
  simp only [instantiate, substitute_rename]
  rw [show (fun index =>
      Substitution.single argument
        (DependentCalculus.Renaming.shift index)) =
      Substitution.identity by
    funext index
    rfl]
  exact substitute_identity term

/-- Lifted substitution after weakening equals substitution followed by weakening. -/
theorem substitute_rename_shift_lift (term : Term source)
    (mapping : Substitution source target) :
    (term.rename DependentCalculus.Renaming.shift).substitute
        (Substitution.lift mapping) =
      (term.substitute mapping).rename
        DependentCalculus.Renaming.shift := by
  simp only [substitute_rename, rename_substitute]
  apply substitute_congr
  funext index
  rfl

/-- Simultaneous substitution commutes with single-variable instantiation. -/
theorem substitute_instantiate (body : Term (source + 1))
    (argument : Term source) (mapping : Substitution source target) :
    (body.instantiate argument).substitute mapping =
      (body.substitute (Substitution.lift mapping)).instantiate
        (argument.substitute mapping) := by
  simp only [instantiate, substitute_comp]
  apply substitute_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  change mapping older =
    ((mapping older).rename
      DependentCalculus.Renaming.shift).instantiate
      (argument.substitute mapping)
  exact (instantiate_rename_shift (mapping older) (argument.substitute mapping)).symm

end Term

/-- Contexts whose entries use the univalent-parametricity object syntax. -/
inductive Context : Nat → Type where
  /-- The empty extended context. -/
  | empty : Context 0
  /-- Extend a context by one intrinsically scoped type. -/
  | extend {n : Nat} (context : Context n) (type : Term n) : Context (n + 1)
  deriving DecidableEq, Repr

namespace Context

/-- Look up a de Bruijn variable's dependently weakened type. -/
def lookup : Context n → Fin n → Term n
  | .extend context type, index =>
      Fin.cases (type.rename DependentCalculus.Renaming.shift)
        (fun older =>
          (lookup context older).rename DependentCalculus.Renaming.shift)
        index

/-- The newest variable has the weakened extension type. -/
@[simp] theorem lookup_zero (context : Context n) (type : Term n) :
    (Context.extend context type).lookup 0 =
      type.rename DependentCalculus.Renaming.shift :=
  rfl

/-- Looking up an older variable weakens its prior lookup type. -/
@[simp] theorem lookup_succ (context : Context n) (type : Term n) (index : Fin n) :
    (Context.extend context type).lookup index.succ =
      (context.lookup index).rename DependentCalculus.Renaming.shift :=
  rfl

/-- Embed a core context entrywise into the extended syntax. -/
def ofCore : DependentCalculus.Context n → Context n
  | .empty => .empty
  | .extend context type => .extend (ofCore context) (Term.ofCore type)

/-- Lookup in an embedded core context is the embedded core lookup. -/
theorem ofCore_lookup (source : DependentCalculus.Context n)
    (index : Fin n) :
    (ofCore source).lookup index = Term.ofCore (source.lookup index) := by
  induction source with
  | empty => exact Fin.elim0 index
  | extend source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · exact (Term.ofCore_rename type
          DependentCalculus.Renaming.shift).symm
      · intro older
        change ((ofCore source).lookup older).rename
            DependentCalculus.Renaming.shift =
          Term.ofCore ((source.lookup older).rename
            DependentCalculus.Renaming.shift)
        rw [inductionHypothesis older, ← Term.ofCore_rename]

end Context

end DeepWiki.Refine.DependentCalculus.UnivalentParametricity
