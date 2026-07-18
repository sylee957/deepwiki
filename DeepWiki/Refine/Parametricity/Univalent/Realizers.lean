import DeepWiki.Refine.CCOmega.Syntax
import DeepWiki.Refine.PiRelationStructure
import DeepWiki.Refine.UnivalentRelationStructure

/-! # Univalent parametricity realizers

Semantic and intrinsically scoped object-language realizers for the universe and
dependent-product packages used by the univalent parametricity translation. -/

namespace DeepWiki.Refine

universe u v

/-- Form a univalent dependent-function relation package from domain and fiber packages. -/
def UnivalentRelation.pi {A B : Type u} {C : A → Type v} {D : B → Type v}
    (domain : UnivalentRelation A B)
    (fibers : ∀ a b (_related : domain.rel a b), UnivalentRelation (C a) (D b)) :
    UnivalentRelation ((a : A) → C a) ((b : B) → D b) :=
  (StructuredRelation.pi Annotation.equivalence domain.toStructuredRelationTop
    (fun a b related => (fibers a b related).toStructuredRelationTop)).toUnivalentRelation

/-- Projecting a dependent-function package yields the dependent respectful relation. -/
@[simp] theorem UnivalentRelation.pi_rel {A B : Type u}
    {C : A → Type v} {D : B → Type v} (domain : UnivalentRelation A B)
    (fibers : ∀ a b (_related : domain.rel a b), UnivalentRelation (C a) (D b)) :
    (domain.pi fibers).rel =
      DependentRespectful domain.rel (fun a b related => (fibers a b related).rel) :=
  rfl

/-- Pointwise application of a dependent-function package is dependent respectfulness. -/
@[simp] theorem UnivalentRelation.pi_rel_apply {A B : Type u}
    {C : A → Type v} {D : B → Type v} (domain : UnivalentRelation A B)
    (fibers : ∀ a b (_related : domain.rel a b), UnivalentRelation (C a) (D b))
    (left : (a : A) → C a) (right : (b : B) → D b) :
    (domain.pi fibers).rel left right =
      ∀ a b (related : domain.rel a b),
        (fibers a b related).rel (left a) (right b) :=
  rfl

example {A B : Type u} {C : A → Type v} {D : B → Type v}
    (domain : UnivalentRelation A B)
    (fibers : ∀ a b (_related : domain.rel a b), UnivalentRelation (C a) (D b)) :
    UnivalentRelation ((a : A) → C a) ((b : B) → D b) :=
  domain.pi fibers

example {A B : Type u} {C : A → Type v} {D : B → Type v}
    (domain : UnivalentRelation A B)
    (fibers : ∀ a b (_related : domain.rel a b), UnivalentRelation (C a) (D b)) :
    (domain.pi fibers).rel =
      DependentRespectful domain.rel (fun a b related => (fibers a b related).rel) :=
  rfl

end DeepWiki.Refine

namespace DeepWiki.Refine.DependentCalculus.UnivalentParametricity

/-- Terms of the underlying intrinsically scoped `CCω` calculus. -/
abbrev CoreTerm := DeepWiki.Refine.DependentCalculus.Term

/-- Renamings between intrinsically scoped univalent-parametricity terms. -/
abbrev Renaming := DeepWiki.Refine.DependentCalculus.Renaming

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

namespace Renaming

/-- Lift a renaming beneath any number of fresh binders. -/
def liftBy (mapping : Renaming source target) :
    (amount : Nat) → Renaming (source + amount) (target + amount)
  | 0 => mapping
  | amount + 1 => DeepWiki.Refine.DependentCalculus.Renaming.lift
      (liftBy mapping amount)

/-- Repeatedly lifting the identity renaming gives the identity renaming. -/
@[simp] theorem liftBy_identity (amount : Nat) :
    liftBy (DeepWiki.Refine.DependentCalculus.Renaming.identity : Renaming n n) amount =
      DeepWiki.Refine.DependentCalculus.Renaming.identity := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [liftBy, inductionHypothesis,
        DeepWiki.Refine.DependentCalculus.Renaming.lift_identity]

/-- Repeated lifting preserves composition of renamings. -/
@[simp] theorem liftBy_comp (outer : Renaming middle target)
    (inner : Renaming source middle) (amount : Nat) :
    liftBy (DeepWiki.Refine.DependentCalculus.Renaming.comp outer inner) amount =
      DeepWiki.Refine.DependentCalculus.Renaming.comp
        (liftBy outer amount) (liftBy inner amount) := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [liftBy, inductionHypothesis,
        DeepWiki.Refine.DependentCalculus.Renaming.lift_comp]

end Renaming

namespace Term

/-- Rename every free variable, lifting through ordinary and relational binders. -/
def rename (mapping : Renaming source target) : Term source → Term target
  | .sort level => .sort level
  | .var index => .var (mapping index)
  | .app function argument => .app (rename mapping function) (rename mapping argument)
  | .lam domain body =>
      .lam (rename mapping domain)
        (rename (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping) body)
  | .pi domain codomain =>
      .pi (rename mapping domain)
        (rename (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping) codomain)
  | .packageFamily level => .packageFamily level
  | .universePackage level => .universePackage level
  | .dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage =>
      .dependentProductPackage
        (rename mapping leftDomain) (rename mapping rightDomain)
        (rename (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping) leftCodomain)
        (rename (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping) rightCodomain)
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
    rename DeepWiki.Refine.DependentCalculus.Renaming.identity term = term := by
  induction term with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [rename, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [rename, domainInduction,
        DeepWiki.Refine.DependentCalculus.Renaming.lift_identity, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [rename, domainInduction,
        DeepWiki.Refine.DependentCalculus.Renaming.lift_identity, codomainInduction]
  | packageFamily => rfl
  | universePackage => rfl
  | dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage leftDomainInduction rightDomainInduction
      leftCodomainInduction rightCodomainInduction domainPackageInduction
      codomainPackageInduction =>
      simp only [rename, leftDomainInduction, rightDomainInduction,
        DeepWiki.Refine.DependentCalculus.Renaming.lift_identity,
        leftCodomainInduction, rightCodomainInduction, domainPackageInduction,
        Renaming.liftBy_identity, codomainPackageInduction]
  | relationProjection package packageInduction =>
      simp only [rename, packageInduction]

/-- Successive renamings act as their composition. -/
theorem rename_comp (term : Term source) (inner : Renaming source middle)
    (outer : Renaming middle target) :
    rename outer (rename inner term) =
      rename (DeepWiki.Refine.DependentCalculus.Renaming.comp outer inner) term := by
  induction term generalizing middle target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [rename, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [rename, domainInduction, bodyInduction,
        DeepWiki.Refine.DependentCalculus.Renaming.lift_comp]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [rename, domainInduction, codomainInduction,
        DeepWiki.Refine.DependentCalculus.Renaming.lift_comp]
  | packageFamily => rfl
  | universePackage => rfl
  | dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
      domainPackage codomainPackage leftDomainInduction rightDomainInduction
      leftCodomainInduction rightCodomainInduction domainPackageInduction
      codomainPackageInduction =>
      simp only [rename, leftDomainInduction, rightDomainInduction,
        leftCodomainInduction, rightCodomainInduction, domainPackageInduction,
        codomainPackageInduction,
        DeepWiki.Refine.DependentCalculus.Renaming.lift_comp,
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
      simp only [DeepWiki.Refine.DependentCalculus.Term.rename, ofCore, rename,
        functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [DeepWiki.Refine.DependentCalculus.Term.rename, ofCore, rename,
        domainInduction, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [DeepWiki.Refine.DependentCalculus.Term.rename, ofCore, rename,
        domainInduction, codomainInduction]

/-- Weaken an extended term by any finite number of fresh variables. -/
def weakenBy (term : Term n) : (amount : Nat) → Term (n + amount)
  | 0 => term
  | amount + 1 => (weakenBy term amount).rename
      DeepWiki.Refine.DependentCalculus.Renaming.shift

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
  ofRenaming DeepWiki.Refine.DependentCalculus.Renaming.identity

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
      DeepWiki.Refine.DependentCalculus.Renaming.shift)

/-- Lifting fixes the newest variable. -/
@[simp] theorem lift_zero (mapping : Substitution source target) :
    lift mapping 0 = .var 0 :=
  rfl

/-- Lifting weakens every substituted older variable. -/
@[simp] theorem lift_succ (mapping : Substitution source target) (index : Fin source) :
    lift mapping index.succ =
      (mapping index).rename DeepWiki.Refine.DependentCalculus.Renaming.shift :=
  rfl

/-- Lift an extended substitution beneath any number of binders. -/
def liftBy (mapping : Substitution source target) :
    (amount : Nat) → Substitution (source + amount) (target + amount)
  | 0 => mapping
  | amount + 1 => lift (liftBy mapping amount)

/-- Lifting a renaming substitution agrees with lifting its renaming. -/
@[simp] theorem lift_ofRenaming (mapping : Renaming source target) :
    lift (ofRenaming mapping) =
      ofRenaming (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Lifting the identity substitution gives the identity substitution. -/
@[simp] theorem lift_identity : lift (identity : Substitution n n) = identity := by
  simpa only [identity,
    DeepWiki.Refine.DependentCalculus.Renaming.lift_identity] using
    lift_ofRenaming (DeepWiki.Refine.DependentCalculus.Renaming.identity : Renaming n n)

/-- Lifting commutes with precomposition by a renaming. -/
theorem lift_precomp (substitute : Substitution middle target)
    (mapping : Renaming source middle) :
    lift (fun index => substitute (mapping index)) =
      fun index => lift substitute
        (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping index) := by
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
def ofCore (mapping : DeepWiki.Refine.DependentCalculus.Substitution source target) :
    Substitution source target :=
  fun index => Term.ofCore (mapping index)

/-- Lifting commutes with pointwise embedding of a core substitution. -/
@[simp] theorem lift_ofCore
    (mapping : DeepWiki.Refine.DependentCalculus.Substitution source target) :
    lift (ofCore mapping) =
      ofCore (DeepWiki.Refine.DependentCalculus.Substitution.lift mapping) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  exact (Term.ofCore_rename (mapping older)
    DeepWiki.Refine.DependentCalculus.Renaming.shift).symm

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
      (DeepWiki.Refine.DependentCalculus.Renaming.identity : Renaming n n)

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
    (mapping : DeepWiki.Refine.DependentCalculus.Substitution source target) :
    ofCore (term.substitute mapping) =
      substitute (Substitution.ofCore mapping) (ofCore term) := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DeepWiki.Refine.DependentCalculus.Term.substitute, ofCore, substitute,
        functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [DeepWiki.Refine.DependentCalculus.Term.substitute, ofCore, substitute,
        domainInduction, Substitution.lift_ofCore, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [DeepWiki.Refine.DependentCalculus.Term.substitute, ofCore, substitute,
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
        (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping) := by
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
        (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping)).instantiate
        (argument.rename mapping) := by
  simp only [instantiate, rename_substitute, substitute_rename]
  apply substitute_congr
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Instantiating a weakened term cancels the weakening. -/
@[simp] theorem instantiate_rename_shift (term : Term n) (argument : Term n) :
    (term.rename DeepWiki.Refine.DependentCalculus.Renaming.shift).instantiate argument =
      term := by
  simp only [instantiate, substitute_rename]
  rw [show (fun index =>
      Substitution.single argument
        (DeepWiki.Refine.DependentCalculus.Renaming.shift index)) =
      Substitution.identity by
    funext index
    rfl]
  exact substitute_identity term

/-- Lifted substitution after weakening equals substitution followed by weakening. -/
theorem substitute_rename_shift_lift (term : Term source)
    (mapping : Substitution source target) :
    (term.rename DeepWiki.Refine.DependentCalculus.Renaming.shift).substitute
        (Substitution.lift mapping) =
      (term.substitute mapping).rename
        DeepWiki.Refine.DependentCalculus.Renaming.shift := by
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
      DeepWiki.Refine.DependentCalculus.Renaming.shift).instantiate
      (argument.substitute mapping)
  exact (instantiate_rename_shift (mapping older) (argument.substitute mapping)).symm

end Term

/-- Embed a one-binder original endpoint into its three-binder relational context. -/
def originalBinderRenaming : Renaming (n + 1) (n + 3) :=
  Fin.cases ⟨2, by simp⟩ (fun index => index.succ.succ.succ)

/-- Original endpoint insertion sends its bound variable to the original slot. -/
@[simp] theorem originalBinderRenaming_zero :
    originalBinderRenaming (n := n) 0 = (2 : Fin (n + 3)) := rfl

/-- Original endpoint insertion shifts every ambient variable by three slots. -/
@[simp] theorem originalBinderRenaming_succ (index : Fin n) :
    originalBinderRenaming (n := n) index.succ = index.succ.succ.succ := rfl

/-- Embed a one-binder primed endpoint into its three-binder relational context. -/
def primedBinderRenaming : Renaming (n + 1) (n + 3) :=
  Fin.cases ⟨1, by simp⟩ (fun index => index.succ.succ.succ)

/-- Primed endpoint insertion sends its bound variable to the primed slot. -/
@[simp] theorem primedBinderRenaming_zero :
    primedBinderRenaming (n := n) 0 = (1 : Fin (n + 3)) := rfl

/-- Primed endpoint insertion shifts every ambient variable by three slots. -/
@[simp] theorem primedBinderRenaming_succ (index : Fin n) :
    primedBinderRenaming (n := n) index.succ = index.succ.succ.succ := rfl

/-- Original endpoint insertion commutes with ambient renaming. -/
theorem originalBinderRenaming_natural (mapping : Renaming source target) :
    DeepWiki.Refine.DependentCalculus.Renaming.comp
        (Renaming.liftBy mapping 3) (originalBinderRenaming (n := source)) =
      DeepWiki.Refine.DependentCalculus.Renaming.comp
        (originalBinderRenaming (n := target))
        (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

/-- Primed endpoint insertion commutes with ambient renaming. -/
theorem primedBinderRenaming_natural (mapping : Renaming source target) :
    DeepWiki.Refine.DependentCalculus.Renaming.comp
        (Renaming.liftBy mapping 3) (primedBinderRenaming (n := source)) =
      DeepWiki.Refine.DependentCalculus.Renaming.comp
        (primedBinderRenaming (n := target))
        (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

/-- Weakening commutes with lifting an ambient renaming. -/
theorem shiftRenaming_natural (mapping : Renaming source target) :
    DeepWiki.Refine.DependentCalculus.Renaming.comp
        (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping)
        DeepWiki.Refine.DependentCalculus.Renaming.shift =
      DeepWiki.Refine.DependentCalculus.Renaming.comp
        DeepWiki.Refine.DependentCalculus.Renaming.shift mapping := by
  funext index
  rfl

/-- Insert two function binders behind the three argument-relation binders. -/
def insertTwoAfterThree : Renaming (n + 3) (n + 5) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2
    (fun index => index.succ.succ.succ.succ.succ)))

namespace Term

/-- The object-language type of level-`i` binary relations between two endpoint types. -/
def relationType (level : Nat) (left right : Term n) : Term n :=
  .pi left (.pi (right.rename DeepWiki.Refine.DependentCalculus.Renaming.shift) (.sort level))

/-- Apply the level-indexed package family to two endpoint types. -/
def packageType (level : Nat) (left right : Term n) : Term n :=
  .app (.app (.packageFamily level) left) right

/-- Apply a binary relation to its two endpoint terms. -/
def relationApplication (relation left right : Term n) : Term n :=
  .app (.app relation left) right

/-- Project the binary relation carried by a package. -/
def rel (package : Term n) : Term n :=
  .relationProjection package

/-- Form the relation type of the two newest endpoint variables. -/
def relatedDomain (package : Term n) : Term (n + 2) :=
  relationApplication (.relationProjection (package.weakenBy 2)) (.var 1) (.var 0)

/-- Relation types are natural under ambient renaming. -/
theorem relationType_rename (level : Nat) (left right : Term source)
    (mapping : Renaming source target) :
    (relationType level left right).rename mapping =
      relationType level (left.rename mapping) (right.rename mapping) := by
  simp only [relationType, rename, rename_comp]
  apply congrArg (Term.pi _)
  apply congrArg (fun domain => Term.pi domain (.sort level))
  apply rename_congr
  funext index
  rfl

/-- Package-family applications are natural under ambient renaming. -/
theorem packageType_rename (level : Nat) (left right : Term source)
    (mapping : Renaming source target) :
    (packageType level left right).rename mapping =
      packageType level (left.rename mapping) (right.rename mapping) :=
  rfl

/-- Original endpoint codomain embedding is natural under ambient renaming. -/
theorem originalBinder_rename (codomain : Term (source + 1))
    (mapping : Renaming source target) :
    (codomain.rename (originalBinderRenaming (n := source))).rename
        (Renaming.liftBy mapping 3) =
      (codomain.rename
        (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping)).rename
        (originalBinderRenaming (n := target)) := by
  simp only [rename_comp]
  apply rename_congr
  exact originalBinderRenaming_natural mapping

/-- Primed endpoint codomain embedding is natural under ambient renaming. -/
theorem primedBinder_rename (codomain : Term (source + 1))
    (mapping : Renaming source target) :
    (codomain.rename (primedBinderRenaming (n := source))).rename
        (Renaming.liftBy mapping 3) =
      (codomain.rename
        (DeepWiki.Refine.DependentCalculus.Renaming.lift mapping)).rename
        (primedBinderRenaming (n := target)) := by
  simp only [rename_comp]
  apply rename_congr
  exact primedBinderRenaming_natural mapping

/-- The projected relation binder is natural under renaming of its ambient scope. -/
theorem relatedDomain_rename (package : Term source)
    (mapping : Renaming source target) :
    relatedDomain (package.rename mapping) =
      (relatedDomain package).rename (Renaming.liftBy mapping 2) := by
  simp only [relatedDomain, relationApplication, rename, weakenBy_rename]
  rfl

/-- The projected relation binder is natural under substitution of its ambient scope. -/
theorem relatedDomain_substitute (package : Term source)
    (mapping : Substitution source target) :
    relatedDomain (package.substitute mapping) =
      (relatedDomain package).substitute (Substitution.liftBy mapping 2) := by
  simp only [relatedDomain, relationApplication, Term.substitute,
    weakenBy_substitute]
  congr 1

/-- Relation types are natural under simultaneous substitution. -/
theorem relationType_substitute (level : Nat) (left right : Term source)
    (mapping : Substitution source target) :
    (relationType level left right).substitute mapping =
      relationType level (left.substitute mapping) (right.substitute mapping) := by
  simp only [relationType, substitute]
  apply congrArg (Term.pi _)
  apply congrArg (fun domain => Term.pi domain (.sort level))
  exact substitute_rename_shift_lift right mapping

/-- Package-family applications are natural under simultaneous substitution. -/
theorem packageType_substitute (level : Nat) (left right : Term source)
    (mapping : Substitution source target) :
    (packageType level left right).substitute mapping =
      packageType level (left.substitute mapping) (right.substitute mapping) :=
  rfl

/-- Original endpoint codomain embedding is natural under substitution. -/
theorem originalBinder_substitute (codomain : Term (source + 1))
    (mapping : Substitution source target) :
    (codomain.rename (originalBinderRenaming (n := source))).substitute
        (Substitution.liftBy mapping 3) =
      (codomain.substitute (Substitution.lift mapping)).rename
        (originalBinderRenaming (n := target)) := by
  rw [substitute_rename, rename_substitute]
  apply substitute_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  change (mapping older).weakenBy 3 =
    ((mapping older).rename
      DeepWiki.Refine.DependentCalculus.Renaming.shift).rename
      originalBinderRenaming
  simp only [weakenBy, rename_comp]
  apply rename_congr
  funext element
  rfl

/-- Primed endpoint codomain embedding is natural under substitution. -/
theorem primedBinder_substitute (codomain : Term (source + 1))
    (mapping : Substitution source target) :
    (codomain.rename (primedBinderRenaming (n := source))).substitute
        (Substitution.liftBy mapping 3) =
      (codomain.substitute (Substitution.lift mapping)).rename
        (primedBinderRenaming (n := target)) := by
  rw [substitute_rename, rename_substitute]
  apply substitute_congr
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  change (mapping older).weakenBy 3 =
    ((mapping older).rename
      DeepWiki.Refine.DependentCalculus.Renaming.shift).rename
      primedBinderRenaming
  simp only [weakenBy, rename_comp]
  apply rename_congr
  funext element
  rfl

/-- The relation field of the universe package is the package family itself. -/
def universeRelation (level : Nat) : Term n :=
  .packageFamily level

/-- The dependent respectful relation with all endpoint data explicit. -/
def dependentProductRelation
    (leftDomain rightDomain : Term n)
    (leftCodomain rightCodomain : Term (n + 1))
    (domainPackage : Term n) (codomainPackage : Term (n + 3)) : Term n :=
  .lam (.pi leftDomain leftCodomain)
    (.lam ((Term.pi rightDomain rightCodomain : Term n).weakenBy 1)
      (.pi (leftDomain.weakenBy 2)
        (.pi (rightDomain.weakenBy 3)
          (.pi
            (relationApplication
              (.relationProjection (domainPackage.weakenBy 4)) (.var 1) (.var 0))
            (relationApplication
              (.relationProjection
                (codomainPackage.rename insertTwoAfterThree))
              (.app (.var 4) (.var 2))
              (.app (.var 3) (.var 1)))))))

/-- Contract a head relation projection from either canonical package constructor. -/
def contractProjection : Term n → Term n
  | .relationProjection (.universePackage level) => universeRelation level
  | .relationProjection
      (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage) =>
      dependentProductRelation leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage
  | term => term

/-- Projecting `p□` computes to the univalent package family. -/
@[simp] theorem contractProjection_universePackage (level : Nat) :
    contractProjection (.relationProjection (.universePackage level) : Term n) =
      universeRelation level :=
  rfl

/-- Projecting `pΠ` computes to its dependent respectful relation. -/
@[simp] theorem contractProjection_dependentProductPackage
    (leftDomain rightDomain : Term n)
    (leftCodomain rightCodomain : Term (n + 1))
    (domainPackage : Term n) (codomainPackage : Term (n + 3)) :
    contractProjection
        (.relationProjection
          (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
            domainPackage codomainPackage)) =
      dependentProductRelation leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage :=
  rfl

end Term

example (level : Nat) :
    Term.contractProjection
        (.relationProjection (.universePackage level) : Term n) =
      .packageFamily level :=
  rfl

example (leftDomain rightDomain : Term n)
    (leftCodomain rightCodomain : Term (n + 1))
    (domainPackage : Term n) (codomainPackage : Term (n + 3)) :
    Term.contractProjection
        (.relationProjection
          (.dependentProductPackage leftDomain rightDomain leftCodomain rightCodomain
            domainPackage codomainPackage)) =
      Term.dependentProductRelation leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage :=
  rfl

end DeepWiki.Refine.DependentCalculus.UnivalentParametricity
