import DeepWiki.Refine.Parametricity.Univalent.SurfaceSyntax
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
    DependentCalculus.Renaming.comp
        (Renaming.liftBy mapping 3) (originalBinderRenaming (n := source)) =
      DependentCalculus.Renaming.comp
        (originalBinderRenaming (n := target))
        (DependentCalculus.Renaming.lift mapping) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

/-- Primed endpoint insertion commutes with ambient renaming. -/
theorem primedBinderRenaming_natural (mapping : Renaming source target) :
    DependentCalculus.Renaming.comp
        (Renaming.liftBy mapping 3) (primedBinderRenaming (n := source)) =
      DependentCalculus.Renaming.comp
        (primedBinderRenaming (n := target))
        (DependentCalculus.Renaming.lift mapping) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  rfl

/-- Weakening commutes with lifting an ambient renaming. -/
theorem shiftRenaming_natural (mapping : Renaming source target) :
    DependentCalculus.Renaming.comp
        (DependentCalculus.Renaming.lift mapping)
        DependentCalculus.Renaming.shift =
      DependentCalculus.Renaming.comp
        DependentCalculus.Renaming.shift mapping := by
  funext index
  rfl

/-- Insert two function binders behind the three argument-relation binders. -/
def insertTwoAfterThree : Renaming (n + 3) (n + 5) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2
    (fun index => index.succ.succ.succ.succ.succ)))

namespace Term

/-- The object-language type of level-`i` binary relations between two endpoint types. -/
def relationType (level : Nat) (left right : Term n) : Term n :=
  uω!{
    Π leftValue : %{left},
    Π rightValue : %{right.rename DependentCalculus.Renaming.shift},
    □[level] }

/-- Apply the level-indexed package family to two endpoint types. -/
def packageType (level : Nat) (left right : Term n) : Term n :=
  uω!{ Pkg[level] %{left} %{right} }

/-- Apply a binary relation to its two endpoint terms. -/
def relationApplication (relation left right : Term n) : Term n :=
  uω!{ %{relation} %{left} %{right} }

/-- Project the binary relation carried by a package. -/
def rel (package : Term n) : Term n :=
  uω!{ rel(%{package}) }

/-- Form the relation type of the two newest endpoint variables. -/
def relatedDomain (package : Term n) : Term (n + 2) :=
  uω!{
    rel(%{package.weakenBy 2})
      %{(.var 1 : Term (n + 2))}
      %{(.var 0 : Term (n + 2))} }

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
        (DependentCalculus.Renaming.lift mapping)).rename
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
        (DependentCalculus.Renaming.lift mapping)).rename
        (primedBinderRenaming (n := target)) := by
  simp only [rename_comp]
  apply rename_congr
  exact primedBinderRenaming_natural mapping

/-- The projected relation binder is natural under renaming of its ambient scope. -/
theorem relatedDomain_rename (package : Term source)
    (mapping : Renaming source target) :
    relatedDomain (package.rename mapping) =
      (relatedDomain package).rename (Renaming.liftBy mapping 2) := by
  simp only [relatedDomain, rename, weakenBy_rename]
  rfl

/-- The projected relation binder is natural under substitution of its ambient scope. -/
theorem relatedDomain_substitute (package : Term source)
    (mapping : Substitution source target) :
    relatedDomain (package.substitute mapping) =
      (relatedDomain package).substitute (Substitution.liftBy mapping 2) := by
  simp only [relatedDomain, Term.substitute, weakenBy_substitute]
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
      DependentCalculus.Renaming.shift).rename
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
      DependentCalculus.Renaming.shift).rename
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
  uω!{
    λ leftFunction : (Π leftArgument : %{leftDomain}, %{leftCodomain}),
    λ rightFunction :
      %{(uω!{
        Π rightArgument : %{rightDomain}, %{rightCodomain} }).weakenBy 1},
    Π leftArgument : %{leftDomain.weakenBy 2},
    Π rightArgument : %{rightDomain.weakenBy 3},
    Π relatedArgument :
      rel(%{domainPackage.weakenBy 4}) leftArgument rightArgument,
    rel(%{codomainPackage.rename insertTwoAfterThree})
      (leftFunction leftArgument) (rightFunction rightArgument) }

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
        (uω!{
          rel(pΠ[
            (leftValue : %{leftDomain}) ↦ %{leftCodomain};
            (rightValue : %{rightDomain}) ↦ %{rightCodomain};
            (relatedValue : rel(%{domainPackage}) leftValue rightValue) ↦
              %{codomainPackage}]) }) =
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
        (uω!{
          rel(pΠ[
            (leftValue : %{leftDomain}) ↦ %{leftCodomain};
            (rightValue : %{rightDomain}) ↦ %{rightCodomain};
            (relatedValue : rel(%{domainPackage}) leftValue rightValue) ↦
              %{codomainPackage}]) }) =
      Term.dependentProductRelation leftDomain rightDomain leftCodomain rightCodomain
        domainPackage codomainPackage :=
  rfl

end DeepWiki.Refine.DependentCalculus.UnivalentParametricity
