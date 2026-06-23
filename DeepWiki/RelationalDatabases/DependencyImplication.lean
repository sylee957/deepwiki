import DeepWiki.RelationalDatabases.MultivaluedDependencies
import DeepWiki.RelationalDatabases.NormalForms

/-! # Mixed dependency implication and fourth normal form
Functional- and multivalued-dependency reasoning over one scheme is unified by a *mixed* implication
relation: a set `D` of dependencies (each an fd `X → Y` or an mvd `X ↠ Y`) *implies* a dependency
when every relation satisfying all of `D` satisfies it. Each row-level inference rule lifts to this
relation by quantifying over relations.

With implication in hand a *superkey* is `D ⊨ X → Ω`, and a scheme is in *fourth normal form* when
every nontrivial implied mvd has a superkey left-hand side. We prove `4NF ⟹ BCNF`. -/

namespace DeepWiki

universe u v

variable {Att : Type u} [DecidableEq Att] {Val : Type v} {Ω : Finset Att}

/-- A dependency over a scheme: a functional dependency `X → Y` or a multivalued dependency
`X ↠ Y`. -/
inductive Dep (Att : Type u) where
  /-- A functional dependency `X → Y`. -/
  | fd : Finset Att → Finset Att → Dep Att
  /-- A multivalued dependency `X ↠ Y`. -/
  | mvd : Finset Att → Finset Att → Dep Att

/-- A row set satisfies a dependency. -/
def Dep.Satisfies {Ω : Finset Att} (r : Table Ω Val) : Dep Att → Prop
  | .fd X Y => SatisfiesFd r X Y
  | .mvd X Y => SatisfiesMvd r X Y

/-- A mixed dependency set `D` *implies* `d` over scheme `Ω`: every relation satisfying all of `D`
satisfies `d`. -/
def DepImplies (Ω : Finset Att) (Val : Type v) (D : Set (Dep Att)) (d : Dep Att) : Prop :=
  ∀ r : Table Ω Val, (∀ e ∈ D, Dep.Satisfies r e) → Dep.Satisfies r d

variable {D : Set (Dep Att)} {X Y Z W V : Finset Att}

/-- Rule FM1 at the implication level: an implied fd is an implied mvd. -/
theorem depImplies_mvd_of_fd (h : DepImplies Ω Val D (.fd X Y)) :
    DepImplies Ω Val D (.mvd X Y) :=
  fun r hr => satisfiesMvd_of_satisfiesFd (h r hr)

/-- Rule M1 at the implication level (complementation). -/
theorem depImplies_mvd_complement (h : DepImplies Ω Val D (.mvd X Y)) :
    DepImplies Ω Val D (.mvd X (Ω \ Y)) :=
  fun r hr => satisfiesMvd_complement (h r hr)

/-- Rule M2 at the implication level (augmentation). -/
theorem depImplies_mvd_augment (hVW : V ⊆ W) (h : DepImplies Ω Val D (.mvd X Y)) :
    DepImplies Ω Val D (.mvd (W ∪ X) (V ∪ Y)) :=
  fun r hr => satisfiesMvd_augment hVW (h r hr)

/-- Rule M3 at the implication level (mvd-transitivity). -/
theorem depImplies_mvd_trans (hXY : DepImplies Ω Val D (.mvd X Y))
    (hYZ : DepImplies Ω Val D (.mvd Y Z)) : DepImplies Ω Val D (.mvd X (Z \ Y)) :=
  fun r hr => satisfiesMvd_trans (hXY r hr) (hYZ r hr)

/-- Rule FM2 at the implication level (mixed pseudotransitivity). -/
theorem depImplies_fd_of_mvd_fd (hXY : DepImplies Ω Val D (.mvd X Y))
    (hYZ : DepImplies Ω Val D (.fd Y Z)) : DepImplies Ω Val D (.fd X (Z \ Y)) :=
  fun r hr => satisfiesFd_of_mvd_fd (hXY r hr) (hYZ r hr)

/-- Rule M4 at the implication level (mvd-union). -/
theorem depImplies_mvd_union (hXY : DepImplies Ω Val D (.mvd X Y))
    (hXZ : DepImplies Ω Val D (.mvd X Z)) : DepImplies Ω Val D (.mvd X (Y ∪ Z)) :=
  fun r hr => satisfiesMvd_union (hXY r hr) (hXZ r hr)

/-- `X` is a *superkey* with respect to a mixed dependency set: `D ⊨ X → Ω`. -/
def IsSuperkeyDep (Ω : Finset Att) (Val : Type v) (D : Set (Dep Att)) (X : Finset Att) : Prop :=
  DepImplies Ω Val D (.fd X Ω)

/-- A scheme with mixed dependency set `D` is in *fourth normal form*: every nontrivial implied
multivalued dependency `X ↠ Y` (`Y ⊄ X` and `X ∪ Y` not covering `Ω`) has `X` a superkey. -/
def Is4NF (Ω : Finset Att) (Val : Type v) (D : Set (Dep Att)) : Prop :=
  ∀ X Y : Finset Att, DepImplies Ω Val D (.mvd X Y) →
    ¬ (Y ⊆ X) → ¬ (Ω ⊆ X ∪ Y) → IsSuperkeyDep Ω Val D X

/-- A scheme with mixed dependency set `D` is in *Boyce–Codd normal form*: every implied `X → {A}`
(`A ∈ Ω`) has `A ∈ X` or `X` a superkey. -/
def IsBCNFDep (Ω : Finset Att) (Val : Type v) (D : Set (Dep Att)) : Prop :=
  ∀ (X : Finset Att) (A : Att), A ∈ Ω → DepImplies Ω Val D (.fd X {A}) →
    A ∈ X ∨ IsSuperkeyDep Ω Val D X

/-- If `D ⊨ X → {A}` and `X ∪ {A}` already covers `Ω`, then `X` is a superkey: `X` determines `A`
and contains all of `Ω` apart from `A`. -/
theorem isSuperkeyDep_of_fd_cover {A : Att} (hXA : DepImplies Ω Val D (.fd X {A}))
    (hcov : Ω ⊆ X ∪ {A}) : IsSuperkeyDep Ω Val D X := by
  intro r hr t ht u hu hag
  have hA : Agree {A} t u := hXA r hr t ht u hu hag
  intro a ha
  rcases Finset.mem_union.mp (hcov ha) with hX | hAeq
  · exact hag a hX
  · exact hA a hAeq

/-- A scheme in fourth normal form is in Boyce–Codd normal form. A nontrivial implied fd `X → {A}`
lifts (FM1) to a nontrivial mvd `X ↠ {A}`, so 4NF makes `X` a superkey; a *trivial* one (`X ∪ {A}`
covering `Ω`) already makes `X` a superkey. -/
theorem isBCNFDep_of_is4NF (h : Is4NF Ω Val D) : IsBCNFDep Ω Val D := by
  intro X A hA hXA
  by_cases hAX : A ∈ X
  · exact Or.inl hAX
  · refine Or.inr ?_
    by_cases hcov : Ω ⊆ X ∪ {A}
    · exact isSuperkeyDep_of_fd_cover hXA hcov
    · refine h X {A} (depImplies_mvd_of_fd hXA) ?_ hcov
      intro hsub
      exact hAX (hsub (Finset.mem_singleton_self A))

end DeepWiki
