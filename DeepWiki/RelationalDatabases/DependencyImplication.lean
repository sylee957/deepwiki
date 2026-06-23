import DeepWiki.RelationalDatabases.MultivaluedDependencies
import DeepWiki.RelationalDatabases.NormalForms

/-! # Mixed dependency implication and fourth normal form
Functional- and multivalued-dependency reasoning over one scheme is unified by a *mixed* implication
relation: a set `D` of dependencies (each an fd `X → Y` or an mvd `X ↠ Y`) *implies* a dependency
when every relation satisfying all of `D` satisfies it. Each row-level inference rule lifts to this
relation by quantifying over relations (all of FM1/M0–M4/FM2 for mvds and the Armstrong rules for
fds).

With implication in hand a *superkey* is `D ⊨ X → Ω`, a scheme is in *fourth normal form* when
every nontrivial implied mvd has a superkey left-hand side, and in *fifth normal form* when every
implied join dependency is implied by the key dependencies. We prove `4NF ⟹ BCNF` and
`5NF ⟹ 4NF`. -/

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

/-- A dependency in the set is implied by it. -/
theorem depImplies_of_mem {d : Dep Att} (hd : d ∈ D) : DepImplies Ω Val D d :=
  fun _ hr => hr d hd

/-- A trivial fd (`Y ⊆ X`) is implied by any dependency set. -/
theorem depImplies_fd_trivial (h : Y ⊆ X) : DepImplies Ω Val D (.fd X Y) :=
  fun _ _ => satisfiesFd_trivial h

/-- A trivial mvd (`Y ⊆ X`) is implied by any dependency set. -/
theorem depImplies_mvd_trivial (h : Y ⊆ X) : DepImplies Ω Val D (.mvd X Y) :=
  fun _ _ => satisfiesMvd_trivial h

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

/-- Armstrong transitivity at the implication level. -/
theorem depImplies_fd_trans (hXY : DepImplies Ω Val D (.fd X Y))
    (hYZ : DepImplies Ω Val D (.fd Y Z)) : DepImplies Ω Val D (.fd X Z) :=
  fun r hr => satisfiesFd_trans (hXY r hr) (hYZ r hr)

/-- Armstrong augmentation at the implication level. -/
theorem depImplies_fd_augment (h : DepImplies Ω Val D (.fd X Y)) :
    DepImplies Ω Val D (.fd X (X ∪ Y)) :=
  fun r hr => satisfiesFd_augment (h r hr)

/-- Functional-dependency union at the implication level. -/
theorem depImplies_fd_union (hXY : DepImplies Ω Val D (.fd X Y))
    (hXZ : DepImplies Ω Val D (.fd X Z)) : DepImplies Ω Val D (.fd X (Y ∪ Z)) :=
  fun r hr => satisfiesFd_unionRule (hXY r hr) (hXZ r hr)

/-- Functional-dependency decomposition at the implication level. -/
theorem depImplies_fd_decompose (h : DepImplies Ω Val D (.fd X (Y ∪ Z))) :
    DepImplies Ω Val D (.fd X Y) :=
  fun r hr => satisfiesFd_decompose (h r hr)

/-- `X` is a *superkey* with respect to a mixed dependency set: `D ⊨ X → Ω`. -/
def IsSuperkeyDep (Ω : Finset Att) (Val : Type v) (D : Set (Dep Att)) (X : Finset Att) : Prop :=
  DepImplies Ω Val D (.fd X Ω)

/-- A scheme with mixed dependency set `D` is in *fourth normal form*: every nontrivial implied
multivalued dependency `X ↠ Y` (`Y ⊄ X` and `X ∪ Y` not covering `Ω`) has `X` a superkey. -/
def Is4NF (Ω : Finset Att) (Val : Type v) (D : Set (Dep Att)) : Prop :=
  ∀ X Y : Finset Att, Y ⊆ Ω → DepImplies Ω Val D (.mvd X Y) →
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
    · refine h X {A} (Finset.singleton_subset_iff.mpr hA) (depImplies_mvd_of_fd hXA) ?_ hcov
      intro hsub
      exact hAX (hsub (Finset.mem_singleton_self A))

/-! ## Fifth normal form (project-join normal form) -/

/-- `X` is a superkey whenever some superkey `Z` is contained in `X` over `Ω`. -/
theorem isSuperkeyDep_of_subset {Z : Finset Att} (hZ : IsSuperkeyDep Ω Val D Z)
    (hsub : ∀ a : {x // x ∈ Ω}, a.val ∈ Z → a.val ∈ X) : IsSuperkeyDep Ω Val D X :=
  fun r hr s₁ hs₁ s₂ hs₂ hag => hZ r hr s₁ hs₁ s₂ hs₂ (fun a ha => hag a (hsub a ha))

/-- A scheme with mixed dependency set `D` is in *fifth normal form* (project-join normal form,
Def 4.8): every (finite) join dependency implied by `D` is already implied by the key dependencies
`{X → Ω | D ⊨ X → Ω}`. -/
def Is5NF (Ω : Finset Att) (Val : Type v) (D : Set (Dep Att)) : Prop :=
  ∀ {ι : Type} [Fintype ι] (comp : ι → Finset Att),
    (∀ r : Table Ω Val, (∀ e ∈ D, Dep.Satisfies r e) → SatisfiesJd r comp) →
    ∀ r : Table Ω Val, (∀ Z : Finset Att, IsSuperkeyDep Ω Val D Z → SatisfiesFd r Z Ω) →
      SatisfiesJd r comp

/-- **Theorem 4.8**: a relation scheme in fifth normal form is in fourth normal form. A nontrivial
implied mvd is the two-component jd `⋈[X∪Y, X∪(Ω−Y)]` (Theorem 3.9), so 5NF makes it implied by the
keys; the two-tuple relation agreeing exactly on `X` satisfies every key fd (else `X` would already
be a superkey) yet violates that jd unless `X` is a superkey. -/
theorem is4NF_of_is5NF [Nontrivial Val] (h5 : Is5NF Ω Val D) : Is4NF Ω Val D := by
  intro X Y hYΩ hmvd hnY hnc
  by_contra hnsk
  obtain ⟨v0, v1, hv⟩ := exists_pair_ne Val
  set t : Tuple Ω Val := (fun _ => v0) with ht
  set u : Tuple Ω Val := (fun a => if a.val ∈ X then v0 else v1) with hu
  have htu : ∀ a : {x // x ∈ Ω}, t a = u a ↔ a.val ∈ X := by
    intro a
    simp only [ht, hu]
    by_cases haX : a.val ∈ X
    · simp [haX]
    · simp [haX, hv]
  have hkeysat : ∀ Z : Finset Att, IsSuperkeyDep Ω Val D Z →
      SatisfiesFd ({t, u} : Table Ω Val) Z Ω := by
    intro Z hZ s₁ hs₁ s₂ hs₂ hag
    have key : Agree Z t u → False := fun hagZ =>
      hnsk (isSuperkeyDep_of_subset hZ (fun a ha => (htu a).mp (hagZ a ha)))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs₁ hs₂
    rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl
    · exact fun _ _ => rfl
    · exact absurd hag key
    · exact absurd hag.symm key
    · exact fun _ _ => rfl
  have hjdStar : SatisfiesJd ({t, u} : Table Ω Val) (mvdComp X Y Ω) :=
    h5 (mvdComp X Y Ω) (fun r hr => satisfiesMvd_iff_satisfiesJd.mp (hmvd r hr))
      ({t, u} : Table Ω Val) hkeysat
  have hmvdStar : SatisfiesMvd ({t, u} : Table Ω Val) X Y :=
    satisfiesMvd_iff_satisfiesJd.mpr hjdStar
  obtain ⟨w, hw, hwt, hwu⟩ :=
    hmvdStar t (Set.mem_insert _ _) u (Set.mem_insert_iff.mpr (Or.inr rfl))
      (fun a ha => (htu a).mpr ha)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · apply hnc
    intro a ha
    by_contra haXY
    simp only [Finset.mem_union, not_or] at haXY
    exact haXY.1 ((htu ⟨a, ha⟩).mp
      (hwu ⟨a, ha⟩ (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨ha, haXY.2⟩)))))
  · apply hnY
    intro b hb
    exact (htu ⟨b, hYΩ hb⟩).mp (hwt ⟨b, hYΩ hb⟩ (Finset.mem_union.mpr (Or.inr hb))).symm

/-! ## Dependency basis (Theorem 3.11) -/

/-- Two attributes lie in the same *dependency-basis block* of `X` (w.r.t. `D`) when every implied
multivalued dependency `X ↠ Y` contains both or neither. The blocks are the classes of this
equivalence — the partition `DepB(X)` of Theorem 3.11; the implied mvds `X ↠ Y` are exactly those
whose right side is a union of blocks. -/
def SameBlock (Ω : Finset Att) (Val : Type v) (D : Set (Dep Att)) (X : Finset Att) (A B : Att) :
    Prop :=
  ∀ Y : Finset Att, DepImplies Ω Val D (.mvd X Y) → (A ∈ Y ↔ B ∈ Y)

/-- `SameBlock` is reflexive. -/
theorem SameBlock.refl (A : Att) : SameBlock Ω Val D X A A := fun _ _ => Iff.rfl

/-- `SameBlock` is symmetric. -/
theorem SameBlock.symm {A B : Att} (h : SameBlock Ω Val D X A B) : SameBlock Ω Val D X B A :=
  fun Y hY => (h Y hY).symm

/-- `SameBlock` is transitive. -/
theorem SameBlock.trans {A B C : Att} (hAB : SameBlock Ω Val D X A B)
    (hBC : SameBlock Ω Val D X B C) : SameBlock Ω Val D X A C :=
  fun Y hY => (hAB Y hY).trans (hBC Y hY)

/-- **Theorem 3.11** (forward direction): the right side of an implied multivalued dependency is a
union of dependency-basis blocks — it is saturated under `SameBlock` (if it contains `A` it contains
every attribute in `A`'s block). -/
theorem mem_of_sameBlock_of_depImplies {X Y : Finset Att} (h : DepImplies Ω Val D (.mvd X Y))
    {A B : Att} (hA : A ∈ Y) (hAB : SameBlock Ω Val D X A B) : B ∈ Y :=
  (hAB Y h).mp hA

/-- An attribute determined by `X` forms a singleton block: if `D ⊨ X → {A}` then `A`'s block is
`{A}` (every block-mate of `A` equals `A`). This is the `{A} ∈ DepB(X)` clause of Theorem 3.11. -/
theorem sameBlock_singleton_of_fd {X : Finset Att} {A : Att}
    (hA : DepImplies Ω Val D (.fd X {A})) {B : Att} (hAB : SameBlock Ω Val D X A B) : B = A := by
  have hmvd : DepImplies Ω Val D (.mvd X {A}) := depImplies_mvd_of_fd hA
  have : B ∈ ({A} : Finset Att) := (hAB {A} hmvd).mp (Finset.mem_singleton_self A)
  exact Finset.mem_singleton.mp this

end DeepWiki
