import DeepWiki.NetworkCalculus.WorstCaseBoundNPHardness

/-! # 3-Dimensional Matching reduces to Exact-3-Cover (Karp `3DM ≤ₖ X3C`)
This file builds the classical textbook Karp reduction **3-Dimensional Matching ⤳
Exact-Cover-by-3-Sets** (Garey & Johnson, *Computers and Intractability*, 1979; Karp 1972),
on the `KarpReduction` framework. 3DM is the special case of X3C in which the `3q`-element
ground set is *tripartite* — `W ⊕ X ⊕ Y` with `|W| = |X| = |Y| = q` — and the 3-subsets are
exactly the triples `{w, x, y}` of a triple family `M ⊆ W × X × Y`. So 3DM is *literally* a
restricted X3C, and the reduction is the structural inclusion `M ↦ (the induced X3C
instance)`, with the genuine bi-implication **`M has a perfect matching ↔ the induced X3C
instance has an exact 3-cover`** as its many-one correctness.

This **relocates** the cited NP-completeness axiom one step toward Cook–Levin: chaining the
new `threeDMToX3C` reduction with the existing `x3cToWorstCaseBacklog` lets the worst-case
backlog NP-hardness rest on the cited fact "**3DM is NP-complete**" (Garey-Johnson SP1 /
Karp 1972) — a *more canonical* seed — instead of "X3C is NP-complete". It does **NOT**
discharge the axiom: some base NP-complete problem (3DM, or SAT via Cook–Levin) is still
cited, not proved (a Turing-machine framework Mathlib lacks). What *is* proved here is the
reduction map and its correctness; what is *cited* is `ThreeDMIsNPHard`.

The reduction `correct` proof (matching ⟺ cover) is genuine: a matching `N ⊆ M` is read as
the assignment routing each ground element to the unique matching triple containing it, and
its triples are exactly the saturated subsets forming the exact cover; conversely an exact
cover's `q` saturated triples are a perfect matching. -/

namespace DeepWiki

open Finset

/-! ## The tripartite ground type of a 3DM instance
3DM's ground set is the disjoint union `W ⊎ X ⊎ Y` of three `q`-element types. We model it
as `W ⊕ X ⊕ Y` (`Sum W (Sum X Y)`, right-associated); the X3C ground set the reduction
outputs is exactly this type, and each triple `(w, x, y)` becomes the 3-subset
`{groundW w, groundX x, groundY y}`. -/

/-- The **tripartite ground type** `W ⊕ X ⊕ Y` of a 3DM instance with parts `W`, `X`, `Y` —
the disjoint union that becomes the X3C ground set under the reduction. -/
abbrev ThreeDMGround (W X Y : Type*) : Type _ := W ⊕ X ⊕ Y

/-- Inject the `W`-coordinate `w` into the ground `W ⊕ X ⊕ Y` (`= inl w`). -/
def groundW {W X Y : Type*} (w : W) : ThreeDMGround W X Y := Sum.inl w

/-- Inject the `X`-coordinate `x` into the ground `W ⊕ X ⊕ Y` (`= inr (inl x)`). -/
def groundX {W X Y : Type*} (x : X) : ThreeDMGround W X Y := Sum.inr (Sum.inl x)

/-- Inject the `Y`-coordinate `y` into the ground `W ⊕ X ⊕ Y` (`= inr (inr y)`). -/
def groundY {W X Y : Type*} (y : Y) : ThreeDMGround W X Y := Sum.inr (Sum.inr y)

/-- Inject a triple `(w, x, y)` to its 3-element ground subset
`{groundW w, groundX x, groundY y} ⊆ W ⊕ X ⊕ Y`. -/
def tripleGround {W X Y : Type*} [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    (t : W × X × Y) : Finset (ThreeDMGround W X Y) :=
  {groundW t.1, groundX t.2.1, groundY t.2.2}

variable {W X Y : Type*}

/-- A `W`-coordinate and an `X`-coordinate never coincide in the ground type. -/
theorem groundW_ne_groundX (w : W) (x : X) :
    (groundW w : ThreeDMGround W X Y) ≠ groundX x := by simp [groundW, groundX]

/-- A `W`-coordinate and a `Y`-coordinate never coincide in the ground type. -/
theorem groundW_ne_groundY (w : W) (y : Y) :
    (groundW w : ThreeDMGround W X Y) ≠ groundY y := by simp [groundW, groundY]

/-- An `X`-coordinate and a `Y`-coordinate never coincide in the ground type. -/
theorem groundX_ne_groundY (x : X) (y : Y) :
    (groundX x : ThreeDMGround W X Y) ≠ groundY y := by simp [groundX, groundY]

variable [DecidableEq W] [DecidableEq X] [DecidableEq Y]

/-- Each induced ground subset has exactly three elements (the three coordinates of the
triple are pairwise distinct as ground elements). -/
theorem card_tripleGround (t : W × X × Y) :
    (tripleGround t).card = 3 := by
  rw [tripleGround, Finset.card_eq_three]
  exact ⟨_, _, _, groundW_ne_groundX _ _, groundW_ne_groundY _ _, groundX_ne_groundY _ _, rfl⟩

/-! ## The 3DM instance
A **3-Dimensional Matching** instance: three disjoint `q`-element parts `W`, `X`, `Y` (here
`Fintype`s of common cardinality `q`) and a triple family `M ⊆ W × X × Y`. A *perfect
matching* is a sub-family `N ⊆ M` that covers each ground element exactly once. -/

/-- A **3-Dimensional Matching instance**: three finite parts `W`, `X`, `Y` of common
cardinality `q` and a triple family `M ⊆ W × X × Y`. (Bundled into one `Type` like
`WellFormedX3C`, so the reduction can range over all instances.) -/
structure ThreeDMInstance where
  /-- The first part of the tripartite ground set. -/
  W : Type
  /-- The second part of the tripartite ground set. -/
  X : Type
  /-- The third part of the tripartite ground set. -/
  Y : Type
  /-- `W` is finite. -/
  [fW : Fintype W]
  /-- `X` is finite. -/
  [fX : Fintype X]
  /-- `Y` is finite. -/
  [fY : Fintype Y]
  /-- `W` has decidable equality. -/
  [dW : DecidableEq W]
  /-- `X` has decidable equality. -/
  [dX : DecidableEq X]
  /-- `Y` has decidable equality. -/
  [dY : DecidableEq Y]
  /-- The triple family `M ⊆ W × X × Y`. -/
  M : Finset (W × X × Y)
  /-- The common part size `q`. -/
  q : ℕ
  /-- `W` has `q` elements. -/
  card_W : Fintype.card W = q
  /-- `X` has `q` elements. -/
  card_X : Fintype.card X = q
  /-- `Y` has `q` elements. -/
  card_Y : Fintype.card Y = q

attribute [instance] ThreeDMInstance.fW ThreeDMInstance.fX ThreeDMInstance.fY
  ThreeDMInstance.dW ThreeDMInstance.dX ThreeDMInstance.dY

namespace ThreeDMInstance

/-- The ground type `W ⊕ X ⊕ Y` of the instance. -/
abbrev Ground (D : ThreeDMInstance) : Type := ThreeDMGround D.W D.X D.Y

/-- A sub-family `N ⊆ M` is a **perfect matching** when it covers every ground element
exactly once: each `e : W ⊕ X ⊕ Y` lies in the ground subset of a *unique* triple of `N`.
(Equivalently each part element is matched exactly once.) -/
def IsMatching (D : ThreeDMInstance) (N : Finset (D.W × D.X × D.Y)) : Prop :=
  N ⊆ D.M ∧ ∀ e : D.Ground, ∃! t : D.W × D.X × D.Y, t ∈ N ∧ e ∈ tripleGround t

/-- The **3DM decision problem**: does the instance admit a perfect matching? This is the
canonical NP-complete seed (Garey-Johnson SP1 / Karp 1972). -/
def threeDMDecision (D : ThreeDMInstance) : Prop :=
  ∃ N, D.IsMatching N

/-- The **encoding size** of a 3DM instance: the triple-family cardinality plus the three
part sizes (`|M| + 3q`), a linear measure of the instance description. -/
def size (D : ThreeDMInstance) : ℕ :=
  D.M.card + (Fintype.card D.W + Fintype.card D.X + Fintype.card D.Y)

end ThreeDMInstance

/-! ## A canonical well-formed X3C instance with **no** exact cover
The reduction map must be total: ill-formed 3DM instances (some part element in no triple,
or `q > |M|`) trivially have no perfect matching, so we send them to a fixed well-formed X3C
instance that provably has **no** exact cover, keeping the bi-implication. The witness is the
3-cyclic family `{0,1,2}, {2,3,4}, {4,5,0}` over `Fin 6` with `q = 2`: every element is
coverable (so `HasAssignment`), but the three triples pairwise intersect, so no two are
disjoint — hence no two saturated triples can partition the six elements. -/

/-- The 3-cyclic triple family over `Fin 6`: `{0,1,2}`, `{2,3,4}`, `{4,5,0}`. Pairwise
intersecting and jointly covering, so no two are disjoint. -/
def cyclicMembers : Fin 3 → Finset (Fin 6)
  | 0 => {0, 1, 2}
  | 1 => {2, 3, 4}
  | 2 => {4, 5, 0}

/-- The no-cover X3C instance: the 3-cyclic family over `Fin 6` with target `q = 2`. -/
def noCoverX3CInstance : X3CInstance (Fin 3) (Fin 6) where
  members := cyclicMembers
  q := 2
  card_members := by decide
  card_elts := by decide

/-- Every element of `Fin 6` lies in some cyclic triple, so `noCoverX3CInstance` admits an
assignment. -/
theorem noCoverX3CInstance_hasAssignment : noCoverX3CInstance.HasAssignment := by
  have h : ∀ e : Fin 6, ∃ i, e ∈ cyclicMembers i := by decide
  choose f hf using h
  exact ⟨f, hf⟩

/-- Distinct cyclic triples are never disjoint (they pairwise share an element). -/
theorem cyclicMembers_not_disjoint {i j : Fin 3} (hne : i ≠ j) :
    ¬ Disjoint (cyclicMembers i) (cyclicMembers j) := by
  revert hne; revert i j; decide

/-- **The canonical instance has no exact cover.** An exact cover would be two distinct
saturated triples; but saturated triples are disjoint while the cyclic triples pairwise
intersect — contradiction. -/
theorem noCoverX3CInstance_no_cover :
    ¬ ∃ assign C, noCoverX3CInstance.IsExactCover C assign ∧
      (∀ e, ∃ i ∈ C, e ∈ noCoverX3CInstance.members i) := by
  rintro ⟨assign, C, ⟨_, hCsub, hCcard⟩, _⟩
  -- `C` has two elements; both saturated, hence disjoint members, contradicting cyclic
  have h2 : 1 < C.card := by rw [hCcard]; decide
  obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp h2
  have hisat := noCoverX3CInstance.mem_saturated.mp (hCsub hi)
  have hjsat := noCoverX3CInstance.mem_saturated.mp (hCsub hj)
  exact cyclicMembers_not_disjoint hne
    (noCoverX3CInstance.members_disjoint_of_saturated hisat hjsat hne)

/-- The canonical instance bundled as a `WellFormedX3C`: well-formed (assignment exists,
`q = 2 ≤ 3 = |ι|`) yet has no exact cover. The total reduction sends ill-formed 3DM
instances here. -/
def noCoverWellFormedX3C : WellFormedX3C where
  ι := Fin 3
  α := Fin 6
  I := noCoverX3CInstance
  hasAssignment := noCoverX3CInstance_hasAssignment
  qle := by decide

/-- `x3cDecision` is **false** on the canonical no-cover instance. -/
theorem not_x3cDecision_noCoverWellFormedX3C : ¬ x3cDecision noCoverWellFormedX3C :=
  noCoverX3CInstance_no_cover

/-! ## The induced X3C instance of a 3DM instance
The textbook reduction: a 3DM instance `D` with triple family `M` induces the X3C instance
whose **ground set** is `D.Ground = W ⊕ X ⊕ Y`, whose **subsets** are indexed by the triples
of `M` (`ι = {t // t ∈ M}`), and where subset `⟨t, _⟩` is the 3-element ground set
`tripleGround t`. The target size is `q`. This is `D`'s X3C reading; the reduction is the
inclusion `D ↦ inducedX3C D`. -/

namespace ThreeDMInstance

variable (D : ThreeDMInstance)

/-- The **subset-index type** of the induced X3C instance: the triples of `M`. -/
abbrev MIndex : Type := {t : D.W × D.X × D.Y // t ∈ D.M}

/-- The **induced X3C instance**: ground `W ⊕ X ⊕ Y`, one 3-subset `tripleGround t` per
triple `t ∈ M`, target `q`. -/
def inducedX3C : X3CInstance D.MIndex D.Ground where
  members t := tripleGround t.val
  q := D.q
  card_members t := card_tripleGround t.val
  card_elts := by
    simp only [Ground, ThreeDMGround, Fintype.card_sum, D.card_W, D.card_X, D.card_Y]
    ring

@[simp] theorem inducedX3C_q : (D.inducedX3C).q = D.q := rfl

@[simp] theorem inducedX3C_members (t : D.MIndex) :
    (D.inducedX3C).members t = tripleGround t.val := rfl

@[simp] theorem inducedX3C_numSubsets : (D.inducedX3C).numSubsets = D.M.card := by
  rw [X3CInstance.numSubsets, Fintype.card_coe]

/-! ## The matching ⟺ cover correspondence (the genuine reduction correctness)
A perfect matching `N ⊆ M` of `D` *is* an exact 3-cover of `inducedX3C D` and conversely.
This is the combinatorial heart of `3DM ≤ₖ X3C`. -/

variable {D}

/-- **Matching → cover.** A perfect matching of `D` yields an assignment of the induced X3C
instance whose saturated subsets exhaust the ground set — so `saturatedCount = q`, i.e. an
exact 3-cover. The assignment routes each ground element to the unique matching triple
containing it. -/
theorem inducedX3C_saturatedCount_eq_q_of_isMatching
    {N : Finset (D.W × D.X × D.Y)} (hN : D.IsMatching N) :
    ∃ assign, (D.inducedX3C).IsAssignment assign ∧
      (D.inducedX3C).saturatedCount assign = D.q := by
  classical
  obtain ⟨hNM, hcov⟩ := hN
  -- `assign e` = the unique matching triple containing `e`, as a subtype element.
  let assign : D.Ground → D.MIndex := fun e =>
    ⟨(hcov e).choose, hNM (hcov e).choose_spec.1.1⟩
  -- the chosen triple contains `e` and lies in `N`
  have hmem : ∀ e, (assign e).val ∈ N ∧ e ∈ tripleGround (assign e).val :=
    fun e => (hcov e).choose_spec.1
  -- uniqueness: any triple of `N` containing `e` equals the chosen one
  have huniq : ∀ e, ∀ t, t ∈ N ∧ e ∈ tripleGround t → t = (assign e).val :=
    fun e t ht => (hcov e).choose_spec.2 t ht
  have hassign : (D.inducedX3C).IsAssignment assign := fun e => (hmem e).2
  -- every chosen subset is saturated: its three elements all route back to it
  have hsat : ∀ e, (D.inducedX3C).IsSaturated assign (assign e) := by
    intro e e' he'
    -- `e' ∈ members (assign e) = tripleGround (assign e).val`, and `(assign e).val ∈ N`
    refine Subtype.ext ?_
    exact (huniq e' (assign e).val ⟨(hmem e).1, he'⟩).symm
  refine ⟨assign, hassign, ?_⟩
  -- the saturated subsets' members cover everything, so saturatedCount = q
  have huniv : ((D.inducedX3C).saturated assign).biUnion (D.inducedX3C).members =
      Finset.univ := by
    refine Finset.eq_univ_of_forall fun e => ?_
    rw [Finset.mem_biUnion]
    exact ⟨assign e, (D.inducedX3C).mem_saturated.mpr (hsat e), (hmem e).2⟩
  have hcard : 3 * (D.inducedX3C).saturatedCount assign = 3 * D.q := by
    have h := (D.inducedX3C).card_biUnion_saturated assign
    rw [huniv, Finset.card_univ, (D.inducedX3C).card_elts, inducedX3C_q] at h
    exact h.symm
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hcard

/-- **Cover → matching.** An exact 3-cover of `inducedX3C D` (a set `C` of `q` saturated
triples that covers every ground element) yields a perfect matching of `D`: take the
underlying triples of `C`. Uniqueness of the covering triple is exactly disjointness of the
saturated subsets. -/
theorem isMatching_of_inducedX3C_isExactCover
    {assign : D.Ground → D.MIndex} {C : Finset D.MIndex}
    (hcover : (D.inducedX3C).IsExactCover C assign)
    (htot : ∀ e, ∃ i ∈ C, e ∈ (D.inducedX3C).members i) :
    D.IsMatching (C.image Subtype.val) := by
  classical
  obtain ⟨_, hCsub, _⟩ := hcover
  refine ⟨?_, fun e => ?_⟩
  · -- `C.image val ⊆ M`
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact i.property
  · -- each `e` lies in a unique triple of the image
    obtain ⟨i, hiC, hei⟩ := htot e
    refine ⟨i.val, ⟨Finset.mem_image_of_mem _ hiC, hei⟩, ?_⟩
    rintro t ⟨ht, het⟩
    rw [Finset.mem_image] at ht
    obtain ⟨j, hjC, rfl⟩ := ht
    -- `i, j ∈ C ⊆ saturated`; if `i ≠ j` their members are disjoint, but `e ∈ both`
    by_contra hne
    have hij : i ≠ j := fun h => hne (by rw [h])
    have hdisj := (D.inducedX3C).members_disjoint_of_saturated
      ((D.inducedX3C).mem_saturated.mp (hCsub hiC))
      ((D.inducedX3C).mem_saturated.mp (hCsub hjC)) hij
    exact (Finset.disjoint_left.mp hdisj hei) het

/-! ## Well-formedness of the induced instance
The induced X3C instance is `WellFormedX3C` (admits an assignment, `q ≤ |ι|`) exactly when
`D` is **non-degenerate**: every ground element lies in some triple of `M`, and there are at
least `q` triples. Degenerate instances have no perfect matching (an uncovered element
cannot be matched; fewer than `q` triples cannot cover `3q` elements three at a time), so the
total reduction sends them to the canonical no-cover instance. -/

variable (D)

/-- `D` is **non-degenerate**: every ground element is covered by some triple of `M`, and
there are at least `q` triples. Exactly the condition making `inducedX3C D` well-formed. -/
def IsNonDegenerate : Prop :=
  (∀ e : D.Ground, ∃ t ∈ D.M, e ∈ tripleGround t) ∧ D.q ≤ D.M.card

instance : Decidable D.IsNonDegenerate := by unfold IsNonDegenerate; infer_instance

/-- A non-degenerate `D` admits an assignment of its induced X3C instance (route each
covered ground element to a containing triple). -/
theorem inducedX3C_hasAssignment (hD : D.IsNonDegenerate) :
    (D.inducedX3C).HasAssignment := by
  classical
  choose t ht hmem using hD.1
  exact ⟨fun e => ⟨t e, ht e⟩, fun e => hmem e⟩

/-- The induced instance of a non-degenerate `D`, bundled as `WellFormedX3C`. -/
def wellFormedInduced (hD : D.IsNonDegenerate) : WellFormedX3C where
  ι := D.MIndex
  α := D.Ground
  I := D.inducedX3C
  hasAssignment := D.inducedX3C_hasAssignment hD
  qle := by rw [inducedX3C_numSubsets]; exact hD.2

variable {D}

/-- For a non-degenerate `D`, `x3cDecision (wellFormedInduced D)` is exactly the cover
statement of the induced X3C instance. -/
@[simp] theorem x3cDecision_wellFormedInduced (hD : D.IsNonDegenerate) :
    x3cDecision (D.wellFormedInduced hD) ↔
      ∃ assign C, (D.inducedX3C).IsExactCover C assign ∧
        (∀ e, ∃ i ∈ C, e ∈ (D.inducedX3C).members i) :=
  Iff.rfl

/-! ## The bi-implication on non-degenerate instances
The genuine reduction correctness: `D` has a perfect matching iff the induced X3C instance
has an exact 3-cover. Both directions are the matching ⟺ cover correspondence. -/

/-- **The reduction correctness on non-degenerate instances**: `D` admits a perfect matching
iff `inducedX3C D` admits an exact 3-cover. -/
theorem threeDMDecision_iff_x3cDecision_wellFormedInduced (hD : D.IsNonDegenerate) :
    D.threeDMDecision ↔ x3cDecision (D.wellFormedInduced hD) := by
  rw [x3cDecision_wellFormedInduced hD]
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨assign, hassign, hcount⟩ := inducedX3C_saturatedCount_eq_q_of_isMatching hN
    exact ⟨assign, ((D.inducedX3C).saturatedCount_eq_q_iff_exists_cover hassign).mp hcount⟩
  · rintro ⟨assign, C, hcover, htot⟩
    exact ⟨_, isMatching_of_inducedX3C_isExactCover hcover htot⟩

/-! ## Degenerate instances have no perfect matching
An uncovered ground element cannot be matched, and `< q` triples cannot perfectly cover the
`3q` elements; either failure of non-degeneracy refutes `threeDMDecision`. -/

/-- A perfect matching covers every ground element, so it forces every element to lie in some
triple of `M`. -/
theorem forall_mem_tripleGround_of_isMatching {N : Finset (D.W × D.X × D.Y)}
    (hN : D.IsMatching N) (e : D.Ground) : ∃ t ∈ D.M, e ∈ tripleGround t := by
  obtain ⟨hNM, hcov⟩ := hN
  obtain ⟨t, ⟨htN, het⟩, _⟩ := hcov e
  exact ⟨t, hNM htN, het⟩

/-- A degenerate `D` (some element in no triple, or `q > |M|`) has no perfect matching. -/
theorem not_threeDMDecision_of_not_nonDegenerate (hD : ¬ D.IsNonDegenerate) :
    ¬ D.threeDMDecision := by
  rintro ⟨N, hN⟩
  apply hD
  refine ⟨fun e => forall_mem_tripleGround_of_isMatching hN e, ?_⟩
  -- a perfect matching has exactly `q` triples (it partitions `3q` ground elements), so
  -- `q ≤ |M|` since `N ⊆ M`; derive `q ≤ |M|` via the induced cover count
  obtain ⟨assign, _, hcount⟩ := inducedX3C_saturatedCount_eq_q_of_isMatching hN
  -- `saturated assign ⊆ univ = M-index`, so `q = saturatedCount ≤ |MIndex| = |M|`
  have hle : D.q ≤ D.M.card := by
    calc D.q = (D.inducedX3C).saturatedCount assign := hcount.symm
      _ = ((D.inducedX3C).saturated assign).card := rfl
      _ ≤ Fintype.card D.MIndex :=
          (Finset.card_le_card (Finset.subset_univ _)).trans (le_of_eq Finset.card_univ)
      _ = D.M.card := Fintype.card_coe _
  exact hle

end ThreeDMInstance

/-! ## The total reduction map and its Karp reduction
The reduction `D ↦ toX3C D`: a non-degenerate `D` maps to its induced X3C instance
(`wellFormedInduced`); a degenerate `D` (which has no matching) maps to the canonical
no-cover instance. Both branches keep the bi-implication `threeDMDecision D ↔ x3cDecision
(toX3C D)`, so the map is a correct many-one reduction. The output size is `D.size` in the
non-degenerate branch and the constant `9` in the degenerate branch, both bounded by the
linear-plus-constant polynomial `X + 9`. -/

open ThreeDMInstance

/-- The **total reduction map** `ThreeDMInstance → WellFormedX3C`: induced X3C instance for
non-degenerate `D`, the canonical no-cover instance otherwise. -/
noncomputable def threeDMToX3CMap (D : ThreeDMInstance) : WellFormedX3C :=
  if h : D.IsNonDegenerate then D.wellFormedInduced h else noCoverWellFormedX3C

/-- **The reduction correctness** (`3DM ≤ₖ X3C`): `D` has a perfect matching iff its image
under `threeDMToX3CMap` has an exact 3-cover. Non-degenerate `D` uses the matching ⟺ cover
correspondence; degenerate `D` has neither a matching nor (via the no-cover image) a cover. -/
theorem threeDMDecision_iff_x3cDecision_threeDMToX3CMap (D : ThreeDMInstance) :
    D.threeDMDecision ↔ x3cDecision (threeDMToX3CMap D) := by
  unfold threeDMToX3CMap
  by_cases h : D.IsNonDegenerate
  · rw [dif_pos h]
    exact threeDMDecision_iff_x3cDecision_wellFormedInduced h
  · rw [dif_neg h]
    constructor
    · intro hM; exact absurd hM (not_threeDMDecision_of_not_nonDegenerate h)
    · intro hC; exact absurd hC not_x3cDecision_noCoverWellFormedX3C

/-- The output size equals the input size on the non-degenerate branch, and is the constant
`9` on the degenerate branch — so `WellFormedX3C.size (threeDMToX3CMap D) ≤ D.size + 9`. -/
theorem size_threeDMToX3CMap_le (D : ThreeDMInstance) :
    WellFormedX3C.size (threeDMToX3CMap D) ≤ D.size + 9 := by
  unfold threeDMToX3CMap
  by_cases h : D.IsNonDegenerate
  · rw [dif_pos h]
    have : WellFormedX3C.size (D.wellFormedInduced h) = D.size := by
      simp only [WellFormedX3C.size, wellFormedInduced, ThreeDMInstance.size,
        Fintype.card_coe]
      congr 1
      show Fintype.card (D.W ⊕ D.X ⊕ D.Y) = _
      rw [Fintype.card_sum, Fintype.card_sum, Nat.add_assoc]
    rw [this]; exact Nat.le_add_right _ _
  · rw [dif_neg h]
    have : WellFormedX3C.size noCoverWellFormedX3C = 9 := by decide
    rw [this]; exact Nat.le_add_left _ _

/-- **The Karp reduction `3DM ≤ₖ X3C`**: the total map `threeDMToX3CMap`, with the matching
⟺ cover bi-implication as correctness and the linear-plus-constant size bound `X + 9` as the
honest poly-time proxy (output size = input size on non-degenerate instances, a constant
otherwise). The textbook structural inclusion of 3DM into X3C, formalized. -/
noncomputable def threeDMToX3C :
    KarpReduction ThreeDMInstance.size WellFormedX3C.size
      ThreeDMInstance.threeDMDecision x3cDecision where
  toFun := threeDMToX3CMap
  correct := threeDMDecision_iff_x3cDecision_threeDMToX3CMap
  poly := Polynomial.X + Polynomial.C 9
  size_bound D := by
    have h := size_threeDMToX3CMap_le D
    simpa using h

/-! ## NP-hardness of X3C derived from 3DM, and the relocated axiom
With `threeDMToX3C`, X3C is NP-hard *relative to* 3DM unconditionally. Citing the canonical
external fact "3DM is NP-complete" (Garey-Johnson SP1 / Karp 1972) — a *more canonical* seed
than X3C — we derive X3C's absolute NP-hardness, which in turn (via `x3cToWorstCaseBacklog`)
gives the worst-case-backlog NP-hardness. This **relocates** the cited completeness axiom one
step toward Cook–Levin; it does **not** discharge it. -/

/-- **X3C is NP-hard relative to 3DM** (unconditional): 3DM Karp-reduces to X3C. This needs
no complexity-class framework — only the reduction `threeDMToX3C`. -/
theorem isNPHardVia_threeDM_x3cDecision :
    KarpReduction.IsNPHardVia ThreeDMInstance.size WellFormedX3C.size
      ThreeDMInstance.threeDMDecision x3cDecision :=
  ⟨threeDMToX3C⟩

/-- **External fact (cited, not proved): 3-Dimensional Matching is NP-hard.** 3DM is
NP-complete (Garey & Johnson, *Computers and Intractability*, 1979, problem SP1; Karp 1972),
hence NP-hard. This is the *canonical* base seed — proving it needs the full Turing-machine /
NP framework and Cook–Levin, which Mathlib does not provide, so it is recorded as an axiom.
It **replaces** the previously-cited X3C-completeness axiom: X3C's hardness is now *derived*
(`isNPHard_x3cDecision`). The base NP-completeness fact is still cited, not proved — this
relocates the axiom one canonical step, it does not eliminate it. -/
axiom ThreeDMIsNPHard : IsNPHard ThreeDMInstance.size ThreeDMInstance.threeDMDecision

/-- **X3C is NP-hard, derived from 3DM-completeness.** Every NP problem Karp-reduces to X3C
because every NP problem reduces to 3DM (the cited `ThreeDMIsNPHard`), which Karp-reduces to
X3C (`threeDMToX3C`), and Karp reductions compose. This **derives** what was previously the
cited `X3CIsNPHard` axiom, resting it on the more canonical 3DM-completeness instead. -/
theorem isNPHard_x3cDecision : IsNPHard WellFormedX3C.size x3cDecision := by
  intro σ sizeσ P hP
  exact ⟨threeDMToX3C.comp (ThreeDMIsNPHard σ sizeσ P hP).some⟩

/-- **Worst-case-backlog decision is NP-hard, resting on 3DM-completeness** (Theorem 10.2,
with the axiom relocated to 3DM). Chains the derived `isNPHard_x3cDecision` with the existing
`x3cToWorstCaseBacklog`: every NP problem reduces to 3DM (cited) ⤳ X3C (`threeDMToX3C`) ⤳
worst-case-backlog (`x3cToWorstCaseBacklog`). The single unproved input is now 3DM's
NP-completeness — a more canonical seed than X3C. -/
theorem isNPHard_worstCaseBacklogDecision_via_threeDM :
    IsNPHard WellFormedX3C.size worstCaseBacklogDecision := by
  intro σ sizeσ P hP
  exact ⟨x3cToWorstCaseBacklog.comp (isNPHard_x3cDecision σ sizeσ P hP).some⟩

/-! ## Book restatement (`3DM ≤ₖ X3C`, axiom relocation)
The textbook Karp reduction 3-Dimensional-Matching ⤳ Exact-3-Cover: 3DM is the special case
of X3C with a tripartite ground set, so the reduction is the structural inclusion `D ↦
inducedX3C D` (with the no-cover fallback making it total), and `D` has a perfect matching
iff the induced X3C instance has an exact 3-cover. Hence X3C is NP-hard relative to 3DM
(unconditional), and — citing the canonical fact that 3DM is NP-complete (Garey-Johnson SP1)
— NP-hard absolutely, which in turn carries the worst-case-backlog NP-hardness. What is
proved is the reduction and its matching ⟺ cover correctness; what is cited is 3DM's
NP-completeness (the relocated, more canonical axiom). -/
example :
    -- the reduction is correct (matching ⟺ cover) on every 3DM instance
    (∀ D : ThreeDMInstance, D.threeDMDecision ↔ x3cDecision (threeDMToX3CMap D)) ∧
    -- X3C is NP-hard relative to 3DM (unconditional)
    KarpReduction.IsNPHardVia ThreeDMInstance.size WellFormedX3C.size
      ThreeDMInstance.threeDMDecision x3cDecision :=
  ⟨threeDMDecision_iff_x3cDecision_threeDMToX3CMap, isNPHardVia_threeDM_x3cDecision⟩

end DeepWiki
