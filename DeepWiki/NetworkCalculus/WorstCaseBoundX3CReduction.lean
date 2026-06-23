import DeepWiki.NetworkCalculus.ServersResidual

/-! # The X3C reduction core for worst-case-bound NP-hardness (DNC Theorem 10.2)
Theorem 10.2 states that, in a feed-forward network under arbitrary
multiplexing, computing the exact maximum backlog (or maximum delay) is
NP-hard. The proof reduces **exact cover by 3-sets (X3C)**: given `3q`
elements and a collection of 3-element subsets, decide whether `q` of the
subsets partition the elements.

The reduction builds a three-stage network whose worst-case middle-stage
backlog growth, after optimizing the rate-sharing `r_{i,j}` over the feasible
polytope, equals (up to additive constants) the integer optimum

`max_assignment  Σ_i [ Σ_{j ∈ uᵢ} r_{i,j} − 2 ]⁺`,

attained at the integral extremal vertices `r_{i,j} ∈ {0,1}` with
`Σ_{i ∋ j} r_{i,j} = 1` — i.e. each element is "routed" to exactly one
containing subset. A subset `i` then contributes `1` iff *all three* of its
elements route to it (it is **saturated**); the optimum counts saturated
subsets, is `≤ q`, and equals `q` **iff** an exact 3-cover exists. The full
NP-hardness needs a complexity-reduction framework that Mathlib does not
provide, so what is formalized here is the combinatorial heart of the
reduction — the construction's correctness as a bi-implication
(`saturatedCount_eq_q_iff_exists_cover`) and the optimum bound
(`saturatedCount_le_q`). The network/complexity layer is recorded as
`[research]`/`[external]` in the catalog. -/

namespace DeepWiki

open Finset

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

/-- An **X3C instance**: a finite family of subsets `ι` of a finite element
type `α`, given by their member sets `members`, where every subset has
exactly three elements and there are `3 * q` elements. This is the input the
network reduction is built from. -/
structure X3CInstance (ι α : Type*) [Fintype ι] [Fintype α] [DecidableEq α] where
  /-- `members i`: the three elements of subset `i`. -/
  members : ι → Finset α
  /-- `q`: the target cover size; there are `3 * q` elements. -/
  q : ℕ
  /-- Each subset has exactly three elements. -/
  card_members : ∀ i, (members i).card = 3
  /-- There are `3 * q` elements in all. -/
  card_elts : Fintype.card α = 3 * q

/-! ## Assignments and saturated subsets
The integral extremal vertices of the reduction's polytope are exactly the
assignments routing each element to one containing subset; a subset is
saturated when all three of its elements route to it. -/

/-- A **valid assignment** routes each element `e` to a subset `assign e`
containing it — an integral extremal vertex of the feasible rate polytope. -/
def X3CInstance.IsAssignment (I : X3CInstance ι α) (assign : α → ι) : Prop :=
  ∀ e, e ∈ I.members (assign e)

/-- A subset `i` is **saturated** by `assign` when *every* element of `i`
routes to `i` (so `i` contributes `[3 − 2]⁺ = 1` to the objective). -/
def X3CInstance.IsSaturated (I : X3CInstance ι α) (assign : α → ι) (i : ι) : Prop :=
  ∀ e ∈ I.members i, assign e = i

instance (I : X3CInstance ι α) (assign : α → ι) (i : ι) :
    Decidable (I.IsSaturated assign i) := by
  unfold X3CInstance.IsSaturated; infer_instance

/-- The set of subsets saturated by `assign`. -/
def X3CInstance.saturated (I : X3CInstance ι α) (assign : α → ι) : Finset ι :=
  Finset.univ.filter (fun i => I.IsSaturated assign i)

/-- The objective value `Σ_i [Σ_{j∈uᵢ} r_{i,j} − 2]⁺` at the assignment: the
number of saturated subsets. -/
def X3CInstance.saturatedCount (I : X3CInstance ι α) (assign : α → ι) : ℕ :=
  (I.saturated assign).card

/-- `i ∈ saturated assign ↔ IsSaturated assign i`. -/
theorem X3CInstance.mem_saturated (I : X3CInstance ι α) {assign : α → ι} {i : ι} :
    i ∈ I.saturated assign ↔ I.IsSaturated assign i := by
  simp [X3CInstance.saturated]

/-! ## The members of saturated subsets are pairwise disjoint
Each element routes to *one* subset, so two saturated subsets cannot share a
member — the structural fact that makes the saturated count bound the cover
size. -/

omit [DecidableEq ι] in
/-- Distinct saturated subsets have disjoint member sets: a shared element
would route to both. -/
theorem X3CInstance.members_disjoint_of_saturated (I : X3CInstance ι α)
    {assign : α → ι} {i i' : ι} (hi : I.IsSaturated assign i)
    (hi' : I.IsSaturated assign i') (hne : i ≠ i') :
    Disjoint (I.members i) (I.members i') := by
  rw [Finset.disjoint_left]
  intro e he he'
  exact hne ((hi e he).symm.trans (hi' e he'))

/-- The union of the members of the saturated subsets is a *disjoint* union,
so its cardinality is `3 ·` (number of saturated subsets). -/
theorem X3CInstance.card_biUnion_saturated (I : X3CInstance ι α)
    (assign : α → ι) :
    ((I.saturated assign).biUnion I.members).card = 3 * I.saturatedCount assign := by
  rw [Finset.card_biUnion, X3CInstance.saturatedCount]
  · rw [Finset.sum_congr rfl (fun i _ => I.card_members i), Finset.sum_const,
      smul_eq_mul, Nat.mul_comm]
  · intro i hi i' hi' hne
    exact I.members_disjoint_of_saturated
      (I.mem_saturated.mp hi) (I.mem_saturated.mp hi') hne

/-! ## The optimum is bounded by `q`, with equality iff an exact cover exists -/

/-- **The objective is bounded by `q`**: `3 ·` the saturated count is at most
the total element count `3q`, since the saturated members are disjoint. -/
theorem X3CInstance.saturatedCount_le_q (I : X3CInstance ι α) (assign : α → ι) :
    I.saturatedCount assign ≤ I.q := by
  have h : 3 * I.saturatedCount assign ≤ 3 * I.q := by
    calc 3 * I.saturatedCount assign
        = ((I.saturated assign).biUnion I.members).card :=
          (I.card_biUnion_saturated assign).symm
      _ ≤ Fintype.card α := by
          rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
      _ = 3 * I.q := I.card_elts
  exact Nat.le_of_mul_le_mul_left h (by norm_num)

/-- An **exact 3-cover**: a family `C` of subsets, each saturated by `assign`
(self-contained), with `C.card = q` — the form produced by the reduction
from a valid assignment attaining the optimum. -/
def X3CInstance.IsExactCover (I : X3CInstance ι α) (C : Finset ι) (assign : α → ι) : Prop :=
  I.IsAssignment assign ∧ C ⊆ I.saturated assign ∧ C.card = I.q

/-- **The construction's correctness (the X3C correspondence)**: a valid
assignment attains the optimum `q` *iff* its saturated subsets form an exact
3-cover that exhausts the element type. Equivalently: the max backlog reaches
the cover threshold exactly when an X3C cover exists. -/
theorem X3CInstance.saturatedCount_eq_q_iff_exists_cover (I : X3CInstance ι α)
    {assign : α → ι} (hassign : I.IsAssignment assign) :
    I.saturatedCount assign = I.q ↔
      ∃ C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) := by
  constructor
  · intro hq
    refine ⟨I.saturated assign, ⟨hassign, Finset.Subset.refl _, hq⟩, ?_⟩
    -- the q saturated triples are disjoint and total 3q = all elements, so cover everything
    intro e
    -- the saturated triples are disjoint and total `3q`, so their union is all of `univ`
    have hcard_eq : ((I.saturated assign).biUnion I.members).card = Fintype.card α := by
      rw [I.card_biUnion_saturated, hq, I.card_elts]
    have huniv : (I.saturated assign).biUnion I.members = Finset.univ :=
      Finset.eq_univ_of_card _ hcard_eq
    have he : e ∈ (I.saturated assign).biUnion I.members := huniv ▸ Finset.mem_univ e
    rw [Finset.mem_biUnion] at he
    obtain ⟨i, hi, hei⟩ := he
    exact ⟨i, hi, hei⟩
  · rintro ⟨C, ⟨_, hCsub, hCcard⟩, _⟩
    exact le_antisymm (I.saturatedCount_le_q assign)
      (hCcard ▸ Finset.card_le_card hCsub)

/-! ## Book restatement (Theorem 10.2, combinatorial core)
The reduction from X3C builds a network in which the maximum middle-stage
backlog, optimized over the feasible rate-sharing polytope, equals (up to
additive constants) the count of *saturated* subsets at an integral extremal
vertex — an assignment routing each of the `3q` elements to one containing
3-subset. This count is at most `q`, and reaches `q` exactly when those `q`
saturated subsets partition the elements, i.e. when an exact 3-cover exists.
Hence deciding whether the worst-case backlog reaches the cover threshold is
equivalent to X3C, and computing the exact worst-case bound is NP-hard. The
network and complexity-class wrappers are external to this combinatorial
core. -/
example (I : X3CInstance ι α) {assign : α → ι} (hassign : I.IsAssignment assign) :
    I.saturatedCount assign ≤ I.q ∧
    (I.saturatedCount assign = I.q ↔
      ∃ C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i)) :=
  ⟨I.saturatedCount_le_q assign,
   I.saturatedCount_eq_q_iff_exists_cover hassign⟩

end DeepWiki
