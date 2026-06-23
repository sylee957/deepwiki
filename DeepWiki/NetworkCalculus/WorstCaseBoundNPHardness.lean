import DeepWiki.NetworkCalculus.KarpReduction
import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReductionNetwork

/-! # NP-hardness of worst-case backlog computation (DNC Theorem 10.2)
The combinatorial reduction (`WorstCaseBoundX3CReduction*`) proves the threshold ⟺ cover
bi-implication `(∃ exact 3-cover) ↔ (3s − 2q ≤ worstCaseBacklog I)`. This file packages it
as a **Karp reduction** (`KarpReduction`) from the Exact-3-Cover (X3C) decision problem to
the worst-case-backlog decision problem, and concludes NP-hardness of the latter *relative
to* X3C (`IsNPHardVia`). The classical external fact "X3C is NP-complete" (Garey & Johnson,
*Computers and Intractability*, 1979, problem SP2) is cited, **not** proved — proving it
needs the full Turing-machine framework Mathlib lacks.

**The reduction map is the identity on well-formed instances.** The Figure-10.7 network is
*determined* by the X3C instance `I` (its topology is `I.members`, and the worst-case
backlog and threshold `3s − 2q` are functions of `I`). So the reduction `f : I ↦ N(I)`
that a textbook describes is, at the decision-predicate level, the identity on `I`: the
source predicate is "`I` has an exact 3-cover", the target predicate is
"`3s − 2q ≤ worstCaseBacklog I`", and `reduceToDecision_correct` is exactly
`∀ I, P I ↔ Q (id I)`. The output size equals the input size, so the poly-time proxy is the
linear polynomial `X` (output size `≤ input size`).

**Honesty ledger** (every abstraction is a visible def/hypothesis, never a hidden claim):
* *Poly-time* is the structural size-bound proxy of `KarpReduction` (output size `≤
  poly(input size)`), not a TM cost model — stated in `KarpReduction`'s docstring.
* *X3C ∈ NP-complete* is the cited external `X3CIsNPHard` axiom (Garey-Johnson), not proved.
* *Network dynamics realize `worstCaseBacklog`* (rate integration; fractional-vs-integral
  vertex optimality) is the analysis layer scoped in `WorstCaseBoundX3CReductionNetwork`,
  above the served-equation arithmetic. The Karp reduction is built on the combinatorial
  `worstCaseBacklog` (the served-equation optimum), exactly as the bridge defines it. -/

namespace DeepWiki

open Finset

/-! ## The bundled well-formed X3C instance (a single `Type` for the reduction domain)
A Karp reduction is a map between two `Type`s. We bundle an X3C instance together with its
finite element/subset types, decidability, and well-formedness (`HasAssignment` and
`q ≤ numSubsets`, the hypotheses the threshold correspondence needs) into one `Type`, so
the reduction can range over the family of all well-formed instances. -/

/-- A **well-formed X3C instance**, bundled into a single `Type`: the subset type `ι` and
element type `α` with their finiteness/decidability, the instance `I`, and the
well-formedness facts `HasAssignment` (every element is coverable) and `q ≤ numSubsets`
(enough subsets) that the threshold correspondence requires. -/
structure WellFormedX3C where
  /-- The subset (index) type. -/
  ι : Type
  /-- The element type. -/
  α : Type
  /-- `ι` is finite. -/
  [fι : Fintype ι]
  /-- `α` is finite. -/
  [fα : Fintype α]
  /-- `ι` has decidable equality. -/
  [dι : DecidableEq ι]
  /-- `α` has decidable equality. -/
  [dα : DecidableEq α]
  /-- The underlying X3C instance. -/
  I : X3CInstance ι α
  /-- Every element is coverable (an assignment exists). -/
  hasAssignment : I.HasAssignment
  /-- Enough subsets to cover: `q ≤ s`. -/
  qle : I.q ≤ I.numSubsets

attribute [instance] WellFormedX3C.fι WellFormedX3C.fα WellFormedX3C.dι WellFormedX3C.dα

/-- The **encoding size** of a well-formed X3C instance: the number of subsets plus the
number of elements (`s + 3q`), a linear measure of the instance's description size. The
network the reduction outputs is the *same* instance, so this is also the output size. -/
def WellFormedX3C.size (w : WellFormedX3C) : ℕ := Fintype.card w.ι + Fintype.card w.α

/-! ## The two decision problems
* **X3C decision**: does the instance have an exact 3-cover?
* **Worst-case-backlog decision**: is the worst-case backlog at least the threshold
  `3s − 2q`? -/

/-- The **X3C (Exact-3-Cover) decision problem**: does the bundled instance admit an exact
3-cover (a set of `q` saturated subsets that, with some assignment, partition the elements)?
This is the classical NP-complete problem the reduction starts from. -/
def x3cDecision (w : WellFormedX3C) : Prop :=
  ∃ assign C, w.I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ w.I.members i)

/-- The **worst-case-backlog decision problem** (Theorem 10.2's target): is the worst-case
backlog at the bottom server `W` at least the threshold `3s − 2q`? This is the decision the
book proves NP-hard. -/
def worstCaseBacklogDecision (w : WellFormedX3C) : Prop :=
  3 * w.I.numSubsets - 2 * w.I.q ≤ w.I.worstCaseBacklog

/-! ## The reduction's correctness (the threshold ⟺ cover bi-implication)
The identity map on well-formed instances reduces X3C to worst-case-backlog decision: the
correctness is `threshold_le_worstCaseBacklog_iff_exists_cover`, which holds *because* the
instance is well-formed (the bundled `hasAssignment`/`qle`). -/

/-- **The reduction correctness** (Theorem 10.2): an instance has an exact 3-cover iff its
worst-case backlog reaches the threshold `3s − 2q`. This is the many-one bi-implication
`x3cDecision w ↔ worstCaseBacklogDecision w` over the well-formed instances — the genuine
NP-hardness content. -/
theorem x3cDecision_iff_worstCaseBacklogDecision (w : WellFormedX3C) :
    x3cDecision w ↔ worstCaseBacklogDecision w :=
  (w.I.threshold_le_worstCaseBacklog_iff_exists_cover w.hasAssignment w.qle).symm

/-! ## The Karp reduction
The identity map carries the X3C decision to the worst-case-backlog decision, with the
above bi-implication as correctness and the linear polynomial `X` as the poly-time proxy
(the output instance is the input instance, so output size = input size ≤ `X`(input
size)). -/

/-- **The Karp reduction X3C ≤ₖ worst-case-backlog decision** (Theorem 10.2): the
identity map on well-formed instances, with the threshold ⟺ cover bi-implication as
correctness and the linear size bound `X` (the Figure-10.7 network is the instance itself,
so the reduction is structural and size-preserving — the honest poly-time proxy). -/
noncomputable def x3cToWorstCaseBacklog :
    KarpReduction WellFormedX3C.size WellFormedX3C.size x3cDecision worstCaseBacklogDecision where
  toFun := _root_.id
  correct := x3cDecision_iff_worstCaseBacklogDecision
  poly := Polynomial.X
  size_bound w := by simp

/-! ## NP-hardness relative to X3C, and the absolute statement under the cited fact
With the Karp reduction in hand, worst-case-backlog decision is NP-hard *relative to* X3C
unconditionally. Citing the external fact that X3C is NP-complete (so NP-hard), we obtain
the absolute Theorem 10.2. -/

/-- **Worst-case-backlog decision is NP-hard relative to X3C** (Theorem 10.2, faithful
form): X3C Karp-reduces to it. This is *unconditional* — it needs no complexity-class
framework, only the reduction `x3cToWorstCaseBacklog`. -/
theorem isNPHardVia_x3c_worstCaseBacklogDecision :
    KarpReduction.IsNPHardVia WellFormedX3C.size WellFormedX3C.size
      x3cDecision worstCaseBacklogDecision :=
  ⟨x3cToWorstCaseBacklog⟩

/-- **External fact (cited, not proved): X3C is NP-hard.** Exact-3-Cover is NP-complete
(Garey & Johnson, *Computers and Intractability*, 1979, problem SP2 / [GAR 79]); hence
NP-hard. Proving this requires the full Turing-machine / NP framework Mathlib does not
provide, so it is recorded as an axiom — the single, clearly-marked external input to the
absolute Theorem 10.2. -/
axiom X3CIsNPHard : IsNPHard WellFormedX3C.size x3cDecision

/-- **Theorem 10.2 (absolute, under the cited X3C-completeness): computing the worst-case
backlog is NP-hard.** Every NP problem Karp-reduces to worst-case-backlog decision —
because every NP problem reduces to X3C (the cited `X3CIsNPHard`), which Karp-reduces to
worst-case-backlog decision (`x3cToWorstCaseBacklog`), and Karp reductions compose. The
*only* unproved input is the cited NP-completeness of X3C. -/
theorem isNPHard_worstCaseBacklogDecision :
    IsNPHard WellFormedX3C.size worstCaseBacklogDecision := by
  intro σ sizeσ P hP
  exact ⟨x3cToWorstCaseBacklog.comp (X3CIsNPHard σ sizeσ P hP).some⟩

/-! ## Book restatement (Theorem 10.2)
The Figure-10.7 reduction is a polynomial-time many-one (Karp) reduction from Exact-3-Cover
to the worst-case-backlog decision problem (`x3cToWorstCaseBacklog`): an instance has an
exact 3-cover iff its worst-case backlog reaches `3s − 2q`. Hence worst-case-backlog
decision is NP-hard relative to X3C (unconditional), and — citing the classical fact that
X3C is NP-complete (Garey-Johnson) — NP-hard absolutely. What is proved is the Karp
reduction and its correctness; what is cited is X3C's NP-completeness; what is scoped
(above the served-equation arithmetic, in `WorstCaseBoundX3CReductionNetwork`) is the
fluid-dynamics realization of `worstCaseBacklog`. -/
example :
    -- the reduction is correct (threshold ⟺ cover) on every well-formed instance
    (∀ w : WellFormedX3C, x3cDecision w ↔ worstCaseBacklogDecision w) ∧
    -- worst-case-backlog decision is NP-hard relative to X3C
    KarpReduction.IsNPHardVia WellFormedX3C.size WellFormedX3C.size
      x3cDecision worstCaseBacklogDecision :=
  ⟨x3cDecision_iff_worstCaseBacklogDecision, isNPHardVia_x3c_worstCaseBacklogDecision⟩

end DeepWiki
