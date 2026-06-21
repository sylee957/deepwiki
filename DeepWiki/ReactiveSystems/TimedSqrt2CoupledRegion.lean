import DeepWiki.ReactiveSystems.TimedSqrt2FullRel

/-! # The `√2` Mt-bisimulation, step 5: the coupled (single-irrational-cut) live relation (Ex 12.12(3))

`Sq2FullRel` proves five of the six `IsMtBisimulation` clauses — including the entire crossing/past
regime (`delay_cross`) — but its live regime is **insufficient**: it tracks the process-to-clock
relationship only at the *integer* level (`AsymMatch` on crossing-values), with no information on the
process's *fractional* position relative to the clocks. So the clock time-successor's `δ'` need not
place the process within reach of the τ-target, and the live-stay clause cannot close.

This file states the fix: the **single-irrational-cut region in crossing-value coordinates**. The
relation adds, to `Sq2FRel`, the symmetric fractional orderings on the *combined* valuation
`[clocks u] ∪ [crossing-values cv d u] ∪ [τ = √2 − d]`. The split is:
* **clocks** — symmetric region (`RegionEqAll u u'`), re-established by the time-successor;
* **crossing-values / τ** — *asymmetric* integer cuts (`AsymMatch`, open A / closed B), the `cv`-cuts
  being delay-**invariant** (`cv_delay_invariant`);
* **all fractional orderings** (clock–clock, clock–crossing, crossing–crossing) — **symmetric** (the
  missing coupling).

This coordinate choice is what makes the **reset** clause clean: a freshly reset clock `x` has
`cv x = 0 + (√2 − d) = τ` *exactly*, so it lands on the τ-coordinate and ties with it consistently in
both A and B — no spurious asymmetry (the apparent reset failure in `jointValW` coordinates is an
artifact: there the process clock `none = process + (2−√2)` is not the virtual-0 crossing).

The hard remaining clause is the live delay: a time-successor advancing the clocks `u` past the
*fixed* crossing-value landmarks, with the asymmetric √2-cut sitting at those landmarks. This file
nails the definition, the seed, and the structural reductions to `Sq2FullRel` (so the five proven
clauses transfer); the coupled reset/action/delay clauses follow. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-- The **combined valuation** over `D ⊕ Option D`: the formula clocks (`inl y ↦ u y`), the per-clock
crossing-values (`inr (some y) ↦ cv d u y`), and the process's own crossing-value `τ = √2 − d`
(`inr none`). Its fractional orderings are the data the coupled relation adds. -/
noncomputable def combVal {D : Type*} (d : ℝ≥0) (u : Valuation D) : D ⊕ Option D → ℝ≥0
  | Sum.inl y => u y
  | Sum.inr (some y) => cv d u y
  | Sum.inr none => sqrt2NN - d

@[simp] theorem combVal_inl {D : Type*} (d : ℝ≥0) (u : Valuation D) (y : D) :
    combVal d u (Sum.inl y) = u y := rfl

@[simp] theorem combVal_inr_some {D : Type*} (d : ℝ≥0) (u : Valuation D) (y : D) :
    combVal d u (Sum.inr (some y)) = cv d u y := rfl

@[simp] theorem combVal_inr_none {D : Type*} (d : ℝ≥0) (u : Valuation D) :
    combVal d u (Sum.inr none) = sqrt2NN - d := rfl

/-- The **coupling condition**: the symmetric fractional orderings on the combined valuation agree
between A and B. This is exactly what `Sq2FRel` lacks — it links the process's fractional position to
the clocks, so that a single delay `δ'` can match both the clock region and the τ. -/
def CombFracOrder {D : Type*} (d : ℝ≥0) (u : Valuation D) (e : ℝ≥0) (u' : Valuation D) : Prop :=
  ∀ i j : D ⊕ Option D, fracPart (combVal d u i) ≤ fracPart (combVal d u j) ↔
    fracPart (combVal e u' i) ≤ fracPart (combVal e u' j)

/-- The **coupled live relation**: `Sq2FRel` (clock region + asymmetric crossing/τ floors) together
with the symmetric combined frac-orderings — the single-irrational-cut region in crossing-value
coordinates. -/
def Sq2CoupledFRel {D : Type*} (d : ℝ≥0) (u : Valuation D) (e : ℝ≥0) (u' : Valuation D) : Prop :=
  Sq2FRel d u e u' ∧ CombFracOrder d u e u'

/-- The coupled `√2` relation: past regime (both `a`-disabled, clocks region-equivalent) or the
coupled live regime. -/
def Sq2CoupledRel {D : Type*} (p : Sq2) (u : Valuation D) (q : Sq2) (u' : Valuation D) : Prop :=
  (aDisabled sqrt2NN p ∧ aDisabled sqrt2NN q ∧ RegionEqAll u u')
  ∨ (∃ d e : ℝ≥0, p = Sq2.A d ∧ q = Sq2.B e ∧ Sq2CoupledFRel d u e u')

/-- **Forget the coupling.** Every coupled state is a `Sq2FullRel` state, so the five proven
`Sq2FullRel` clauses (guard, reset, both actions, the crossing/past delay) transfer directly. -/
theorem Sq2CoupledRel.toFullRel {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') : Sq2FullRel p u q u' := by
  rcases h with hpast | ⟨d, e, hp, hq, hfr, _⟩
  · exact Or.inl hpast
  · exact Or.inr ⟨d, e, hp, hq, hfr⟩

/-- Both regimes give region-equivalent formula clocks (for the guard clause). -/
theorem Sq2CoupledRel.regionEqAll {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') : RegionEqAll u u' :=
  h.toFullRel.regionEqAll

/-- **Guard clause** for the coupled relation. -/
theorem Sq2CoupledRel.guard {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') (g : ClockConstraint D) : satisfies u g ↔ satisfies u' g :=
  regionEqAll_satisfies h.regionEqAll g

/-- **The seed** `(A 0) ~ (B 0)` at the all-zero valuation: A and B coincide, so the coupling is
trivial and `Sq2FRel` holds as in `sq2FullRel_seed`. -/
theorem sq2CoupledRel_seed {D : Type*} :
    Sq2CoupledRel (Sq2.A 0) (fun _ : D => 0) (Sq2.B 0) (fun _ : D => 0) := by
  refine Or.inr ⟨0, 0, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact RegionEqAll.refl _
  · exact zero_lt_sqrt2NN
  · exact le_of_lt zero_lt_sqrt2NN
  · simp only [crossVal_zero, tsub_zero]; exact asymMatch_sqrt2_self
  · intro _; simp only [crossVal, tsub_zero, zero_add]; exact asymMatch_sqrt2_self
  · intro i j; exact Iff.rfl

end TLTS

end DeepWiki.ReactiveSystems
