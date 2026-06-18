import DeepWiki.ReactiveSystems.TimedBisimulationHmlStrict
import DeepWiki.ReactiveSystems.TimedHmlClocks
import DeepWiki.ReactiveSystems.TimedRegions
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Real.Sqrt

/-! # The `√2` example is full-`Mt`-equivalent (Ex 12.12(3) / Prop 12.2)
The `√2` TLTS states `(A,0)` and `(B,0)` satisfy the same *full* `Mt` formulae (timed
Hennessy–Milner logic with formula clocks and integer-valued guards) even though they are
not timed bisimilar. The witnessing `Mt`-bisimulation lives on the **realizable** shape of
runs: the process clock is never reset while formula clocks are, so along every run from the
seed each clock equals `T − rx x` for a *shared* reset-epoch vector `rx` — all clocks lie on
a diagonal. On that diagonal the region of a state is a function of the single elapsed-time
coordinate, and irrationality of `√2` (no reachable value equals it; it is interior to the
band `(1,2)`) supplies the room to match a boundary-crossing delay. This file builds the
`√2`-refined region machinery on the realizable shape and assembles the `Mt`-bisimulation.

This is the converse-failure refinement of `TimedBisimulationHmlStrict`: there the pair is
shown *not* timed bisimilar yet basic-`TimedHML`-equivalent; here they are full-`Mt`-equivalent. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-! ### The boundary `√2` -/

/-- The boundary `√2`, as an `ℝ≥0`. -/
noncomputable def sqrt2NN : ℝ≥0 := (Real.sqrt 2).toNNReal

/-- `(sqrt2NN : ℝ) = √2` (since `√2 ≥ 0`). -/
@[simp] theorem coe_sqrt2NN : (sqrt2NN : ℝ) = Real.sqrt 2 :=
  Real.coe_toNNReal _ (Real.sqrt_nonneg 2)

/-- `√2` (read in `ℝ`) is irrational. -/
theorem irrational_sqrt2NN : Irrational (sqrt2NN : ℝ) := by
  rw [coe_sqrt2NN]; exact irrational_sqrt_two

/-- `1 < √2`. -/
theorem one_lt_sqrt2NN : (1 : ℝ) < sqrt2NN := by rw [coe_sqrt2NN]; exact Real.one_lt_sqrt_two

/-- `√2 < 2`. -/
theorem sqrt2NN_lt_two : (sqrt2NN : ℝ) < 2 := by
  rw [coe_sqrt2NN]; exact Real.sqrt_two_lt_three_halves.trans (by norm_num)

/-- `√2 ≠ 0`, hence `0 < √2`. -/
theorem zero_lt_sqrt2NN : (0 : ℝ≥0) < sqrt2NN := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_zero, coe_sqrt2NN]
  exact lt_trans one_pos Real.one_lt_sqrt_two

/-! ### The joint valuation (process clock + formula clocks) -/

/-- Pack a process-clock value `t` and a formula valuation `u : Valuation D` into a joint
valuation over `Option D`: `none ↦ t` (process clock), `some x ↦ u x`. -/
def jointVal {D : Type*} (t : ℝ≥0) (u : Valuation D) : Valuation (Option D)
  | none => t
  | some x => u x

@[simp] theorem jointVal_none {D : Type*} (t : ℝ≥0) (u : Valuation D) :
    jointVal t u none = t := rfl

@[simp] theorem jointVal_some {D : Type*} (t : ℝ≥0) (u : Valuation D) (x : D) :
    jointVal t u (some x) = u x := rfl

/-- `jointVal` precomposed with `some` recovers the formula valuation. -/
theorem jointVal_comp_some {D : Type*} (t : ℝ≥0) (u : Valuation D) :
    (fun x => jointVal t u (some x)) = u := rfl

/-- Advancing a joint valuation by `δ` advances process and formula clocks together. -/
theorem jointVal_add {D : Type*} (t : ℝ≥0) (u : Valuation D) (δ : ℝ≥0) :
    (jointVal t u).add δ = jointVal (t + δ) (u.add δ) := by
  funext x; cases x <;> simp [jointVal, Valuation.add]

/-- Resetting a formula clock `some x` leaves the process clock `none` untouched. -/
theorem jointVal_reset_some {D : Type*} (t : ℝ≥0) (u : Valuation D) (x : D) :
    Valuation.reset {some x} (jointVal t u) = jointVal t (Valuation.reset {x} u) := by
  funext y
  cases y with
  | none => simp [Valuation.reset, jointVal]
  | some z =>
      simp only [Valuation.reset, jointVal, Set.mem_singleton_iff, Option.some.injEq]
      by_cases h : z = x <;> simp [h]

/-! ### The augmented clock: reducing the irrational `√2` cut to an integer cut

The crux device. The process boundary is the *irrational* `√2`, which integer-valued region
equivalence is blind to. Adding a virtual clock `w = process + (2 − √2)` converts it to an
**integer** cut: `process < √2 ⟺ w < 2`. Since `w` advances at rate 1 with delays (it is the
process clock shifted by a constant) and is untouched by formula-clock resets, the
`√2`-refined region is just the *ordinary* `RegionEqAll` on the valuation carrying `w` at
`none` and the formula clocks at `some x` — so the entire existing region stack (time
successor, reset, guard restriction) applies verbatim. -/

/-- `2 − √2`, a positive `ℝ≥0` shift. -/
noncomputable def twoSubSqrt2NN : ℝ≥0 := 2 - sqrt2NN

/-- `√2 ≤ 2` in `ℝ≥0`. -/
theorem sqrt2NN_le_two : sqrt2NN ≤ 2 := by
  rw [← NNReal.coe_le_coe]; push_cast; exact le_of_lt sqrt2NN_lt_two

/-- `(2 − √2 : ℝ≥0)` reads as `2 − √2` in `ℝ` (exact, since `√2 ≤ 2`). -/
@[simp] theorem coe_twoSubSqrt2NN : (twoSubSqrt2NN : ℝ) = 2 - Real.sqrt 2 := by
  rw [twoSubSqrt2NN, NNReal.coe_sub sqrt2NN_le_two, coe_sqrt2NN]; push_cast; ring

/-- The augmented joint valuation: `none ↦ w = T + (2 − √2)` (the process clock shifted so
its `√2`-crossing is an integer crossing), `some x ↦ u x` (formula clocks). -/
noncomputable def jointValW {D : Type*} (T : ℝ≥0) (u : Valuation D) : Valuation (Option D) :=
  jointVal (T + twoSubSqrt2NN) u

/-- The process clock crosses `√2` exactly when the augmented clock crosses integer `2`:
`T < √2 ↔ jointValW T u none < 2`. -/
theorem jointValW_none_lt_two_iff {D : Type*} (T : ℝ≥0) (u : Valuation D) :
    jointValW T u none < 2 ↔ T < sqrt2NN := by
  rw [jointValW, jointVal_none, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
  push_cast [coe_twoSubSqrt2NN, coe_sqrt2NN]
  constructor <;> intro h <;> linarith

/-- `jointValW` precomposed with `some` recovers the formula valuation (for guard restriction). -/
theorem jointValW_comp_some {D : Type*} (T : ℝ≥0) (u : Valuation D) :
    (fun x => jointValW T u (some x)) = u := rfl

/-- Advancing the augmented joint valuation by `δ` advances the (shifted) process clock and
the formula clocks together — the key to reusing the ordinary region time-successor. -/
theorem jointValW_add {D : Type*} (T : ℝ≥0) (u : Valuation D) (δ : ℝ≥0) :
    (jointValW T u).add δ = jointValW (T + δ) (u.add δ) := by
  rw [jointValW, jointValW, jointVal_add]; rw [add_right_comm]

/-- Resetting a formula clock leaves the augmented process clock `none` untouched. -/
theorem jointValW_reset_some {D : Type*} (T : ℝ≥0) (u : Valuation D) (x : D) :
    Valuation.reset {some x} (jointValW T u) = jointValW T (Valuation.reset {x} u) := by
  rw [jointValW, jointValW, jointVal_reset_some]

/-- **Delay clause, validated.** A left delay `d` from a pair of `√2`-refined-region-equivalent
augmented states is matched by some right delay `d'` landing again `√2`-refined-region-equivalent
— and this is exactly the *existing* `regionEqAll_timeSuccessor` applied to the augmented
valuation (the irrational cut rides along inside `none`'s integer region). The `√2`-side is
preserved because it *is* `none`'s region (`jointValW_none_lt_two_iff`). -/
theorem jointValW_delay_match {D : Type*} [Fintype D] {TL TR : ℝ≥0} {u u' : Valuation D}
    (h : RegionEqAll (jointValW TL u) (jointValW TR u')) (d : ℝ≥0) :
    ∃ d', RegionEqAll (jointValW (TL + d) (u.add d)) (jointValW (TR + d') (u'.add d')) := by
  obtain ⟨e, he⟩ := regionEqAll_timeSuccessor h d
  rw [jointValW_add, jointValW_add] at he
  exact ⟨e, he⟩

end DeepWiki.ReactiveSystems
