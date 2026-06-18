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

end DeepWiki.ReactiveSystems
