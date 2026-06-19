import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

/-! # Fractional differencing coefficients (§13.2)
The coefficients of the fractional difference operator `(1 − B)^d = ∑_{j≥0} binom(d,j)(−1)ʲ Bʲ`
whose application defines the long-memory ARIMA(0,d,0) (fractionally integrated) process. -/

namespace DeepWiki.TimeSeries

/-- **§13.2 (eq 13.2.3)**: the `j`-th coefficient `binom(d,j)·(−1)ʲ` of the fractional difference
operator `(1 − B)^d` (the generalized binomial coefficient `Ring.choose d j` times `(−1)ʲ`), whose
powers of the backshift `B` define the long-memory ARIMA(0,d,0) process. -/
noncomputable def fracDiffCoeff (d : ℝ) (j : ℕ) : ℝ := Ring.choose d j * (-1) ^ j

/-- The order-`0` fractional-difference coefficient is `1`. -/
@[simp] theorem fracDiffCoeff_zero (d : ℝ) : fracDiffCoeff d 0 = 1 := by
  simp [fracDiffCoeff]

/-- The order-`1` fractional-difference coefficient is `−d`, so `(1 − B)^d` begins `1 − d·B + ⋯`. -/
@[simp] theorem fracDiffCoeff_one (d : ℝ) : fracDiffCoeff d 1 = -d := by
  simp [fracDiffCoeff]

/-- At differencing order `d = 0` the operator `(1 − B)^0` is the identity — the coefficient
sequence is the unit `[j = 0]` (`1` at `j = 0`, else `0`), i.e. no differencing. -/
theorem fracDiffCoeff_d_zero (j : ℕ) : fracDiffCoeff 0 j = if j = 0 then 1 else 0 := by
  cases j with
  | zero => simp
  | succ n => simp [fracDiffCoeff]

end DeepWiki.TimeSeries
