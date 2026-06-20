import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-! # The lag-product process `Xₜ = Zₜ Zₜ₋₁` (Problem 1.7(f))
For an iid mean-zero sequence `Z` (with finite fourth moments so the products are square
integrable), the lag product `Xₜ = Zₜ Zₜ₋₁` is white noise: mean `0`, variance `σ⁴`, and
autocovariance `0` at every nonzero lag — hence weakly stationary. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℤ → Ω → ℝ} {σ2 : ℝ}

/-- **Problem 1.7(f)**: the lag-product process `Xₜ = Zₜ · Zₜ₋₁`. -/
noncomputable def lagProductProcess (Z : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ := Z t * Z (t - 1)

/-- `Xₜ = Zₜ Zₜ₋₁` is square integrable when `Z` has finite fourth moments (Hölder, `L⁴·L⁴ ⊆ L²`). -/
theorem memLp_lagProductProcess (hmem : ∀ t, MemLp (Z t) 4 μ) (t : ℤ) :
    MemLp (lagProductProcess Z t) 2 μ := by
  haveI : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul, (by norm_num : (4 : ℝ≥0∞) = 2 * 2),
      ENNReal.mul_inv (.inl two_ne_zero) (.inl ENNReal.ofNat_ne_top), ← mul_assoc,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]⟩
  exact MemLp.mul (hmem (t - 1)) (hmem t)

/-- **Problem 1.7(f)**: the lag-product process has mean `0` — by independence
`E[Zₜ Zₜ₋₁] = E[Zₜ] E[Zₜ₋₁] = 0`. -/
theorem lagProductProcess_mean (hindep : iIndepFun Z μ) (hmem : ∀ t, MemLp (Z t) 4 μ)
    (hmean : ∀ t, ∫ ω, Z t ω ∂μ = 0) (t : ℤ) :
    ∫ ω, lagProductProcess Z t ω ∂μ = 0 := by
  rw [lagProductProcess,
    (hindep.indepFun (show (t : ℤ) ≠ t - 1 by omega)).integral_mul_eq_mul_integral
      ((hmem t).aestronglyMeasurable) ((hmem (t - 1)).aestronglyMeasurable),
    hmean t, zero_mul]

end DeepWiki.TimeSeries
