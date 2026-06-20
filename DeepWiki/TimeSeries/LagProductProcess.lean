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

/-- **Problem 1.7(f)**: the variance is `γ(0) = σ⁴` — by independence
`E[(Zₜ Zₜ₋₁)²] = E[Zₜ²] E[Zₜ₋₁²] = σ² · σ²`. -/
theorem lagProductProcess_acvf_zero [IsProbabilityMeasure μ] (hindep : iIndepFun Z μ)
    (hmem : ∀ t, MemLp (Z t) 4 μ)
    (hmean : ∀ t, ∫ ω, Z t ω ∂μ = 0) (hvar : ∀ t, ∫ ω, (Z t ω) ^ 2 ∂μ = σ2) (t : ℤ) :
    cov[lagProductProcess Z t, lagProductProcess Z t; μ] = σ2 ^ 2 := by
  have hne : (t : ℤ) ≠ t - 1 := by omega
  have hsq : Measurable (fun x : ℝ => x * x) := measurable_id.mul measurable_id
  have haesm : ∀ s, AEStronglyMeasurable (fun ω => Z s ω * Z s ω) μ := fun s =>
    (hmem s).aestronglyMeasurable.mul (hmem s).aestronglyMeasurable
  have e : ∀ s, (∫ ω, Z s ω * Z s ω ∂μ) = σ2 := fun s => by
    rw [show (fun ω => Z s ω * Z s ω) = (fun ω => (Z s ω) ^ 2) from by funext ω; ring]
    exact hvar s
  rw [covariance_eq_sub (memLp_lagProductProcess hmem t) (memLp_lagProductProcess hmem t),
    lagProductProcess_mean hindep hmem hmean t, mul_zero, sub_zero]
  calc ∫ ω, (lagProductProcess Z t * lagProductProcess Z t) ω ∂μ
      = ∫ ω, (Z t ω * Z t ω) * (Z (t - 1) ω * Z (t - 1) ω) ∂μ :=
        integral_congr_ae (.of_forall fun ω => by simp only [lagProductProcess, Pi.mul_apply]; ring)
    _ = (∫ ω, Z t ω * Z t ω ∂μ) * (∫ ω, Z (t - 1) ω * Z (t - 1) ω ∂μ) :=
        ((hindep.indepFun hne).comp hsq hsq).integral_mul_eq_mul_integral (haesm t) (haesm (t - 1))
    _ = σ2 ^ 2 := by rw [e t, e (t - 1)]; ring

end DeepWiki.TimeSeries
