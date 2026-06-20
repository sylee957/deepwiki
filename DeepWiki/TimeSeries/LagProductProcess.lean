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

/-- **Problem 1.7(f)**: the autocovariance vanishes when the index pairs are disjoint, i.e.
`{i, i−1} ∩ {j, j−1} = ∅` — then `Xᵢ = Zᵢ Zᵢ₋₁` and `Xⱼ = Zⱼ Zⱼ₋₁` are independent, so `γ = 0`.
This covers all lags `|i − j| ≥ 2`. -/
theorem lagProductProcess_cov_of_disjoint [IsProbabilityMeasure μ] (hindep : iIndepFun Z μ)
    (hmem : ∀ t, MemLp (Z t) 4 μ) {i j : ℤ}
    (h1 : i ≠ j) (h2 : i ≠ j - 1) (h3 : i - 1 ≠ j) :
    cov[lagProductProcess Z i, lagProductProcess Z j; μ] = 0 := by
  have haem : ∀ t, AEMeasurable (Z t) μ := fun t => (hmem t).aestronglyMeasurable.aemeasurable
  have hpp := hindep.indepFun_prodMk_prodMk₀ haem i (i - 1) j (j - 1) h1 h2 h3 (by omega)
  have hXY : IndepFun (lagProductProcess Z i) (lagProductProcess Z j) μ :=
    hpp.comp (measurable_fst.mul measurable_snd) (measurable_fst.mul measurable_snd)
  exact hXY.covariance_eq_zero (memLp_lagProductProcess hmem i) (memLp_lagProductProcess hmem j)

/-- **Problem 1.7(f)**: the lag-`1` autocovariance vanishes, `γ(1) = 0`. Although `X_{s+1}` and `Xₛ`
share the factor `Zₛ`, the product `X_{s+1} Xₛ = Z_{s+1} · (Zₛ² Zₛ₋₁)` still has the lone factor
`Z_{s+1}` (independent of `Zₛ, Zₛ₋₁`, mean `0`), so `E[X_{s+1} Xₛ] = E[Z_{s+1}] · E[Zₛ² Zₛ₋₁] = 0`. -/
theorem lagProductProcess_cov_succ [IsProbabilityMeasure μ] (hindep : iIndepFun Z μ)
    (hmem : ∀ t, MemLp (Z t) 4 μ) (hmean : ∀ t, ∫ ω, Z t ω ∂μ = 0) (s : ℤ) :
    cov[lagProductProcess Z (s + 1), lagProductProcess Z s; μ] = 0 := by
  have haem : ∀ t, AEMeasurable (Z t) μ := fun t => (hmem t).aestronglyMeasurable.aemeasurable
  have hg : Measurable (fun p : ℝ × ℝ => p.1 * p.1 * p.2) :=
    (measurable_fst.mul measurable_fst).mul measurable_snd
  have hind := (hindep.indepFun_prodMk₀ haem s (s - 1) (s + 1) (by omega) (by omega)).comp
    hg (measurable_id : Measurable (id : ℝ → ℝ))
  have haesmB : AEStronglyMeasurable (fun ω => Z s ω * Z s ω * Z (s - 1) ω) μ :=
    ((hmem s).aestronglyMeasurable.mul (hmem s).aestronglyMeasurable).mul
      (hmem (s - 1)).aestronglyMeasurable
  rw [covariance_eq_sub (memLp_lagProductProcess hmem (s + 1)) (memLp_lagProductProcess hmem s),
    lagProductProcess_mean hindep hmem hmean (s + 1), zero_mul, sub_zero]
  calc ∫ ω, (lagProductProcess Z (s + 1) * lagProductProcess Z s) ω ∂μ
      = ∫ ω, (Z s ω * Z s ω * Z (s - 1) ω) * Z (s + 1) ω ∂μ :=
        integral_congr_ae (.of_forall fun ω => by
          simp only [lagProductProcess, Pi.mul_apply, show (s : ℤ) + 1 - 1 = s from by omega]; ring)
    _ = (∫ ω, Z s ω * Z s ω * Z (s - 1) ω ∂μ) * (∫ ω, Z (s + 1) ω ∂μ) :=
        hind.integral_mul_eq_mul_integral haesmB (hmem (s + 1)).aestronglyMeasurable
    _ = 0 := by rw [hmean (s + 1), mul_zero]

/-- **Problem 1.7(f)**: the full white autocovariance `Cov(Xᵢ, Xⱼ) = σ⁴ · [i = j]` — assembling
the lag-`0` (`= σ⁴`), lag-`±1` (`= 0`), and `|i − j| ≥ 2` (`= 0`) cases. -/
theorem lagProductProcess_cov [IsProbabilityMeasure μ] (hindep : iIndepFun Z μ)
    (hmem : ∀ t, MemLp (Z t) 4 μ) (hmean : ∀ t, ∫ ω, Z t ω ∂μ = 0)
    (hvar : ∀ t, ∫ ω, (Z t ω) ^ 2 ∂μ = σ2) (i j : ℤ) :
    cov[lagProductProcess Z i, lagProductProcess Z j; μ] = if i = j then σ2 ^ 2 else 0 := by
  rcases eq_or_ne i j with rfl | hne
  · rw [if_pos rfl]; exact lagProductProcess_acvf_zero hindep hmem hmean hvar i
  rw [if_neg hne]
  rcases eq_or_ne i (j + 1) with rfl | h1
  · exact lagProductProcess_cov_succ hindep hmem hmean j
  rcases eq_or_ne j (i + 1) with rfl | h2
  · rw [covariance_comm]; exact lagProductProcess_cov_succ hindep hmem hmean i
  exact lagProductProcess_cov_of_disjoint hindep hmem hne (by omega) (by omega)

/-- **Problem 1.7(f)**: `Xₜ = Zₜ Zₜ₋₁` is **weakly stationary** — it is white noise (mean `0`,
autocovariance `σ⁴` at lag `0` and `0` elsewhere). -/
theorem lagProductProcess_isWeaklyStationary [IsProbabilityMeasure μ] (hindep : iIndepFun Z μ)
    (hmem : ∀ t, MemLp (Z t) 4 μ) (hmean : ∀ t, ∫ ω, Z t ω ∂μ = 0)
    (hvar : ∀ t, ∫ ω, (Z t ω) ^ 2 ∂μ = σ2) :
    IsWeaklyStationary (lagProductProcess Z) μ :=
  isWeaklyStationary_of_whiteCov (v := σ2 ^ 2) (fun t => memLp_lagProductProcess hmem t)
    (fun s t => by
      simp only [mean]
      rw [lagProductProcess_mean hindep hmem hmean s, lagProductProcess_mean hindep hmem hmean t])
    (fun i j => lagProductProcess_cov hindep hmem hmean hvar i j)

/-- **Problem 1.7(f)**: the autocovariance function `γ(h) = σ⁴ · [h = 0]` of `Xₜ = Zₜ Zₜ₋₁`. -/
theorem lagProductProcess_acvfStat [IsProbabilityMeasure μ] (hindep : iIndepFun Z μ)
    (hmem : ∀ t, MemLp (Z t) 4 μ) (hmean : ∀ t, ∫ ω, Z t ω ∂μ = 0)
    (hvar : ∀ t, ∫ ω, (Z t ω) ^ 2 ∂μ = σ2) (h : ℤ) :
    acvfStat (lagProductProcess Z) μ h = if h = 0 then σ2 ^ 2 else 0 := by
  rw [acvfStat_apply, lagProductProcess_cov hindep hmem hmean hvar h 0]

end DeepWiki.TimeSeries
