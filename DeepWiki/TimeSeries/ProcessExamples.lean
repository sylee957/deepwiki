import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! # Worked examples of stochastic processes (§1.2–§1.3)
Realizations (Def 1.2.2) and the cosine process `Xₜ = A cos(θt) + B sin(θt)`
(Example 1.3.1): a stationary process with autocovariance `σ² cos(θh)`. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Definition 1.2.2**: a realization (sample path) of a process `X` at the
outcome `ω` is the function `t ↦ Xₜ(ω)`. -/
def realization (X : ℤ → Ω → ℝ) (ω : Ω) : ℤ → ℝ := fun t => X t ω

/-- Bilinear expansion of the covariance of two linear combinations of `A`, `B`. -/
private theorem covariance_lin_comb [IsFiniteMeasure μ] {A B : Ω → ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (c₁ d₁ c₂ d₂ : ℝ) :
    cov[c₁ • A + d₁ • B, c₂ • A + d₂ • B; μ]
      = c₁ * c₂ * cov[A, A; μ] + c₁ * d₂ * cov[A, B; μ]
        + d₁ * c₂ * cov[B, A; μ] + d₁ * d₂ * cov[B, B; μ] := by
  rw [covariance_add_left (hA.const_smul c₁) (hB.const_smul d₁)
        ((hA.const_smul c₂).add (hB.const_smul d₂)),
      covariance_add_right (hA.const_smul c₁) (hA.const_smul c₂) (hB.const_smul d₂),
      covariance_add_right (hB.const_smul d₁) (hA.const_smul c₂) (hB.const_smul d₂),
      covariance_smul_left, covariance_smul_left, covariance_smul_left, covariance_smul_left,
      covariance_smul_right, covariance_smul_right, covariance_smul_right, covariance_smul_right]
  ring

/-- **Example 1.3.1**: the cosine process `Xₜ = A cos(θt) + B sin(θt)`, with `A`, `B`
uncorrelated, mean zero, and common variance. -/
noncomputable def cosProcess (A B : Ω → ℝ) (θ : ℝ) : ℤ → Ω → ℝ :=
  fun t => Real.cos (θ * (t : ℝ)) • A + Real.sin (θ * (t : ℝ)) • B

/-- **Example 1.3.1**: the autocovariance of the cosine process is
`γ(r,s) = σ² cos(θ(r − s))` (with `σ² = Var A = Var B` and `A`, `B` uncorrelated). -/
theorem cosProcess_acvf [IsFiniteMeasure μ] {A B : Ω → ℝ} {θ σ2 : ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hVA : cov[A, A; μ] = σ2) (hVB : cov[B, B; μ] = σ2) (hAB : cov[A, B; μ] = 0)
    (r s : ℤ) :
    acvf (cosProcess A B θ) μ r s = σ2 * Real.cos (θ * ((r : ℝ) - (s : ℝ))) := by
  simp only [acvf, cosProcess]
  rw [covariance_lin_comb hA hB, hVA, hVB, hAB, covariance_comm B A, hAB, mul_sub, Real.cos_sub]
  ring

/-- **Example 1.3.1**: the cosine process is (covariance) stationary — its
autocovariance is invariant under a common time shift. -/
theorem cosProcess_acvf_shift [IsFiniteMeasure μ] {A B : Ω → ℝ} {θ σ2 : ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hVA : cov[A, A; μ] = σ2) (hVB : cov[B, B; μ] = σ2) (hAB : cov[A, B; μ] = 0)
    (r s h : ℤ) :
    acvf (cosProcess A B θ) μ r s = acvf (cosProcess A B θ) μ (r + h) (s + h) := by
  rw [cosProcess_acvf hA hB hVA hVB hAB, cosProcess_acvf hA hB hVA hVB hAB]
  congr 2
  push_cast
  ring

end DeepWiki.TimeSeries
