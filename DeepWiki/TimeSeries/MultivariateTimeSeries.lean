import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # Multivariate time series: the covariance matrix function (§11.1)
The matrix-valued autocovariance `Γ(h) = [Cov(X_{h,i}, X_{0,j})]ᵢⱼ` of a stationary `d`-variate
process (eq 11.1.5) — the matrix analogue of the univariate `acvf`/`acvfStat`. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}

/-- **§11.1 (eq 11.1.5)**: the **covariance matrix function** `Γ(h) = [γᵢⱼ(h)]` of a stationary
`d`-variate process `X : ℤ → Ω → (Fin d → ℝ)`, with entries the component cross-covariances
`γᵢⱼ(h) = Cov(X_{h,i}, X_{0,j})` — the matrix-valued analogue of the univariate `acvfStat`. -/
noncomputable def mvACVF (X : ℤ → Ω → Fin d → ℝ) (μ : Measure Ω) (h : ℤ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => cov[fun ω => X h ω i, fun ω => X 0 ω j; μ]

@[simp] theorem mvACVF_apply (X : ℤ → Ω → Fin d → ℝ) (μ : Measure Ω) (h : ℤ) (i j : Fin d) :
    mvACVF X μ h i j = cov[fun ω => X h ω i, fun ω => X 0 ω j; μ] := rfl

/-- The diagonal entries of the covariance matrix function are the univariate autocovariances of
the component series: `γᵢᵢ(h) = γ_{Xⁱ}(h, 0)` for the `i`-th component process `Xⁱ`. -/
theorem mvACVF_diag (X : ℤ → Ω → Fin d → ℝ) (μ : Measure Ω) (h : ℤ) (i : Fin d) :
    mvACVF X μ h i i = acvf (fun t ω => X t ω i) μ h 0 := rfl

/-- The contemporaneous covariance matrix `Γ(0) = Cov(X₀)` is symmetric: `γᵢⱼ(0) = γⱼᵢ(0)`. -/
theorem mvACVF_zero_isSymm (X : ℤ → Ω → Fin d → ℝ) (μ : Measure Ω) :
    (mvACVF X μ 0).IsSymm := by
  show (mvACVF X μ 0)ᵀ = mvACVF X μ 0
  ext i j
  simp only [Matrix.transpose_apply, mvACVF_apply]
  exact covariance_comm _ _

end DeepWiki.TimeSeries
