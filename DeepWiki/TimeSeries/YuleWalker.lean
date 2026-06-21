import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! # The Yule–Walker estimator (§8.1)
The Yule–Walker estimator of the AR(p) coefficients solves the sample normal (Yule–Walker)
equations `Γ̂ₚ φ̂ = γ̂ₚ`, giving `φ̂ = Γ̂ₚ⁻¹ γ̂ₚ` (eq 8.1.6) — the sample analogue of the
population Yule–Walker equations `Γₚ φ = γₚ`, which are the §5.1 prediction equations for an
AR(p) process. -/

namespace DeepWiki.TimeSeries

open Matrix

/-- **§8.1 (eq 8.1.6)**: the **Yule–Walker estimator** `φ̂ = Γ̂⁻¹ γ̂` of the autoregressive
coefficients — the solution of the sample normal equations `Γ̂ φ̂ = γ̂`, with `Γ̂` the sample
covariance matrix and `γ̂` the sample autocovariance vector. -/
noncomputable def yuleWalkerEstimator {p : ℕ} (Γ : Matrix (Fin p) (Fin p) ℝ) (γ : Fin p → ℝ) :
    Fin p → ℝ := Γ⁻¹ *ᵥ γ

/-- The Yule–Walker estimator solves the Yule–Walker equations `Γ̂ φ̂ = γ̂` when the sample
covariance matrix `Γ̂` is non-singular. -/
theorem yuleWalkerEstimator_spec {p : ℕ} {Γ : Matrix (Fin p) (Fin p) ℝ} (hΓ : IsUnit Γ.det)
    (γ : Fin p → ℝ) : Γ *ᵥ yuleWalkerEstimator Γ γ = γ := by
  rw [yuleWalkerEstimator, mulVec_mulVec, mul_nonsing_inv Γ hΓ, one_mulVec]

/-- **§8.1 (eq 8.1.7)**: the **Yule–Walker estimate of the white-noise variance**
`σ̂² = γ̂(0) − φ̂' γ̂ₚ`, with `φ̂` the Yule–Walker estimator and `γ̂(0)` the sample variance — the
sample analogue of the population variance equation `σ² = γ(0) − φ' γₚ` (eq 8.1.5). -/
noncomputable def yuleWalkerVariance {p : ℕ} (Γ : Matrix (Fin p) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γ0 : ℝ) : ℝ := γ0 - yuleWalkerEstimator Γ γ ⬝ᵥ γ

/-- The Yule–Walker variance estimate as the quadratic form `σ̂² = γ̂(0) − γ̂' Γ̂⁻¹ γ̂`. -/
theorem yuleWalkerVariance_eq {p : ℕ} (Γ : Matrix (Fin p) (Fin p) ℝ) (γ : Fin p → ℝ) (γ0 : ℝ) :
    yuleWalkerVariance Γ γ γ0 = γ0 - γ ⬝ᵥ (Γ⁻¹ *ᵥ γ) := by
  rw [yuleWalkerVariance, yuleWalkerEstimator, dotProduct_comm]

end DeepWiki.TimeSeries
