import DeepWiki.TimeSeries.MultivariateTimeSeries

/-! # Vector ARMA processes (§11.3)
The `d`-variate `ARMA(p, q)` recursion `Xₜ − Φ₁Xₜ₋₁ − ⋯ − ΦₚXₜ₋ₚ = Zₜ + Θ₁Zₜ₋₁ + ⋯ + Θ_qZₜ₋q`
with matrix coefficients `Φᵢ, Θⱼ` and a white-noise input `Z` (the matrix lag polynomial form
`Φ(B)Xₜ = Θ(B)Zₜ`). -/

namespace DeepWiki.TimeSeries

open Matrix

variable {Ω : Type*} {d : ℕ}

/-- **§11.3 — the vector `ARMA(p, q)` recursion**: the `d`-variate process `X` is a vector
`ARMA(p, q)` process with AR coefficient matrices `Φ`, MA coefficient matrices `Θ`, and input `Z` if
pathwise `Xₜ = ∑ᵢ Φᵢ Xₜ₋ᵢ₋₁ + Zₜ + ∑ⱼ Θⱼ Zₜ₋ⱼ₋₁` (the matrix lag polynomial identity
`Φ(B)Xₜ = Θ(B)Zₜ`). Following the arrival-curve convention, the white-noise property of `Z` and
stationarity of `X` are supplied as separate hypotheses where a theorem needs them. -/
def IsVectorARMA {p q : ℕ} (Φ : Fin p → Matrix (Fin d) (Fin d) ℝ)
    (Θ : Fin q → Matrix (Fin d) (Fin d) ℝ) (X Z : ℤ → Ω → Fin d → ℝ) : Prop :=
  ∀ t : ℤ, ∀ ω : Ω, X t ω
    = (∑ i : Fin p, Φ i *ᵥ X (t - (i : ℤ) - 1) ω) + Z t ω
      + ∑ j : Fin q, Θ j *ᵥ Z (t - (j : ℤ) - 1) ω

/-- A vector `ARMA(0, 0)` process is exactly its white-noise input: `X = Z`. -/
theorem isVectorARMA_zero {Φ : Fin 0 → Matrix (Fin d) (Fin d) ℝ}
    {Θ : Fin 0 → Matrix (Fin d) (Fin d) ℝ} {X Z : ℤ → Ω → Fin d → ℝ} :
    IsVectorARMA Φ Θ X Z ↔ ∀ t ω, X t ω = Z t ω := by
  simp [IsVectorARMA]

end DeepWiki.TimeSeries
