import DeepWiki.TimeSeries.CausalPolyDisk
import DeepWiki.TimeSeries.SpectralDensity
import DeepWiki.TimeSeries.SpectralDensityFourier

/-! # §4.4 — The rational spectral density of an ARMA process (Theorem 4.4.2)

The frequency response `ψ̂(z) = ∑ₙ ψₙ zⁿ` of a causal `ARMA(p,q)` filter (`ψ = θ/φ` weights)
equals `θ(z)/φ(z)` on the closed unit disk — the evaluated form of `φ·ψ = θ` (a Cauchy product,
`aeval_mul_tsum_psi`). This is the bridge from the autocovariance's Fourier series
(`fourier_tsum_mul_shift_eq_normSq`) to the rational spectral density `(σ²/2π)|θ/φ|²`
(`armaSpectralDensity`). -/

namespace DeepWiki.TimeSeries

open Polynomial PowerSeries

/-- A causal `φ` has a nonzero constant term: `φ(0) ≠ 0`, since `aeval 0 φ ≠ 0`. -/
theorem IsCausalPoly.constantCoeff_coe_ne_zero {φ : ℝ[X]} (hφ : IsCausalPoly φ) :
    constantCoeff (φ : PowerSeries ℝ) ≠ 0 := by
  rw [Polynomial.constantCoeff_coe]
  have h := hφ 0 (by simp)
  rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero] at h
  simpa using h

/-- **ARMA transfer relation (frequency response):** for a causal `φ`, the `ψ = θ/φ` weight series
`ψ̂(z) = ∑ₙ ψₙ zⁿ` satisfies `φ(z)·ψ̂(z) = θ(z)` on the closed unit disk `‖z‖ ≤ 1` — the evaluated
form of `ψ = θ/φ`. Instance of `aeval_mul_tsum_psi` with the `armaPsi` weights. -/
theorem aeval_mul_tsum_armaPsi {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Polynomial.aeval z φ * (∑' n : ℕ, ((PowerSeries.coeff n (armaPsi φ θ) : ℝ) : ℂ) * z ^ n)
      = Polynomial.aeval z θ :=
  aeval_mul_tsum_psi (φ := φ) (θ := θ) (ψ := fun n => PowerSeries.coeff n (armaPsi φ θ))
    (summable_abs_armaPsi_coeff hφ)
    (armaPsi_coeff_recursion_antidiagonal hφ.constantCoeff_coe_ne_zero) hz

/-- **ARMA transfer function `= θ/φ`:** for a causal `φ`, the `ψ`-weight series evaluates to the
ratio `ψ̂(z) = θ(z)/φ(z)` on the closed unit disk (where `φ(z) ≠ 0`). -/
theorem tsum_armaPsi_mul_pow_eq_div {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∑' n : ℕ, ((PowerSeries.coeff n (armaPsi φ θ) : ℝ) : ℂ) * z ^ n)
      = Polynomial.aeval z θ / Polynomial.aeval z φ := by
  rw [eq_div_iff (hφ z hz), mul_comm]
  exact aeval_mul_tsum_armaPsi hφ hz

end DeepWiki.TimeSeries
