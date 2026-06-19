import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-! # The periodogram (§10.1)
The periodogram `Iₙ(λ) = n⁻¹ |∑ₜ xₜ e^{-itλ}|²` (eq 10.1.8) is the squared modulus of the
discrete Fourier transform of the data, normalized by the sample size — the basic
nonparametric estimator of the spectral density. -/

namespace DeepWiki.TimeSeries

/-- **Definition 10.1.2 (eq 10.1.8)**: the **periodogram** `Iₙ(λ) = n⁻¹ |∑_{t<n} xₜ e^{-itλ}|²`
of the data `x₀, …, x_{n-1}` at frequency `λ` — the squared modulus of the discrete Fourier
transform `∑ₜ xₜ e^{-itλ}` of the data, normalized by the sample size `n`. -/
noncomputable def periodogram (n : ℕ) (x : ℕ → ℝ) (lam : ℝ) : ℝ :=
  Complex.normSq (∑ t ∈ Finset.range n, (x t : ℂ) * Complex.exp (-Complex.I * t * lam)) / n

/-- The periodogram is non-negative (a squared modulus divided by `n ≥ 0`). -/
theorem periodogram_nonneg (n : ℕ) (x : ℕ → ℝ) (lam : ℝ) : 0 ≤ periodogram n x lam :=
  div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg n)

/-- At frequency `0` the periodogram is `Iₙ(0) = n⁻¹ (∑_{t<n} xₜ)²` — `n` times the squared
sample mean (since `∑_{t<n} xₜ = n X̄ₙ`). -/
theorem periodogram_zero_eq (n : ℕ) (x : ℕ → ℝ) :
    periodogram n x 0 = (∑ t ∈ Finset.range n, x t) ^ 2 / n := by
  simp only [periodogram, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [← Complex.ofReal_sum, Complex.normSq_ofReal]
  ring

end DeepWiki.TimeSeries
