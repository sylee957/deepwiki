import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! # The spectral density of an ARMA process (§4.4)
The rational spectral density `f(λ) = (σ²/2π) · |θ(e^{-iλ})|² / |φ(e^{-iλ})|²` of an ARMA(p,q)
process `φ(B)X = θ(B)Z`, `Z ~ WN(0,σ²)` (eq 4.4.5). The formula is an algebraic definition; that
this `f` is the spectral density of the process (Theorem 4.4.2) is proved through the `MA(∞)`
representation and the filter transformation `f_X = |ψ(e^{-iλ})|² f_Z` (Theorem 4.4.1), whose
spectral-representation machinery is not developed here. -/

namespace DeepWiki.TimeSeries

open Polynomial

/-- **§4.4 (Theorem 4.4.2, eq 4.4.5)**: the **spectral density of an ARMA(p,q) process**
`φ(B)X = θ(B)Z`, `Z ~ WN(0,σ²)` — the rational function
`f(λ) = (σ²/2π) · |θ(e^{-iλ})|² / |φ(e^{-iλ})|²`. (That `f` is the spectral density of the
process is Theorem 4.4.2, whose proof uses the `MA(∞)` representation; here `f` is the algebraic
formula itself.) -/
noncomputable def armaSpectralDensity (φ θ : ℝ[X]) (σ2 : ℝ) (lam : ℝ) : ℝ :=
  σ2 / (2 * Real.pi) *
    (Complex.normSq (aeval (Complex.exp (-Complex.I * lam)) θ) /
      Complex.normSq (aeval (Complex.exp (-Complex.I * lam)) φ))

/-- The ARMA spectral density is non-negative when `σ² ≥ 0` (a ratio of squared moduli). -/
theorem armaSpectralDensity_nonneg {σ2 : ℝ} (hσ : 0 ≤ σ2) (φ θ : ℝ[X]) (lam : ℝ) :
    0 ≤ armaSpectralDensity φ θ σ2 lam := by
  rw [armaSpectralDensity]
  apply mul_nonneg
  · positivity
  · exact div_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- **Spectral density of white noise** (`φ = θ = 1`): the constant `σ²/2π`. -/
theorem armaSpectralDensity_one_one (σ2 lam : ℝ) :
    armaSpectralDensity 1 1 σ2 lam = σ2 / (2 * Real.pi) := by
  simp [armaSpectralDensity, Complex.normSq_one]

end DeepWiki.TimeSeries
