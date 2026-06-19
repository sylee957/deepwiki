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

/-- `|1 + θ₁ e^{-iλ}|² = 1 + 2θ₁ cos λ + θ₁²` — the squared modulus of the MA(1) transfer
function (`e^{-iλ} = cos λ − i sin λ`). -/
theorem normSq_one_add_ofReal_mul_expNegI (θ1 lam : ℝ) :
    Complex.normSq (1 + (θ1 : ℂ) * Complex.exp (-Complex.I * (lam : ℂ)))
      = 1 + 2 * θ1 * Real.cos lam + θ1 ^ 2 := by
  have hzre : (Complex.exp (-Complex.I * (lam : ℂ))).re = Real.cos lam := by
    rw [Complex.exp_re]; simp [Real.cos_neg]
  have hzim : (Complex.exp (-Complex.I * (lam : ℂ))).im = -Real.sin lam := by
    rw [Complex.exp_im]; simp [Real.sin_neg]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzre, hzim]
  nlinarith [Real.sin_sq_add_cos_sq lam]

/-- **Example 4.4.1**: the spectral density of an `MA(1)` process `Xₜ = Zₜ + θ₁Zₜ₋₁`
(`φ = 1`, `θ = 1 + θ₁z`) is `f(λ) = (σ²/2π)(1 + 2θ₁ cos λ + θ₁²)`. -/
theorem armaSpectralDensity_ma1 (θ1 σ2 lam : ℝ) :
    armaSpectralDensity 1 (1 + Polynomial.C θ1 * Polynomial.X) σ2 lam
      = σ2 / (2 * Real.pi) * (1 + 2 * θ1 * Real.cos lam + θ1 ^ 2) := by
  rw [armaSpectralDensity, map_one, Complex.normSq_one, div_one]
  congr 1
  rw [show aeval (Complex.exp (-Complex.I * (lam : ℂ))) (1 + Polynomial.C θ1 * Polynomial.X)
        = 1 + (θ1 : ℂ) * Complex.exp (-Complex.I * (lam : ℂ)) by
      simp [map_add, map_mul, aeval_C, aeval_X, Complex.coe_algebraMap]]
  exact normSq_one_add_ofReal_mul_expNegI θ1 lam

/-- **Example 4.4.2**: the spectral density of an `AR(1)` process `Xₜ = φ₁Xₜ₋₁ + Zₜ`
(`φ = 1 − φ₁z`, `θ = 1`) is `f(λ) = (σ²/2π) / (1 − 2φ₁ cos λ + φ₁²)`. -/
theorem armaSpectralDensity_ar1 (φ1 σ2 lam : ℝ) :
    armaSpectralDensity (1 - Polynomial.C φ1 * Polynomial.X) 1 σ2 lam
      = σ2 / (2 * Real.pi) / (1 - 2 * φ1 * Real.cos lam + φ1 ^ 2) := by
  rw [armaSpectralDensity, map_one, Complex.normSq_one,
    show aeval (Complex.exp (-Complex.I * (lam : ℂ))) (1 - Polynomial.C φ1 * Polynomial.X)
        = 1 + ((-φ1 : ℝ) : ℂ) * Complex.exp (-Complex.I * (lam : ℂ)) by
      rw [map_sub, map_one, map_mul, aeval_C, aeval_X, Complex.coe_algebraMap]; push_cast; ring,
    normSq_one_add_ofReal_mul_expNegI (-φ1) lam,
    show 1 + 2 * -φ1 * Real.cos lam + (-φ1) ^ 2
        = 1 - 2 * φ1 * Real.cos lam + φ1 ^ 2 by ring,
    mul_one_div]

end DeepWiki.TimeSeries
