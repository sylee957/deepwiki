import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # The Fourier-series spectral density of a summable autocovariance (Theorem 4.3.2)
For an absolutely summable function `K` on `ℤ` (`∑ₙ |K(n)| < ∞`), the Fourier series
`f(λ) = (1/2π) ∑ₙ e^{−inλ} K(n)` recovers `K` by inversion: `K(h) = ∫_{−π}^{π} e^{ihν} f(ν) dν`
(eq 4.3.5–4.3.7). The orthogonality of the complex exponentials on `[−π, π]` is the analytic core. -/

namespace DeepWiki.TimeSeries

open Complex Real intervalIntegral

/-- **Exponential orthogonality on `[−π, π]`:** `∫_{−π}^{π} e^{ikν} dν = 2π` if `k = 0`, else `0`,
for integer `k`. The orthogonality underlying the Fourier inversion of Theorem 4.3.2. -/
theorem integral_exp_int_mul_I (k : ℤ) :
    (∫ ν in (-π)..π, Complex.exp (k * ν * Complex.I)) = if k = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp [two_mul]
  · have hc : (k * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
    have hfun : (fun ν : ℝ => Complex.exp (k * ν * Complex.I))
        = fun ν : ℝ => Complex.exp (k * Complex.I * ν) := by
      funext ν; congr 1; ring
    rw [hfun, integral_exp_mul_complex hc]
    have key : Complex.exp (k * Complex.I * (π : ℂ)) = Complex.exp (k * Complex.I * ((-π : ℝ) : ℂ)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      exact ⟨k, by push_cast; ring⟩
    rw [key, sub_self, zero_div]

end DeepWiki.TimeSeries
