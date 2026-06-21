import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

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

/-- **The Fourier-series spectral density** `f(λ) = (1/2π) ∑ₙ e^{−inλ} K(n)` of a function `K` on
`ℤ` (eq 4.3.7). For an absolutely summable autocovariance `K = γ`, this is its spectral density. -/
noncomputable def fourierSpectralDensity (K : ℤ → ℂ) (lam : ℝ) : ℂ :=
  (1 / (2 * π)) * ∑' n : ℤ, Complex.exp (-(n : ℂ) * lam * Complex.I) * K n

/-- `∫_{−π}^{π} e^{ihν} e^{−inν} dν = 2π` if `h = n`, else `0` — orthogonality of the Fourier
exponentials `{e^{inλ}}`, the `n`-th-term selector for the inversion of Theorem 4.3.2. -/
theorem integral_exp_mul_exp_neg (h n : ℤ) :
    (∫ ν in (-π)..π, Complex.exp (h * ν * Complex.I) * Complex.exp (-(n : ℂ) * ν * Complex.I))
      = if h = n then (2 * π : ℂ) else 0 := by
  have hfun : (fun ν : ℝ => Complex.exp (h * ν * Complex.I) * Complex.exp (-(n : ℂ) * ν * Complex.I))
      = fun ν : ℝ => Complex.exp (((h - n : ℤ) : ℂ) * ν * Complex.I) := by
    funext ν; rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hfun, integral_exp_int_mul_I (h - n)]
  simp only [sub_eq_zero]

open MeasureTheory in
/-- **Theorem 4.3.2 (Fourier inversion of a summable autocovariance):** if `∑ₙ |K(n)| < ∞`, then
`K(h) = ∫_{−π}^{π} e^{ihν} f(ν) dν` for `f = fourierSpectralDensity K` (eq 4.3.5–4.3.7) — so `f` is
the spectral density of `K`: its Fourier coefficients recover `K`. By term-by-term integration
(`integral_tsum`, justified by `∑ₙ |K(n)| < ∞`) and the exponential orthogonality. -/
theorem fourierSpectralDensity_inversion {K : ℤ → ℂ} (hK : Summable fun n => ‖K n‖) (h : ℤ) :
    (∫ ν in (-π)..π, Complex.exp (h * ν * Complex.I) * fourierSpectralDensity K ν) = K h := by
  have hle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  have hπ : (0 : ℝ) < 2 * π := by positivity
  set g : ℤ → ℝ → ℂ := fun n ν =>
    Complex.exp (h * ν * Complex.I) * (1 / (2 * π)) * (Complex.exp (-(n : ℂ) * ν * Complex.I) * K n)
    with hgdef
  have hgnorm : ∀ n (ν : ℝ), ‖g n ν‖ ≤ ‖K n‖ := fun n ν => by
    have e1 : ‖Complex.exp ((h : ℂ) * (ν : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have e2 : ‖Complex.exp (-(n : ℂ) * (ν : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hc : ‖((1 : ℂ) / (2 * π))‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    have hle1 : (1 : ℝ) / (2 * π) ≤ 1 := by rw [div_le_one hπ]; linarith [Real.pi_gt_three]
    simp only [hgdef, norm_mul, e1, e2, hc, one_mul]
    calc 1 / (2 * π) * ‖K n‖ ≤ 1 * ‖K n‖ := mul_le_mul_of_nonneg_right hle1 (norm_nonneg _)
      _ = ‖K n‖ := one_mul _
  have hgcont : ∀ n, Continuous (g n) := fun n => by rw [hgdef]; fun_prop
  have hpt : ∀ ν : ℝ,
      Complex.exp (h * ν * Complex.I) * fourierSpectralDensity K ν = ∑' n, g n ν := fun ν => by
    rw [fourierSpectralDensity, ← mul_assoc, ← tsum_mul_left]
  have hfin : ENNReal.ofReal (2 * π) * ∑' n : ℤ, ‖K n‖ₑ ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have : Summable fun n : ℤ => ‖K n‖₊ :=
      NNReal.summable_coe.mp (by simpa only [coe_nnnorm] using hK)
    simpa only [enorm_eq_nnnorm] using (ENNReal.tsum_coe_ne_top_iff_summable.mpr this)
  simp_rw [hpt]
  rw [intervalIntegral.integral_of_le hle, integral_tsum
    (fun n => (hgcont n).aestronglyMeasurable) ?_]
  · simp_rw [← intervalIntegral.integral_of_le hle]
    have hterm : ∀ n, (∫ ν in (-π)..π, g n ν)
        = (1 / (2 * π)) * K n * (if h = n then (2 * π : ℂ) else 0) := by
      intro n
      have hcong : (∫ ν in (-π)..π, g n ν) = ∫ ν in (-π)..π, (1 / (2 * π)) * K n *
          (Complex.exp (h * ν * Complex.I) * Complex.exp (-(n : ℂ) * ν * Complex.I)) := by
        apply intervalIntegral.integral_congr
        intro ν _
        simp only [hgdef]; ring
      rw [hcong, intervalIntegral.integral_const_mul, integral_exp_mul_exp_neg]
    simp_rw [hterm]
    rw [tsum_eq_single h fun n hn => by rw [if_neg (Ne.symm hn), mul_zero], if_pos rfl]
    field_simp
  · have hbound : ∀ n : ℤ, ∫⁻ ν in Set.Ioc (-π) π, ‖g n ν‖ₑ ∂volume
        ≤ ENNReal.ofReal (2 * π) * ‖K n‖ₑ := by
      intro n
      calc ∫⁻ ν in Set.Ioc (-π) π, ‖g n ν‖ₑ ∂volume
          ≤ ∫⁻ _ν in Set.Ioc (-π) π, ‖K n‖ₑ ∂volume :=
            lintegral_mono fun ν => by
              rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe]; exact_mod_cast hgnorm n ν
        _ = ENNReal.ofReal (2 * π) * ‖K n‖ₑ := by
            rw [setLIntegral_const, Real.volume_Ioc, show (π : ℝ) - -π = 2 * π from by ring, mul_comm]
    have hbsum : ∑' n : ℤ, ∫⁻ ν in Set.Ioc (-π) π, ‖g n ν‖ₑ ∂volume
        ≤ ENNReal.ofReal (2 * π) * ∑' n : ℤ, ‖K n‖ₑ := by
      rw [← ENNReal.tsum_mul_left]; exact ENNReal.tsum_le_tsum hbound
    exact ne_top_of_le_ne_top hfin hbsum

/-- **White-noise spectral density (Theorem 4.3.2 applied):** the white-noise autocovariance
`γ(h) = σ²·[h = 0]` (absolutely summable) has the constant Fourier-series spectral density
`f(λ) = σ²/(2π)` — the flat spectrum of white noise. -/
theorem fourierSpectralDensity_kronecker (σ2 : ℝ) (lam : ℝ) :
    fourierSpectralDensity (fun h => if h = 0 then (σ2 : ℂ) else 0) lam = (σ2 : ℂ) / (2 * π) := by
  rw [fourierSpectralDensity, tsum_eq_single 0 fun n hn => by simp [hn]]
  simp [div_eq_inv_mul]

/-- **Theorem 4.4.1 (Fourier transform of an autocovariance):** for an absolutely summable filter `ψ`
(`∑ₙ |ψₙ| < ∞`), the Fourier series of the correlation `∑ₖ ψₖ ψ_{k+n}` factors as a product of the
transfer functions: `∑ₙ e^{−inλ} ∑ₖ ψₖ ψ_{k+n} = (∑ₖ ψₖ e^{ikλ})(∑ₘ ψₘ e^{−imλ})`. Since `ψ` is real
the two factors are conjugate, so the right side is `|∑ₘ ψₘ e^{−imλ}|²` — the spectral density of a
linear-filtered process is `|ψ̂(e^{−iλ})|²` times the input's (eq 4.4.3, the basis of the rational
`ARMA` spectral density). Proven by the shear `(n,k) ↦ (k, k+n)` turning the double Fourier sum into a
product of single sums. -/
theorem fourier_tsum_mul_shift {ψ : ℤ → ℝ} (hψ : Summable fun n => |ψ n|) (lam : ℝ) :
    (∑' n : ℤ, Complex.exp (-(n : ℂ) * lam * Complex.I) * ∑' k : ℤ, (ψ k : ℂ) * (ψ (k + n) : ℂ))
      = (∑' k : ℤ, (ψ k : ℂ) * Complex.exp ((k : ℂ) * lam * Complex.I)) *
        (∑' m : ℤ, (ψ m : ℂ) * Complex.exp (-(m : ℂ) * lam * Complex.I)) := by
  set f : ℤ → ℂ := fun k => (ψ k : ℂ) * Complex.exp ((k : ℂ) * lam * Complex.I) with hf
  set g : ℤ → ℂ := fun m => (ψ m : ℂ) * Complex.exp (-(m : ℂ) * lam * Complex.I) with hg
  have hfn : Summable fun k => ‖f k‖ := by
    have : (fun k => ‖f k‖) = fun k => |ψ k| := by
      funext k; rw [hf, norm_mul, Complex.norm_exp, Complex.norm_real]; simp
    rw [this]; exact hψ
  have hgn : Summable fun m => ‖g m‖ := by
    have : (fun m => ‖g m‖) = fun m => |ψ m| := by
      funext m; rw [hg, norm_mul, Complex.norm_exp, Complex.norm_real]; simp
    rw [this]; exact hψ
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.2, p.2 + p.1)
      invFun := fun p => (p.2 - p.1, p.1)
      left_inv := fun p => by obtain ⟨n, k⟩ := p; simp
      right_inv := fun p => by obtain ⟨a, b⟩ := p; simp }
  have hcomp : (fun p : ℤ × ℤ =>
      Complex.exp (-(p.1 : ℂ) * lam * Complex.I) * ((ψ p.2 : ℂ) * (ψ (p.2 + p.1) : ℂ)))
      = (fun q : ℤ × ℤ => f q.1 * g q.2) ∘ e := by
    funext p
    have hxp : Complex.exp ((p.2 : ℂ) * lam * Complex.I) *
        Complex.exp (-((p.2 + p.1 : ℤ) : ℂ) * lam * Complex.I)
        = Complex.exp (-(p.1 : ℂ) * lam * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp only [hf, hg, e, Function.comp, Equiv.coe_fn_mk]
    rw [mul_mul_mul_comm, hxp]; ring
  have hFsum : Summable fun p : ℤ × ℤ =>
      Complex.exp (-(p.1 : ℂ) * lam * Complex.I) * ((ψ p.2 : ℂ) * (ψ (p.2 + p.1) : ℂ)) := by
    rw [hcomp]; exact e.summable_iff.mpr ((hfn.mul_norm hgn).of_norm)
  rw [tsum_mul_tsum_of_summable_norm hfn hgn]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_prod' hFsum fun n => hFsum.prod_factor n, hcomp]
  exact e.tsum_eq fun q => f q.1 * g q.2

/-- **Theorem 4.4.1 as a squared modulus (eq 4.4.3):** for a real absolutely summable filter `ψ`, the
Fourier series of the correlation `∑ₖ ψₖ ψ_{k+n}` equals the *squared modulus* of the transfer
function `‖∑ₘ ψₘ e^{−imλ}‖²` — in particular a non-negative real. So the spectral density of a
linear-filtered process is `|ψ̂(e^{−iλ})|²` times the input's, and is `≥ 0`. -/
theorem fourier_tsum_mul_shift_eq_normSq {ψ : ℤ → ℝ} (hψ : Summable fun n => |ψ n|) (lam : ℝ) :
    (∑' n : ℤ, Complex.exp (-(n : ℂ) * lam * Complex.I) * ∑' k : ℤ, (ψ k : ℂ) * (ψ (k + n) : ℂ))
      = (Complex.normSq (∑' m : ℤ, (ψ m : ℂ) * Complex.exp (-(m : ℂ) * lam * Complex.I)) : ℂ) := by
  rw [fourier_tsum_mul_shift hψ]
  set T : ℂ := ∑' m : ℤ, (ψ m : ℂ) * Complex.exp (-(m : ℂ) * lam * Complex.I) with hT
  have hconj : (∑' k : ℤ, (ψ k : ℂ) * Complex.exp ((k : ℂ) * lam * Complex.I)) = star T := by
    rw [hT, tsum_star]
    refine tsum_congr fun k => ?_
    have h1 : star (ψ k : ℂ) = (ψ k : ℂ) := by simp
    have h2 : star (Complex.exp (-(k : ℂ) * lam * Complex.I))
        = Complex.exp ((k : ℂ) * lam * Complex.I) := by
      rw [← starRingEnd_apply, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_neg, map_intCast, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [star_mul', h1, h2, mul_comm]
  rw [hconj, mul_comm, ← starRingEnd_apply, Complex.mul_conj]

end DeepWiki.TimeSeries
