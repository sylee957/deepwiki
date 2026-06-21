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

/-- The two-sided extension of the causal `ψ = θ/φ` weights to `ℤ` (zero on negative indices), the
one-sided filter `ψ(B) = ∑_{j≥0} ψⱼ Bʲ` indexed over `ℤ` as `fourier_tsum_mul_shift` requires. -/
noncomputable def armaPsiZ (φ θ : ℝ[X]) : ℤ → ℝ :=
  fun m => if 0 ≤ m then PowerSeries.coeff m.toNat (armaPsi φ θ) else 0

@[simp] theorem armaPsiZ_natCast (φ θ : ℝ[X]) (n : ℕ) :
    armaPsiZ φ θ n = PowerSeries.coeff n (armaPsi φ θ) := by
  simp [armaPsiZ]

theorem armaPsiZ_neg (φ θ : ℝ[X]) {m : ℤ} (hm : m < 0) : armaPsiZ φ θ m = 0 := by
  simp [armaPsiZ, not_le.mpr hm]

/-- An integer outside `range (Nat.cast)` is negative, so `ψ̃` vanishes there. -/
private theorem armaPsiZ_eq_zero_of_not_mem_range {φ θ : ℝ[X]} {x : ℤ}
    (hx : x ∉ Set.range ((↑) : ℕ → ℤ)) : armaPsiZ φ θ x = 0 :=
  armaPsiZ_neg φ θ (not_le.mp fun h => hx ⟨x.toNat, Int.toNat_of_nonneg h⟩)

/-- **Absolute summability of the two-sided ARMA filter** `∑_{m:ℤ} |ψ̃ₘ| < ∞` (causal ARMA). -/
theorem summable_abs_armaPsiZ {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    Summable (fun m : ℤ => |armaPsiZ φ θ m|) := by
  refine (Function.Injective.summable_iff Nat.cast_injective
    (fun x hx => by rw [armaPsiZ_eq_zero_of_not_mem_range hx, abs_zero])).mp ?_
  have h : ((fun m : ℤ => |armaPsiZ φ θ m|) ∘ (Nat.cast : ℕ → ℤ))
      = fun n : ℕ => |PowerSeries.coeff n (armaPsi φ θ)| := by
    funext n; simp only [Function.comp_apply, armaPsiZ_natCast]
  rw [h]; exact summable_abs_armaPsi_coeff hφ

/-- **ARMA transfer function over `ℤ` `= θ/φ`:** the one-sided filter's frequency response,
`∑_{m:ℤ} ψ̃ₘ e^{-imλ} = θ(e^{-iλ})/φ(e^{-iλ})` — the `ℤ`-indexed form (matching `fourier_tsum_mul_shift`)
of `tsum_armaPsi_mul_pow_eq_div`, via the one-sided bridge `ℤ ← ℕ` and `e^{-imλ} = (e^{-iλ})ᵐ`. -/
theorem tsum_armaPsiZ_fourier_eq_div {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) (lam : ℝ) :
    (∑' m : ℤ, (armaPsiZ φ θ m : ℂ) * Complex.exp (-(m : ℂ) * lam * Complex.I))
      = aeval (Complex.exp (-Complex.I * lam)) θ / aeval (Complex.exp (-Complex.I * lam)) φ := by
  have hz : ‖Complex.exp (-Complex.I * lam)‖ ≤ 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hsupp : (Function.support fun m : ℤ =>
      (armaPsiZ φ θ m : ℂ) * Complex.exp (-(m : ℂ) * lam * Complex.I))
        ⊆ Set.range ((↑) : ℕ → ℤ) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxr
    exact hx (by rw [armaPsiZ_eq_zero_of_not_mem_range hxr]; simp)
  rw [← tsum_armaPsi_mul_pow_eq_div hφ hz,
    ← Function.Injective.tsum_eq Nat.cast_injective hsupp]
  refine tsum_congr fun n => ?_
  rw [armaPsiZ_natCast, ← Complex.exp_nat_mul]
  congr 2
  push_cast; ring

end DeepWiki.TimeSeries
