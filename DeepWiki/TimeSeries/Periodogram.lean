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

open Real (pi)

/-- **Root-of-unity orthogonality (the core of Proposition 10.1.1):** the geometric sum of the
`n`-th roots of unity `∑_{t<n} e^{2πi m t/n}` is `n` if `n ∣ m` and `0` otherwise. This is the
orthogonality of the Fourier basis at the Fourier frequencies `ωⱼ = 2πj/n`. -/
theorem sum_range_exp_two_pi_mul_I (n : ℕ) (hn : 0 < n) (m : ℤ) :
    ∑ t ∈ Finset.range n, Complex.exp (2 * pi * Complex.I * m * t / n)
      = if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h2pi : (2 * (pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcast : ∀ t : ℕ, Complex.exp (2 * pi * Complex.I * m * t / n)
      = Complex.exp (2 * pi * Complex.I * m / n) ^ t := by
    intro t; rw [← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hcast]
  set ζ := Complex.exp (2 * pi * Complex.I * m / n) with hζdef
  have hζn : ζ ^ n = 1 := by
    rw [hζdef, ← Complex.exp_nat_mul,
      show (n : ℂ) * (2 * pi * Complex.I * m / n) = (m : ℂ) * (2 * pi * Complex.I) by field_simp]
    exact_mod_cast Complex.exp_int_mul_two_pi_mul_I m
  by_cases hdvd : (n : ℤ) ∣ m
  · obtain ⟨q, rfl⟩ := hdvd
    have hζ1 : ζ = 1 := by
      rw [hζdef,
        show (2 * pi * Complex.I * ((n : ℤ) * q : ℤ) / n : ℂ) = (q : ℂ) * (2 * pi * Complex.I) by
          push_cast; field_simp]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I q
    rw [if_pos (dvd_mul_right _ _), hζ1]
    simp
  · have hζne : ζ ≠ 1 := by
      intro h
      rw [hζdef, Complex.exp_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      apply hdvd
      rw [div_eq_iff hn0] at hk
      have heq : (2 * (pi : ℂ) * Complex.I) * (m : ℂ)
          = (2 * (pi : ℂ) * Complex.I) * ((n : ℂ) * k) := by linear_combination hk
      have hmn : (m : ℂ) = (n : ℂ) * k := mul_left_cancel₀ h2pi heq
      exact ⟨k, by exact_mod_cast hmn⟩
    rw [if_neg hdvd, geom_sum_eq hζne, hζn, sub_self, zero_div]

/-- **Proposition 10.1.1 (orthonormality of the Fourier basis):** the Fourier vectors
`eⱼ(t) = n^{−1/2} e^{itωⱼ}` (frequencies `ωⱼ = 2πj/n`) are orthonormal — their inner product
`⟨eⱼ, eₖ⟩ = n⁻¹ ∑_{t<n} e^{it(ωⱼ−ωₖ)}` is `1` when `n ∣ (j−k)` (i.e. `ωⱼ = ωₖ`) and `0` otherwise. -/
theorem fourier_inner_eq (n : ℕ) (hn : 0 < n) (j k : ℤ) :
    (∑ t ∈ Finset.range n, Complex.exp (2 * pi * Complex.I * ((j - k : ℤ) : ℂ) * t / n)) / n
      = if (n : ℤ) ∣ (j - k) then 1 else 0 := by
  rw [sum_range_exp_two_pi_mul_I n hn (j - k)]
  split_ifs with h
  · exact div_self (Nat.cast_ne_zero.mpr hn.ne')
  · exact zero_div _

end DeepWiki.TimeSeries
