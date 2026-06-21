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

/-- **Definition 10.1.1 (eq 10.1.7)**: the **discrete Fourier transform** of the data at frequency
`λ`, `a(λ) = n^{−1/2} ∑_{t<n} xₜ e^{−itλ}` (the inner product `⟨x, e_λ⟩` against the Fourier vector).
At a Fourier frequency `ωⱼ = 2πj/n` this is the coefficient `aⱼ`. -/
noncomputable def dftCoeff (n : ℕ) (x : ℕ → ℝ) (lam : ℝ) : ℂ :=
  ((Real.sqrt n)⁻¹ : ℝ) * ∑ t ∈ Finset.range n, (x t : ℂ) * Complex.exp (-Complex.I * t * lam)

/-- **§10.1 (eq 10.1.8):** the periodogram is the squared modulus of the discrete Fourier transform,
`Iₙ(λ) = |a(λ)|²`. -/
theorem periodogram_eq_normSq_dftCoeff (n : ℕ) (x : ℕ → ℝ) (lam : ℝ) :
    periodogram n x lam = Complex.normSq (dftCoeff n x lam) := by
  have hc : Complex.normSq (((Real.sqrt n)⁻¹ : ℝ) : ℂ) = (n : ℝ)⁻¹ := by
    rw [Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  rw [periodogram, div_eq_inv_mul, dftCoeff, Complex.normSq_mul, hc]

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

/-- Inner orthogonality of the data-frequency exponentials: for `s, t < n`,
`∑_{j<n} e^{-itωⱼ} conj(e^{-isωⱼ}) = n` if `s = t`, else `0` (`ωⱼ = 2πj/n`). The diagonal kernel
behind the periodogram's analysis of variance. -/
theorem sum_exp_mul_conj_exp (n : ℕ) (hn : 0 < n) (s t : ℕ) (hs : s < n) (ht : t < n) :
    ∑ j ∈ Finset.range n, Complex.exp (-Complex.I * t * (2 * pi * j / n))
        * (starRingEnd ℂ) (Complex.exp (-Complex.I * s * (2 * pi * j / n)))
      = if s = t then (n : ℂ) else 0 := by
  have hrw : ∀ j : ℕ, Complex.exp (-Complex.I * t * (2 * pi * j / n))
      * (starRingEnd ℂ) (Complex.exp (-Complex.I * s * (2 * pi * j / n)))
      = Complex.exp (2 * pi * Complex.I * (((s : ℤ) - t : ℤ) : ℂ) * j / n) := by
    intro j
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_neg, map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_natCast, map_ofNat]
    push_cast
    ring
  simp_rw [hrw]
  rw [sum_range_exp_two_pi_mul_I n hn ((s : ℤ) - t)]
  have hiff : ((n : ℤ) ∣ ((s : ℤ) - t)) ↔ s = t := by
    constructor
    · intro hd
      rcases lt_trichotomy ((s : ℤ) - t) 0 with h | h | h
      · exact absurd (Int.le_of_dvd (by omega) ((dvd_neg).mpr hd)) (by omega)
      · omega
      · exact absurd (Int.le_of_dvd h hd) (by omega)
    · rintro rfl; simp
  simp only [hiff]

/-- **Equation 10.1.9 (analysis of variance / Parseval):** the periodogram ordinates at the Fourier
frequencies `ωⱼ = 2πj/n` sum to the total sum of squares — `∑_{j<n} Iₙ(ωⱼ) = ∑_{t<n} xₜ²`. -/
theorem periodogram_sum_eq (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) :
    ∑ j ∈ Finset.range n, periodogram n x (2 * pi * j / n) = ∑ t ∈ Finset.range n, (x t) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- the complex Parseval identity: ∑_j |Sⱼ|² (as ∑ Sⱼ conj Sⱼ) = n · ∑ xₜ²
  have keyC : ∑ j ∈ Finset.range n,
      (∑ t ∈ Finset.range n, (x t : ℂ) * Complex.exp (-Complex.I * t * (2 * pi * j / n)))
        * (starRingEnd ℂ) (∑ t ∈ Finset.range n, (x t : ℂ) * Complex.exp (-Complex.I * t * (2 * pi * j / n)))
      = (n : ℂ) * ∑ t ∈ Finset.range n, (x t : ℂ) ^ 2 := by
    have expand : ∀ j ∈ Finset.range n,
        (∑ t ∈ Finset.range n, (x t : ℂ) * Complex.exp (-Complex.I * t * (2 * pi * j / n)))
          * (starRingEnd ℂ) (∑ t ∈ Finset.range n, (x t : ℂ) * Complex.exp (-Complex.I * t * (2 * pi * j / n)))
        = ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n,
            (x t : ℂ) * (x s : ℂ) * (Complex.exp (-Complex.I * t * (2 * pi * j / n))
              * (starRingEnd ℂ) (Complex.exp (-Complex.I * s * (2 * pi * j / n)))) := by
      intro j _
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul, Complex.conj_ofReal]; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.sum_comm]
    have inner : ∀ s ∈ Finset.range n,
        ∑ j ∈ Finset.range n, (x t : ℂ) * (x s : ℂ) * (Complex.exp (-Complex.I * t * (2 * pi * j / n))
          * (starRingEnd ℂ) (Complex.exp (-Complex.I * s * (2 * pi * j / n))))
        = (x t : ℂ) * (x s : ℂ) * (if s = t then (n : ℂ) else 0) := by
      intro s hs
      rw [← Finset.mul_sum, sum_exp_mul_conj_exp n hn s t (Finset.mem_range.mp hs) (Finset.mem_range.mp ht)]
    rw [Finset.sum_congr rfl inner]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.range n) t, if_pos ht]
    ring
  -- descend: ∑ periodogram = (∑ normSq)/n = (n ∑ x²)/n = ∑ x²
  have key : ∑ j ∈ Finset.range n,
      Complex.normSq (∑ t ∈ Finset.range n, (x t : ℂ) * Complex.exp (-Complex.I * t * (2 * pi * j / n)))
      = (n : ℝ) * ∑ t ∈ Finset.range n, (x t) ^ 2 := by
    have hC : ((∑ j ∈ Finset.range n,
        Complex.normSq (∑ t ∈ Finset.range n, (x t : ℂ) * Complex.exp (-Complex.I * t * (2 * pi * j / n))) : ℝ) : ℂ)
        = (n : ℂ) * ∑ t ∈ Finset.range n, (x t : ℂ) ^ 2 := by
      rw [Complex.ofReal_sum]
      simp_rw [← Complex.mul_conj]
      exact keyC
    exact_mod_cast hC
  simp_rw [periodogram]
  push_cast
  rw [← Finset.sum_div, key, mul_comm, mul_div_assoc, div_self hn0, mul_one]

end DeepWiki.TimeSeries
