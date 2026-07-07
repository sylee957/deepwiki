import DeepWiki.SymbolicIntegration.Computable.Tower.RischDE

/-! # Normal-prime pole order drop

Polynomial valuation kernels for Risch normal-denominator arguments: a derivation lowers the
multiplicity at a normal prime by exactly one, and the same drop controls Wronskian numerators. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-! ### Derivation-generic pole order-drop -/

section DerivationPoleOrderDrop

variable {R : Type*} [CommRing R]

/-- Order-drop lower bound: for any `Derivation ℤ R R` and `q^n ∣ p`, `q^(n-1) ∣ D p`. -/
theorem pow_sub_one_dvd_deriv_of_pow_dvd (D : Derivation ℤ R R) {p q : R} {n : ℕ}
    (hdvd : q ^ n ∣ p) : q ^ (n - 1) ∣ D p := by
  obtain ⟨r, rfl⟩ := hdvd
  rw [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, smul_eq_mul]
  -- `D(q^n*r) = q^n*D r + r*(n*q^(n-1)*D q)`, both divisible by `q^(n-1)`.
  refine dvd_add ((pow_dvd_pow q (Nat.sub_le n 1)).mul_right _) ?_
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _

end DerivationPoleOrderDrop

section DerivationNormalOrderDrop

variable {K : Type*} [Field K] [CharZero K]

/-- Order-drop exact half at a normal prime: over a char-zero field, for a prime `p` normal for `D`
(`¬ p ∣ D p`), if `f = p^n*r` with `n ≥ 1` and `p ∤ r`, then `p^n ∤ D f`. -/
theorem not_pow_dvd_deriv_of_normal (D : Derivation ℤ K[X] K[X]) {p r : K[X]} {n : ℕ}
    (hp : Prime p) (hnormal : ¬ p ∣ D p) (hn : 1 ≤ n) (hr : ¬ p ∣ r) :
    ¬ p ^ n ∣ D (p ^ n * r) := by
  -- Write `n = m + 1`; Leibniz gives `D(p^(m+1)*r) = p^m*((m+1)*Dp*r + p*D r)`.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [Nat.zero_add] at *
  have hexp : D (p ^ (m + 1) * r)
      = p ^ m * ((m + 1 : ℕ) • (D p * r) + p * D r) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel]
    rw [nsmul_eq_mul, nsmul_eq_mul, smul_eq_mul, pow_succ]
    push_cast; ring
  intro hdvd
  have hpm0 : p ^ m ≠ 0 := pow_ne_zero m hp.ne_zero
  rw [hexp, pow_succ, mul_dvd_mul_iff_left hpm0] at hdvd
  have hp_dvd : p ∣ (m + 1 : ℕ) • (D p * r) + p * D r := hdvd
  have hp_smul : p ∣ (m + 1 : ℕ) • (D p * r) :=
    (dvd_add_right (dvd_mul_right p (D r))).mp (by rwa [add_comm] at hp_dvd)
  rw [nsmul_eq_mul] at hp_smul
  have hunit : IsUnit ((m + 1 : ℕ) : K[X]) := by
    rw [← Polynomial.C_eq_natCast]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero m))
  have hp_DpR : p ∣ D p * r := hunit.dvd_mul_left.mp hp_smul
  rcases (hp.dvd_mul.mp hp_DpR) with h | h
  · exact hnormal h
  · exact hr h

/-- Exact pole order-drop: over a char-zero field, for a prime `p` normal for `D` (`¬ p ∣ D p`), if
`f = p^n*r` with `n ≥ 1` and `p ∤ r`, then `emultiplicity p (D f) = n − 1`. -/
theorem emultiplicity_deriv_eq_sub_one_of_normal (D : Derivation ℤ K[X] K[X]) {p r : K[X]} {n : ℕ}
    (hp : Prime p) (hnormal : ¬ p ∣ D p) (hn : 1 ≤ n) (hr : ¬ p ∣ r) :
    emultiplicity p (D (p ^ n * r)) = (n - 1 : ℕ) := by
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · exact pow_sub_one_dvd_deriv_of_pow_dvd D (Dvd.intro r rfl)
  · rw [Nat.sub_add_cancel hn]; exact not_pow_dvd_deriv_of_normal D hp hnormal hn hr

/-! ### Wronskian-numerator order-drop -/

/-- Wronskian-numerator multiplicity: for a normal prime `p` (`¬ p ∣ D p`) over a char-zero field,
`a = p^m*a'`, `b = p^k*b'` with `p ∤ a', b'` and `m < k`, `emultiplicity p (D a*b − a*D b) = m + k − 1`. -/
theorem emultiplicity_wronskian_numerator_eq_of_normal (D : Derivation ℤ K[X] K[X]) {p a' b' : K[X]}
    {m k : ℕ} (hp : Prime p) (hnormal : ¬ p ∣ D p) (hlt : m < k) (ha' : ¬ p ∣ a') (hb' : ¬ p ∣ b') :
    emultiplicity p (D (p ^ m * a') * (p ^ k * b') - (p ^ m * a') * D (p ^ k * b'))
      = (m + k - 1 : ℕ) := by
  have hk1 : 1 ≤ k := Nat.one_le_of_lt hlt
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1)
  simp only [Nat.zero_add] at *
  have hleib : ∀ (n : ℕ) (s : K[X]),
      D (p ^ n * s) = p ^ n * D s + (n : ℤ) • (p ^ (n - 1) * (D p * s)) := by
    intro n s
    rw [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      nsmul_eq_mul, zsmul_eq_mul]
    push_cast; ring
  set W : K[X] := ((m : ℤ) - (j + 1 : ℕ)) • (D p * (a' * b')) + p * (D a' * b' - a' * D b') with hW
  have hfactor : D (p ^ m * a') * (p ^ (j + 1) * b') - (p ^ m * a') * D (p ^ (j + 1) * b')
      = p ^ (m + j) * W := by
    rw [hleib m a', hleib (j + 1) b', hW, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp only [pow_zero, one_mul, Nat.cast_zero, zero_sub, Nat.zero_add, zsmul_eq_mul]
      push_cast; ring
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
      simp only [Nat.succ_sub_one, zsmul_eq_mul]
      push_cast
      rw [show m' + 1 + j = (m' + j) + 1 by ring, pow_succ]
      ring
  rw [hfactor]
  have hWne : ¬ p ∣ W := by
    rw [hW]
    intro hdvd
    have hp_lead : p ∣ ((m : ℤ) - (j + 1 : ℕ)) • (D p * (a' * b')) :=
      (dvd_add_right (dvd_mul_right p _)).mp (by rwa [add_comm] at hdvd)
    rw [zsmul_eq_mul] at hp_lead
    have hconstK : ((m : ℤ) - (j + 1 : ℕ) : K) ≠ 0 := by
      have hmj : ((m : ℤ) - (j + 1 : ℕ) : ℤ) ≠ 0 := by omega
      simpa using (Int.cast_ne_zero (α := K)).mpr hmj
    have hcast : (((m : ℤ) - (j + 1 : ℕ) : ℤ) : K[X]) = Polynomial.C ((m : ℤ) - (j + 1 : ℕ) : K) := by
      simp
    have hunit : IsUnit (((m : ℤ) - (j + 1 : ℕ) : ℤ) : K[X]) := by
      rw [hcast]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hconstK)
    have hp_DpAB : p ∣ D p * (a' * b') := hunit.dvd_mul_left.mp hp_lead
    rcases hp.dvd_mul.mp hp_DpAB with h | h
    · exact hnormal h
    · rcases hp.dvd_mul.mp h with h' | h'
      · exact ha' h'
      · exact hb' h'
  rw [emultiplicity_mul hp, emultiplicity_pow_self_of_prime hp, emultiplicity_eq_zero.mpr hWne,
    add_zero, show m + (j + 1) - 1 = m + j from by omega]

end DerivationNormalOrderDrop

/-! ### Restatements against the intended wording (anonymous `example`s) -/

example {R : Type*} [CommRing R] (D : Derivation ℤ R R) {p q : R} {n : ℕ} (hdvd : q ^ n ∣ p) :
    q ^ (n - 1) ∣ D p :=
  pow_sub_one_dvd_deriv_of_pow_dvd D hdvd

example {K : Type*} [Field K] [CharZero K] (D : Derivation ℤ K[X] K[X]) {p r : K[X]} {n : ℕ}
    (hp : Prime p) (hnormal : ¬ p ∣ D p) (hn : 1 ≤ n) (hr : ¬ p ∣ r) :
    emultiplicity p (D (p ^ n * r)) = (n - 1 : ℕ) :=
  emultiplicity_deriv_eq_sub_one_of_normal D hp hnormal hn hr

/-! ### Axiom audit -/

#print axioms pow_sub_one_dvd_deriv_of_pow_dvd
#print axioms not_pow_dvd_deriv_of_normal
#print axioms emultiplicity_deriv_eq_sub_one_of_normal

end DeepWiki.SymbolicIntegration
