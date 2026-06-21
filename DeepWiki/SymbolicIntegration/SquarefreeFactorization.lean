import Mathlib.Algebra.Polynomial.Derivative
import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries

/-! # Squarefree factorization — the derivative criterion (Bronstein §1.6)
The squarefree part and deflations of `A ∈ D[x]` are computed by gcd's with `dA/dx`, resting on
the fact that a prime factor `P` divides `dA/dx` exactly once less than it divides `A`. Here we
prove the easy half (Theorem 1.6.1(i), over any commutative ring): if `Pⁿ⁺¹ ∣ A` then `Pⁿ`
divides both `A` and `dA/dx`, hence `Pⁿ ∣ gcd(A, dA/dx)`. The characteristic-`0` converse
(Theorem 1.6.1(ii)) and the deflation theory it powers are tracked as remaining library work. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- **Theorem 1.6.1(i)** (§1.6, core): if `Pⁿ⁺¹ ∣ A` then `Pⁿ` divides both `A` and its
derivative `dA/dx`. -/
theorem pow_dvd_and_pow_dvd_derivative {A P : R[X]} {n : ℕ} (h : P ^ (n + 1) ∣ A) :
    P ^ n ∣ A ∧ P ^ n ∣ derivative A := by
  refine ⟨(pow_dvd_pow P (Nat.le_succ n)).trans h, ?_⟩
  obtain ⟨B, rfl⟩ := h
  rw [derivative_mul, derivative_pow_succ]
  apply dvd_add
  · exact ((dvd_mul_left (P ^ n) _).mul_right _).mul_right _
  · exact (pow_dvd_pow P (Nat.le_succ n)).mul_right _

/-- **Theorem 1.6.1(i)** (§1.6): if `Pⁿ⁺¹ ∣ A` then `Pⁿ ∣ gcd(A, dA/dx)` (for any gcd `G` of `A`
and its derivative). -/
theorem pow_dvd_gcd_of_pow_succ_dvd {A P G : R[X]} {n : ℕ} (h : P ^ (n + 1) ∣ A)
    (hG : IsGCD A (derivative A) G) : P ^ n ∣ G :=
  hG.dvd (pow_dvd_and_pow_dvd_derivative h).1 (pow_dvd_and_pow_dvd_derivative h).2

section CharZero
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- **Theorem 1.6.1(ii)** (§1.6): the characteristic-`0` converse. If `P` is prime of positive
degree, `0 < n`, and `Pⁿ` divides both `A` and `dA/dx`, then `Pⁿ⁺¹ ∣ A`. -/
theorem pow_succ_dvd_of_pow_dvd_derivative {A P : R[X]} {n : ℕ} (hn : 0 < n) (hP : Prime P)
    (hPdeg : 0 < P.natDegree) (hA : P ^ n ∣ A) (hA' : P ^ n ∣ derivative A) :
    P ^ (n + 1) ∣ A := by
  obtain ⟨B, rfl⟩ := hA
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hPne : P ≠ 0 := hP.ne_zero
  by_contra hcon
  have hPB : ¬ P ∣ B := by
    rintro ⟨D, rfl⟩
    exact hcon ⟨D, by ring⟩
  have hkey : derivative (P ^ (m + 1) * B)
      = P ^ m * (C ((m : R) + 1) * derivative P * B + P * derivative B) := by
    rw [derivative_mul, derivative_pow_succ]; ring
  rw [hkey, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero m hPne)] at hA'
  have hPdvd : P ∣ C ((m : R) + 1) * derivative P * B :=
    (dvd_add_left (dvd_mul_right P (derivative B))).mp hA'
  rcases hP.dvd_mul.mp hPdvd with hL | hR
  · rcases hP.dvd_mul.mp hL with hCC | hPP
    · have hcne : ((m : R) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      have hdeglt : (C ((m : R) + 1)).degree < P.degree := by
        rw [degree_C hcne]; exact natDegree_pos_iff_degree_pos.mp hPdeg
      exact hcne (C_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hCC hdeglt))
    · exact (derivative_ne_zero.mpr hPdeg.ne')
        (eq_zero_of_dvd_of_degree_lt hPP (degree_derivative_lt hPne))
  · exact hPB hR

/-- **Theorem 1.6.1** (§1.6), combined: in characteristic `0`, for a prime `P` of positive
degree and `0 < n`, `Pⁿ⁺¹ ∣ A ⟺ Pⁿ` divides both `A` and `dA/dx`. -/
theorem pow_succ_dvd_iff {A P : R[X]} {n : ℕ} (hn : 0 < n) (hP : Prime P)
    (hPdeg : 0 < P.natDegree) :
    P ^ (n + 1) ∣ A ↔ P ^ n ∣ A ∧ P ^ n ∣ derivative A :=
  ⟨pow_dvd_and_pow_dvd_derivative,
    fun h => pow_succ_dvd_of_pow_dvd_derivative hn hP hPdeg h.1 h.2⟩

end CharZero

end DeepWiki.SymbolicIntegration
