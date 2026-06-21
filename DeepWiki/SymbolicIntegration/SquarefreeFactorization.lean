import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries

/-! # Squarefree factorization — the derivative criterion (Bronstein §1.6–§1.7)
The squarefree part and deflations of `A ∈ D[x]` are computed by gcd's with `dA/dx`, resting on
the fact that a prime factor `P` divides `dA/dx` exactly once less than it divides `A`. Here we
prove the easy half (Theorem 1.6.1(i), over any commutative ring): if `Pⁿ⁺¹ ∣ A` then `Pⁿ`
divides both `A` and `dA/dx`, hence `Pⁿ ∣ gcd(A, dA/dx)`; the characteristic-`0` converse
(Theorem 1.6.1(ii)); and the squarefree criterion of §1.7 (Lemma 1.7.1): over a characteristic-`0`
field, `A` is squarefree iff `gcd(A, dA/dx) = 1`. The deflation theory and the full
squarefree-factorization routine are tracked as remaining library work. -/

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

/-- **Lemma 1.7.1** (§1.7): over a characteristic-`0` field, `A` is squarefree iff it is coprime
to its derivative — `gcd(A, dA/dx) = 1`. (`Squarefree ↔ Separable` on a perfect field, and
`Separable A ↔ IsCoprime A (dA/dx)`.) -/
theorem squarefree_iff_isCoprime_derivative {K : Type*} [Field K] [CharZero K] {A : K[X]} :
    Squarefree A ↔ IsCoprime A (derivative A) :=
  PerfectField.separable_iff_squarefree.symm.trans (separable_def A)

section Deflation
open UniqueFactorizationMonoid
variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D]

open Classical in
/-- **Squarefree part** (§1.6, Definition 1.6.2): `A* = ∏ Pᵢ`, the product of the distinct prime
factors of the primitive part `pp(A) = ∏ Pᵢ^eᵢ`. -/
noncomputable def squarefreePart (A : D[X]) : D[X] :=
  ∏ P ∈ (factors A.primPart).toFinset, P

open Classical in
/-- **`k`-deflation** (§1.6, Definition 1.6.2): `A⁻ᵏ = ∏ Pᵢ^max(0, eᵢ−k)` (truncated exponents),
from `pp(A) = ∏ Pᵢ^eᵢ`. The `1`-deflation `A⁻ = A⁻¹` is the *deflation* of `A`. -/
noncomputable def deflation (A : D[X]) (k : ℕ) : D[X] :=
  ∏ P ∈ (factors A.primPart).toFinset, P ^ ((factors A.primPart).count P - k)

omit [IsDomain D] in
open Classical in
/-- **Relation (1.11)** (§1.6): `A* · A⁻ = pp(A)` (up to associates) — the squarefree part times
the deflation recovers the primitive part, since `∏ Pᵢ · ∏ Pᵢ^(eᵢ−1) = ∏ Pᵢ^eᵢ`. -/
theorem squarefreePart_mul_deflation (A : D[X]) (hA : A.primPart ≠ 0) :
    Associated (squarefreePart A * deflation A 1) A.primPart := by
  rw [squarefreePart, deflation, ← Finset.prod_mul_distrib]
  have h : ∀ P ∈ (factors A.primPart).toFinset,
      P * P ^ ((factors A.primPart).count P - 1) = P ^ ((factors A.primPart).count P) := by
    intro P hP
    rw [← pow_succ']
    congr 1
    have hpos : 0 < (factors A.primPart).count P :=
      Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP)
    omega
  rw [Finset.prod_congr rfl h, ← Finset.prod_multiset_count]
  exact factors_prod hA

end Deflation

end DeepWiki.SymbolicIntegration
