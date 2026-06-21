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
/-- **Squarefree part** (§1.6, Definition 1.6.2): `A* = ∏ Pᵢ`, the product of the distinct
(normalized) prime factors of the primitive part `pp(A) = ∏ Pᵢ^eᵢ`. -/
noncomputable def squarefreePart (A : D[X]) : D[X] :=
  ∏ P ∈ (normalizedFactors A.primPart).toFinset, P

open Classical in
/-- **`k`-deflation** (§1.6, Definition 1.6.2): `A⁻ᵏ = ∏ Pᵢ^max(0, eᵢ−k)` (truncated exponents),
from `pp(A) = ∏ Pᵢ^eᵢ`. The `1`-deflation `A⁻ = A⁻¹` is the *deflation* of `A`. -/
noncomputable def deflation (A : D[X]) (k : ℕ) : D[X] :=
  ∏ P ∈ (normalizedFactors A.primPart).toFinset, P ^ ((normalizedFactors A.primPart).count P - k)

open Classical in
/-- **Relation (1.11)** (§1.6): `A* · A⁻ = pp(A)` (up to associates) — the squarefree part times
the deflation recovers the primitive part, since `∏ Pᵢ · ∏ Pᵢ^(eᵢ−1) = ∏ Pᵢ^eᵢ`. -/
theorem squarefreePart_mul_deflation (A : D[X]) (hA : A.primPart ≠ 0) :
    Associated (squarefreePart A * deflation A 1) A.primPart := by
  rw [squarefreePart, deflation, ← Finset.prod_mul_distrib]
  have h : ∀ P ∈ (normalizedFactors A.primPart).toFinset,
      P * P ^ ((normalizedFactors A.primPart).count P - 1)
        = P ^ ((normalizedFactors A.primPart).count P) := by
    intro P hP
    rw [← pow_succ']
    congr 1
    have hpos : 0 < (normalizedFactors A.primPart).count P :=
      Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP)
    omega
  rw [Finset.prod_congr rfl h, ← Finset.prod_multiset_count]
  exact prod_normalizedFactors hA

open Classical in
/-- **`A⁻⁰ = pp(A)`** (§1.6, the note preceding relation 1.11): the `0`-deflation recovers the
primitive part (up to associates), since `∏ Pᵢ^(eᵢ−0) = ∏ Pᵢ^eᵢ`. -/
theorem deflation_zero (A : D[X]) (hA : A.primPart ≠ 0) : Associated (deflation A 0) A.primPart := by
  rw [deflation]; simp only [Nat.sub_zero]
  rw [← Finset.prod_multiset_count]; exact prod_normalizedFactors hA

open Classical in
/-- Every deflation divides the primitive part: `A⁻ᵏ ∣ pp(A)` (each `Pᵢ^(eᵢ−k) ∣ Pᵢ^eᵢ`). -/
theorem deflation_dvd_primPart (A : D[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    deflation A k ∣ A.primPart := by
  have hdvd : deflation A k ∣ deflation A 0 := by
    rw [deflation, deflation]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun P _ => pow_dvd_pow P (by omega))
  exact hdvd.trans (deflation_zero A hA).dvd

open Classical in
/-- Every deflation is primitive: `A⁻ᵏ` is a divisor of the primitive `pp(A)`. (Used to identify
`pp(A⁻ᵏ)` with `A⁻ᵏ` when iterating the deflation, e.g. for relation 1.13.) -/
theorem deflation_isPrimitive (A : D[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    (deflation A k).IsPrimitive :=
  isPrimitive_of_dvd (isPrimitive_primPart A) (deflation_dvd_primPart A k hA)

open Classical in
/-- The factor multiplicities of a deflation are the truncated original ones:
`count Q (normalizedFactors A⁻ᵏ) = count Q (normalizedFactors pp(A)) − k`. (Canonical because
`normalizedFactors` is normalized — this is why the deflation uses `normalizedFactors`.) -/
theorem count_normalizedFactors_deflation (A : D[X]) (k : ℕ) (Q : D[X]) :
    (normalizedFactors (deflation A k)).count Q = (normalizedFactors A.primPart).count Q - k := by
  set M := normalizedFactors A.primPart with hM
  set M' := M - k • M.dedup with hM'
  have hcountM' : ∀ R, M'.count R = M.count R - k := by
    intro R
    rw [hM', Multiset.count_sub, Multiset.count_nsmul, Multiset.count_dedup]
    by_cases h : R ∈ M <;> simp [h, Multiset.count_eq_zero_of_notMem]
  have hsub : M' ≤ M := Multiset.sub_le_self _ _
  have hirr : ∀ R ∈ M', Irreducible R :=
    fun R hR => irreducible_of_normalized_factor R (Multiset.mem_of_le hsub hR)
  have hnorm : M'.map normalize = M' := by
    rw [Multiset.map_congr rfl
      (fun R hR => normalize_normalized_factor R (Multiset.mem_of_le hsub hR))]
    exact Multiset.map_id' M'
  have hsub'' : M'.toFinset ⊆ M.toFinset := by
    intro P hP
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, hcountM'] at hP
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]; omega
  have hdefl : deflation A k = M'.prod := by
    rw [deflation, ← hM, Finset.prod_multiset_count M']
    simp only [hcountM']
    exact (Finset.prod_subset hsub'' (fun P _ hP' => by
      rw [Multiset.mem_toFinset, ← Multiset.count_pos, hcountM'] at hP'
      rw [show M.count P - k = 0 by omega, pow_zero])).symm
  rw [hdefl, normalizedFactors_prod_eq M' hirr, hnorm, hcountM' Q]

open Classical in
/-- A deflation is never zero (a product of nonzero prime powers). -/
theorem deflation_ne_zero (A : D[X]) (k : ℕ) : deflation A k ≠ 0 := by
  rw [deflation, Finset.prod_ne_zero_iff]
  exact fun P hP =>
    pow_ne_zero _ (irreducible_of_normalized_factor P (Multiset.mem_toFinset.mp hP)).ne_zero

open Classical in
/-- **Relation (1.12)** (§1.6): `A⁻⁽ᵏ⁺¹⁾ = (A⁻ᵏ)⁻` — the `(k+1)`-deflation is the deflation of the
`k`-deflation. -/
theorem deflation_succ (A : D[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    deflation A (k + 1) = deflation (deflation A k) 1 := by
  conv_rhs => rw [deflation, (deflation_isPrimitive A k hA).primPart_eq]
  rw [deflation]
  simp only [count_normalizedFactors_deflation A k, Nat.sub_sub]
  refine (Finset.prod_subset (fun Q hQ => ?_) (fun P _ hP' => ?_)).symm
  · rw [Multiset.mem_toFinset, ← Multiset.count_pos, count_normalizedFactors_deflation A k] at hQ
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]; omega
  · rw [Multiset.mem_toFinset, ← Multiset.count_pos, count_normalizedFactors_deflation A k,
      not_lt] at hP'
    rw [show (normalizedFactors A.primPart).count P - (k + 1) = 0 by omega, pow_zero]

open Classical in
/-- **Relation (1.13)** (§1.6): `A⁻⁽ᵏ⁺¹⁾ = A⁻ᵏ / (A⁻ᵏ)*` — multiplicatively,
`(A⁻ᵏ)* · A⁻⁽ᵏ⁺¹⁾ = A⁻ᵏ` up to associates (relation 1.11 applied to `A⁻ᵏ`, via relation 1.12). -/
theorem squarefreePart_mul_deflation_succ (A : D[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    Associated (squarefreePart (deflation A k) * deflation A (k + 1)) (deflation A k) := by
  have hne : (deflation A k).primPart ≠ 0 := by
    rw [(deflation_isPrimitive A k hA).primPart_eq]; exact deflation_ne_zero A k
  have h := squarefreePart_mul_deflation (deflation A k) hne
  rwa [(deflation_isPrimitive A k hA).primPart_eq, ← deflation_succ A k hA] at h

end Deflation

end DeepWiki.SymbolicIntegration
