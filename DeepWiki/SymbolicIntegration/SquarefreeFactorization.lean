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
(Theorem 1.6.1(ii)); and the §1.7 squarefree criterion: over a characteristic-`0` field, `A` is
squarefree iff `gcd(A, dA/dx) = 1`. The deflation theory (relations 1.11–1.13) and the
squarefree-factorization parts (Lemma 1.7.1's equation 1.15) follow; the full Yun/Musser
squarefree-factorization routine is tracked as remaining library work. -/

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

/-- The squarefree criterion: over a characteristic-`0` field, `A` is squarefree iff it is coprime
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

open Classical in
/-- The squarefree part of a deflation is the product of the prime factors of `pp(A)` whose
multiplicity exceeds `k`: `(A⁻ᵏ)* = ∏_{eₚ > k} P`. -/
theorem squarefreePart_deflation (A : D[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    squarefreePart (deflation A k)
      = ∏ P ∈ (normalizedFactors A.primPart).toFinset.filter
          (fun P => k < (normalizedFactors A.primPart).count P), P := by
  rw [squarefreePart, (deflation_isPrimitive A k hA).primPart_eq]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext P
  rw [Multiset.mem_toFinset, ← Multiset.count_pos, count_normalizedFactors_deflation,
    Finset.mem_filter, Multiset.mem_toFinset, ← Multiset.count_pos]
  omega

open Classical in
/-- **Squarefree-factorization part** (§1.7, Lemma 1.7.1): `Aᵢ = ∏_{eₚ = i} P`, the product of the
prime factors of `pp(A)` of multiplicity exactly `i` (the `i`-th factor of the squarefree
factorization `pp(A) = ∏ᵢ Aᵢⁱ`). -/
noncomputable def sqfreeFactPart (A : D[X]) (i : ℕ) : D[X] :=
  ∏ P ∈ (normalizedFactors A.primPart).toFinset.filter
    (fun P => (normalizedFactors A.primPart).count P = i), P

open Classical in
/-- **Lemma 1.7.1 (ii)** (§1.7, equation 1.15): `Aᵢ = (A⁻⁽ⁱ⁻¹⁾)* / (A⁻ⁱ)*`, in multiplicative
form `(A⁻ⁱ)* · Aᵢ = (A⁻⁽ⁱ⁻¹⁾)*` (`1 ≤ i`). The squarefree parts of consecutive deflations differ
exactly by the factor `Aᵢ` of multiplicity `i`, since `{eₚ > i} ⊔ {eₚ = i} = {eₚ ≥ i}`. -/
theorem squarefreePart_deflation_mul_sqfreeFactPart (A : D[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    squarefreePart (deflation A i) * sqfreeFactPart A i = squarefreePart (deflation A (i - 1)) := by
  have hdisj : Disjoint ((normalizedFactors A.primPart).toFinset.filter
        (fun P => i < (normalizedFactors A.primPart).count P))
      ((normalizedFactors A.primPart).toFinset.filter
        (fun P => (normalizedFactors A.primPart).count P = i)) := by
    rw [Finset.disjoint_left]; intro P h1 h2
    rw [Finset.mem_filter] at h1 h2; omega
  rw [squarefreePart_deflation A i hA, squarefreePart_deflation A (i - 1) hA, sqfreeFactPart,
    ← Finset.prod_union hdisj, ← Finset.filter_or]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro P _
  omega

open Classical in
/-- **Lemma 1.7.1 (i)** (§1.7): `A⁻ᵏ = ∏ᵢ Aᵢ^(i−k)`, the deflation regrouped by multiplicity (the
product ranges over the multiplicities `i` occurring in `pp(A)`; terms with `i ≤ k` contribute `1`).
Proof: `Finset.prod_fiberwise_of_maps_to` partitions the prime factors of `pp(A)` by multiplicity. -/
theorem deflation_eq_prod_sqfreeFactPart (A : D[X]) (k : ℕ) :
    deflation A k = ∏ i ∈ (normalizedFactors A.primPart).toFinset.image
        (fun P => (normalizedFactors A.primPart).count P),
      (sqfreeFactPart A i) ^ (i - k) := by
  rw [deflation, ← Finset.prod_fiberwise_of_maps_to
        (t := (normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P))
        (g := fun P => (normalizedFactors A.primPart).count P)
        (fun P hP => Finset.mem_image_of_mem _ hP)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sqfreeFactPart, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun P hP => ?_
  rw [Finset.mem_filter] at hP
  rw [hP.2]

open Classical in
/-- **Lemma 1.7.1 (iii)** (§1.7): `pp(A) = ∏ᵢ Aᵢⁱ` (up to associates) — the squarefree
factorization of the primitive part. (The `k = 0` case of `deflation_eq_prod_sqfreeFactPart`
combined with `deflation_zero`.) -/
theorem primPart_associated_prod_sqfreeFactPart (A : D[X]) (hA : A.primPart ≠ 0) :
    Associated A.primPart (∏ i ∈ (normalizedFactors A.primPart).toFinset.image
      (fun P => (normalizedFactors A.primPart).count P), (sqfreeFactPart A i) ^ i) := by
  have h := deflation_eq_prod_sqfreeFactPart A 0
  simp only [Nat.sub_zero] at h
  rw [← h]
  exact (deflation_zero A hA).symm

open Classical in
/-- A squarefree-factorization part is never zero (a product of nonzero primes). -/
theorem sqfreeFactPart_ne_zero (A : D[X]) (i : ℕ) : sqfreeFactPart A i ≠ 0 := by
  rw [sqfreeFactPart, Finset.prod_ne_zero_iff]
  exact fun P hP => (irreducible_of_normalized_factor P
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).ne_zero

open Classical in
/-- **Lemma 1.7.1 (iii)** (§1.7), squarefree part: each `Aᵢ = ∏_{eₚ = i} P` is squarefree (a product
of distinct primes). -/
theorem sqfreeFactPart_squarefree (A : D[X]) (i : ℕ) : Squarefree (sqfreeFactPart A i) := by
  rw [sqfreeFactPart]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro P hP Q hQ hPQ
    have hPm := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1
    have hQm := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hQ).1
    apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
      (fun h => (irreducible_of_normalized_factor P hPm).ne_zero h.1)
    intro z hz hzP hzQ
    have hPQa : Associated P Q :=
      (hz.associated_of_dvd (irreducible_of_normalized_factor P hPm) hzP).symm.trans
        (hz.associated_of_dvd (irreducible_of_normalized_factor Q hQm) hzQ)
    apply hPQ
    have := normalize_eq_normalize_iff_associated.mpr hPQa
    rwa [normalize_normalized_factor P hPm, normalize_normalized_factor Q hQm] at this
  · intro P hP
    exact (irreducible_of_normalized_factor P
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).squarefree

open Classical in
/-- **Lemma 1.7.1 (iii)** (§1.7), pairwise coprimality: the `Aᵢ` are pairwise coprime in the gcd
sense — `gcd(Aᵢ, Aⱼ) ∈ D` for `i ≠ j` (stated as `IsRelPrime`, the non-Bézout notion, since `D[X]`
need not be a Bézout domain). Their prime supports `{eₚ = i}` and `{eₚ = j}` are disjoint. -/
theorem sqfreeFactPart_isRelPrime (A : D[X]) {i j : ℕ} (hij : i ≠ j) :
    IsRelPrime (sqfreeFactPart A i) (sqfreeFactPart A j) := by
  apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors (fun h => sqfreeFactPart_ne_zero A i h.1)
  intro z hz hzi hzj
  rw [sqfreeFactPart] at hzi hzj
  obtain ⟨P, hP, hzP⟩ := hz.prime.exists_mem_finset_dvd hzi
  obtain ⟨Q, hQ, hzQ⟩ := hz.prime.exists_mem_finset_dvd hzj
  have hPm := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1
  have hQm := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hQ).1
  have hPQa : Associated P Q :=
    (hz.associated_of_dvd (irreducible_of_normalized_factor P hPm) hzP).symm.trans
      (hz.associated_of_dvd (irreducible_of_normalized_factor Q hQm) hzQ)
  have hPeqQ : P = Q := by
    have := normalize_eq_normalize_iff_associated.mpr hPQa
    rwa [normalize_normalized_factor P hPm, normalize_normalized_factor Q hQm] at this
  have hi := (Finset.mem_filter.mp hP).2
  have hj := (Finset.mem_filter.mp hQ).2
  rw [hPeqQ] at hi
  exact hij (hi.symm.trans hj)

open Classical in
/-- The squarefree part of a deflation as a product of the higher squarefree-factorization parts:
`(A⁻ᵏ)* = ∏_{j > k} Aⱼ`. (The `(A⁻⁽ᵏ⁻¹⁾)* = ∏_{j ≥ k} Aⱼ` identity underlying Yun's eq 1.16.) -/
theorem squarefreePart_deflation_eq_prod (A : D[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    squarefreePart (deflation A k)
      = ∏ j ∈ ((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).filter (fun j => k < j),
        sqfreeFactPart A j := by
  rw [squarefreePart_deflation A k hA,
    ← Finset.prod_fiberwise_of_maps_to (t := ((normalizedFactors A.primPart).toFinset.image
        (fun P => (normalizedFactors A.primPart).count P)).filter (fun j => k < j))
        (g := fun P => (normalizedFactors A.primPart).count P) ?_]
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [sqfreeFactPart]
    refine Finset.prod_congr ?_ (fun _ _ => rfl)
    ext P
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at *
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, by rw [h3]; exact hj.2⟩, h3⟩
  · intro P hP
    rw [Finset.mem_filter] at hP ⊢
    exact ⟨Finset.mem_image_of_mem _ hP.1, hP.2⟩

open Classical in
/-- The derivative of a deflation in factored form (the analytic core of Yun's relation 1.17):
`d(A⁻ᵏ)/dx = ∑ₐ (∏_{b ≠ a} Aᵦ^(b−k)) · (a−k)·Aₐ^(a−k−1)·dAₐ/dx`, by the product and power rules on
`A⁻ᵏ = ∏ Aⱼ^(j−k)`. -/
theorem derivative_deflation (A : D[X]) (k : ℕ) :
    derivative (deflation A k)
      = ∑ a ∈ (normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P),
        (∏ b ∈ ((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).erase a, (sqfreeFactPart A b) ^ (b - k))
        * (C ((a - k : ℕ) : D) * (sqfreeFactPart A a) ^ (a - k - 1)
          * derivative (sqfreeFactPart A a)) := by
  rw [deflation_eq_prod_sqfreeFactPart A k, derivative_prod_finset]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [derivative_pow]

omit [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D] in
/-- Exponent-shifting helper for the Yun recurrence: `(∏ₗ gₗ^(l−j))·(∏_{l≠b} gₗ) =
gᵦ^(b−j)·∏_{l≠b} gₗ^(l−j+1)`. -/
private theorem prod_pow_sub_mul_prod_erase (g : ℕ → D[X]) (s : Finset ℕ) (j b : ℕ) (hb : b ∈ s) :
    (∏ l ∈ s, g l ^ (l - j)) * (∏ l ∈ s.erase b, g l)
      = g b ^ (b - j) * ∏ l ∈ s.erase b, g l ^ (l - j + 1) := by
  rw [← Finset.mul_prod_erase _ (fun l => g l ^ (l - j)) hb, mul_assoc, ← Finset.prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun l _ => (pow_succ (g l) (l - j)).symm)

open Classical in
/-- **Yun's polynomial `Yₖ`** (§1.7, equation 1.16): `Yₖ = ∑_{i≥k} (i−k+1)·(dAᵢ/dx)·∏_{l≥k, l≠i} Aₗ`,
the polynomial driving Yun's squarefree-factorization recurrence. -/
noncomputable def Yun (A : D[X]) (i : ℕ) : D[X] :=
  ∑ a ∈ ((normalizedFactors A.primPart).toFinset.image
      (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => i ≤ a),
    C ((a - i + 1 : ℕ) : D) * derivative (sqfreeFactPart A a)
      * ∏ l ∈ (((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => i ≤ a)).erase a,
        sqfreeFactPart A l

open Classical in
/-- **Lemma 1.7.2** (§1.7, equation 1.17): Yun's derivative recurrence
`d(A⁻⁽ⁱ⁻¹⁾)/dx = A⁻ⁱ · Yᵢ` (`1 ≤ i`). The product/power rule on `A⁻⁽ⁱ⁻¹⁾ = ∏ Aⱼ^(j−i+1)`
(`derivative_deflation`) regroups, term-by-term, into `A⁻ⁱ = ∏ Aⱼ^(j−i)` times Yun's `Yᵢ`. -/
theorem derivative_deflation_pred (A : D[X]) (i : ℕ) (hi : 1 ≤ i) :
    derivative (deflation A (i - 1)) = deflation A i * Yun A i := by
  set I := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with hI
  set f := sqfreeFactPart A with hf
  set I' := I.filter (fun a => i ≤ a) with hI'
  have hdefi : deflation A i = ∏ l ∈ I', f l ^ (l - i) := by
    rw [deflation_eq_prod_sqfreeFactPart A i, ← hI, ← hf]
    refine (Finset.prod_subset (Finset.filter_subset _ _) (fun l hlI hl => ?_)).symm
    rw [Finset.mem_filter, not_and] at hl
    rw [show l - i = 0 from by have := hl hlI; omega, pow_zero]
  rw [derivative_deflation A (i - 1), ← hI, ← hf, hdefi, Yun, ← hI, ← hf, ← hI', Finset.mul_sum,
    ← Finset.sum_subset (Finset.filter_subset (fun a => i ≤ a) I) (fun a haI ha => ?_)]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    have hinner : ∏ b ∈ I.erase a, f b ^ (b - (i - 1)) = ∏ b ∈ I'.erase a, f b ^ (b - i + 1) := by
      refine (Finset.prod_subset (Finset.erase_subset_erase a (Finset.filter_subset _ _))
        (fun b hbI hb => ?_)).symm.trans (Finset.prod_congr rfl fun b hb => ?_)
      · rw [Finset.mem_erase] at hbI
        rw [Finset.mem_erase, Finset.mem_filter, not_and] at hb
        rw [show b - (i - 1) = 0 from by
          have : ¬ i ≤ b := fun h => (hb hbI.1) ⟨hbI.2, h⟩
          omega, pow_zero]
      · rw [Finset.mem_erase, Finset.mem_filter] at hb
        rw [show b - (i - 1) = b - i + 1 from by omega]
    rw [show a - (i - 1) = a - i + 1 from by omega, show a - i + 1 - 1 = a - i from by omega, hinner]
    linear_combination (-(C ((a - i + 1 : ℕ) : D) * derivative (f a)))
      * prod_pow_sub_mul_prod_erase f I' i a (Finset.mem_filter.mpr ha)
  · rw [Finset.mem_filter, not_and] at ha
    rw [show a - (i - 1) = 0 from by have := ha haI; omega]
    simp

open Classical in
/-- The derivative of a squarefree part in factored form (toward Yun's relation 1.18):
`d(A⁻ᵏ)*/dx = ∑_{a > k} (∏_{b > k, b ≠ a} Aᵦ) · dAₐ/dx`, by the product rule on `(A⁻ᵏ)* = ∏_{j > k} Aⱼ`. -/
theorem derivative_squarefreePart_deflation (A : D[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    derivative (squarefreePart (deflation A k))
      = ∑ a ∈ ((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => k < a),
        (∏ b ∈ (((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => k < a)).erase a,
          sqfreeFactPart A b) * derivative (sqfreeFactPart A a) := by
  rw [squarefreePart_deflation_eq_prod A k hA, derivative_prod_finset]

end Deflation

end DeepWiki.SymbolicIntegration
