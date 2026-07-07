import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries
import DeepWiki.SymbolicIntegration.Core.Polynomial.SquarefreeDerivative

/-! # Squarefree factorization via the derivative criterion
The squarefree part and deflations of `A ∈ D[x]` are computed by gcds with `dA/dx`, since a prime
factor `P` divides `dA/dx` exactly once less than it divides `A`. Includes the deflation theory,
the squarefree-factorization parts, and the executable factorization algorithm with its
correctness. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- Over a characteristic-`0` field, `A` is squarefree iff `IsCoprime A (dA/dx)`. -/
theorem squarefree_iff_isCoprime_derivative {K : Type*} [Field K] [CharZero K] {A : K[X]} :
    Squarefree A ↔ IsCoprime A (derivative A) :=
  PerfectField.separable_iff_squarefree.symm.trans (separable_def A)

section Deflation
open UniqueFactorizationMonoid
variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D]

open Classical in
/-- Squarefree part `A* = ∏ Pᵢ`: the product of the distinct normalized prime factors of the
primitive part `pp(A)`. -/
noncomputable def squarefreePart (A : D[X]) : D[X] :=
  ∏ P ∈ (normalizedFactors A.primPart).toFinset, P

open Classical in
/-- `k`-deflation `A⁻ᵏ = ∏ Pᵢ^max(0, eᵢ−k)`: the primitive part with each factor exponent
truncated by `k`. -/
noncomputable def deflation (A : D[X]) (k : ℕ) : D[X] :=
  ∏ P ∈ (normalizedFactors A.primPart).toFinset, P ^ ((normalizedFactors A.primPart).count P - k)

open Classical in
/-- `A* · A⁻¹` is associated to `pp(A)`: the squarefree part times the deflation recovers the
primitive part. -/
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
/-- The `0`-deflation `A⁻⁰` is associated to the primitive part `pp(A)`. -/
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
/-- Every deflation `A⁻ᵏ` is primitive (a divisor of the primitive `pp(A)`). -/
theorem deflation_isPrimitive (A : D[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    (deflation A k).IsPrimitive :=
  isPrimitive_of_dvd (isPrimitive_primPart A) (deflation_dvd_primPart A k hA)

open Classical in
/-- The factor multiplicities of a deflation are the truncated originals:
`count Q (normalizedFactors A⁻ᵏ) = count Q (normalizedFactors pp(A)) − k`. -/
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
/-- `A⁻⁽ᵏ⁺¹⁾ = (A⁻ᵏ)⁻¹`: the `(k+1)`-deflation is the deflation of the `k`-deflation. -/
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
/-- `(A⁻ᵏ)* · A⁻⁽ᵏ⁺¹⁾` is associated to `A⁻ᵏ`: the squarefree part of a deflation times the next
deflation recovers it. -/
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
/-- Squarefree-factorization part `Aᵢ = ∏_{eₚ = i} P`: the product of the prime factors of `pp(A)`
of multiplicity exactly `i`. -/
noncomputable def sqfreeFactPart (A : D[X]) (i : ℕ) : D[X] :=
  ∏ P ∈ (normalizedFactors A.primPart).toFinset.filter
    (fun P => (normalizedFactors A.primPart).count P = i), P

open Classical in
/-- `(A⁻ⁱ)* · Aᵢ = (A⁻⁽ⁱ⁻¹⁾)*` (`1 ≤ i`): consecutive deflation squarefree parts differ exactly by
the multiplicity-`i` factor `Aᵢ`. -/
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
/-- `A⁻ᵏ = ∏ᵢ Aᵢ^(i−k)`: the deflation regrouped by multiplicity `i` (terms with `i ≤ k`
contribute `1`). -/
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
/-- `pp(A)` is associated to `∏ᵢ Aᵢⁱ`: the squarefree factorization of the primitive part. -/
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
/-- Each squarefree-factorization part `Aᵢ` is squarefree (a product of distinct primes). -/
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
/-- The squarefree-factorization parts are pairwise relatively prime: `IsRelPrime (Aᵢ) (Aⱼ)`
for `i ≠ j`. -/
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

open UniqueFactorizationMonoid in
open Classical in
/-- Any associate of `sqfreeFactPart A j` is squarefree. -/
theorem squarefree_of_associated_sqfreeFactPart {K : Type*} [Field K]
    {V : K[X]} (A : K[X]) (j : ℕ) (h : Associated V (sqfreeFactPart A j)) :
    Squarefree V :=
  h.squarefree_iff.mpr (sqfreeFactPart_squarefree A j)

open UniqueFactorizationMonoid in
open Classical in
/-- Associates of distinct squarefree-factorization parts are relatively prime. -/
theorem isRelPrime_of_associated_sqfreeFactPart {K : Type*} [Field K]
    {V W : K[X]} (A : K[X]) {i j : ℕ} (hij : i ≠ j)
    (hV : Associated V (sqfreeFactPart A i)) (hW : Associated W (sqfreeFactPart A j)) :
    IsRelPrime V W :=
  ((sqfreeFactPart_isRelPrime A hij).of_dvd_left hV.dvd).of_dvd_right hW.dvd

open Classical in
/-- The squarefree part of a deflation as a product of higher parts: `(A⁻ᵏ)* = ∏_{j > k} Aⱼ`. -/
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
/-- The derivative of a deflation in factored form:
`d(A⁻ᵏ)/dx = ∑ₐ (∏_{b ≠ a} Aᵦ^(b−k)) · (a−k)·Aₐ^(a−k−1)·dAₐ/dx`. -/
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
/-- Exponent-shifting helper: `(∏ₗ gₗ^(l−j))·(∏_{l≠b} gₗ) = gᵦ^(b−j)·∏_{l≠b} gₗ^(l−j+1)`. -/
private theorem prod_pow_sub_mul_prod_erase (g : ℕ → D[X]) (s : Finset ℕ) (j b : ℕ) (hb : b ∈ s) :
    (∏ l ∈ s, g l ^ (l - j)) * (∏ l ∈ s.erase b, g l)
      = g b ^ (b - j) * ∏ l ∈ s.erase b, g l ^ (l - j + 1) := by
  rw [← Finset.mul_prod_erase _ (fun l => g l ^ (l - j)) hb, mul_assoc, ← Finset.prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun l _ => (pow_succ (g l) (l - j)).symm)

open Classical in
/-- The polynomial `Yₖ = ∑_{i≥k} (i−k+1)·(dAᵢ/dx)·∏_{l≥k, l≠i} Aₗ` driving the
squarefree-factorization recurrence. -/
noncomputable def Yun (A : D[X]) (i : ℕ) : D[X] :=
  ∑ a ∈ ((normalizedFactors A.primPart).toFinset.image
      (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => i ≤ a),
    C ((a - i + 1 : ℕ) : D) * derivative (sqfreeFactPart A a)
      * ∏ l ∈ (((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => i ≤ a)).erase a,
        sqfreeFactPart A l

open Classical in
/-- Derivative recurrence `d(A⁻⁽ⁱ⁻¹⁾)/dx = A⁻ⁱ · Yᵢ` (`1 ≤ i`). -/
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
/-- The derivative of a squarefree part in factored form:
`d(A⁻ᵏ)*/dx = ∑_{a > k} (∏_{b > k, b ≠ a} Aᵦ) · dAₐ/dx`. -/
theorem derivative_squarefreePart_deflation (A : D[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    derivative (squarefreePart (deflation A k))
      = ∑ a ∈ ((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => k < a),
        (∏ b ∈ (((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => k < a)).erase a,
          sqfreeFactPart A b) * derivative (sqfreeFactPart A a) := by
  rw [squarefreePart_deflation_eq_prod A k hA, derivative_prod_finset]

open Classical in
/-- `Yᵢ − d(A⁻⁽ⁱ⁻¹⁾)*/dx = Aᵢ·Y_{i+1}` (`1 ≤ i`). -/
theorem Yun_sub_derivative_squarefreePart (A : D[X]) (i : ℕ) (hi : 1 ≤ i) (hA : A.primPart ≠ 0) :
    Yun A i - derivative (squarefreePart (deflation A (i - 1)))
      = sqfreeFactPart A i * Yun A (i + 1) := by
  set I := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with hI
  set f := sqfreeFactPart A with hf
  have hfi1 : i ∉ I → f i = 1 := by
    intro hiI
    have hempty : (normalizedFactors A.primPart).toFinset.filter
        (fun P => (normalizedFactors A.primPart).count P = i) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun P hP hc => hiI (hc ▸ Finset.mem_image_of_mem _ hP))
    rw [hf, sqfreeFactPart, hempty, Finset.prod_empty]
  have hII : (I.filter (fun a => i ≤ a)).erase i = I.filter (fun a => i + 1 ≤ a) := by
    ext x; simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hne, hxI, hle⟩; exact ⟨hxI, by omega⟩
    · rintro ⟨hxI, hle⟩; exact ⟨by omega, hxI, by omega⟩
  have hfilt : I.filter (fun a => i - 1 < a) = I.filter (fun a => i ≤ a) := by
    ext x; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxI, h⟩; exact ⟨hxI, by omega⟩
    · rintro ⟨hxI, h⟩; exact ⟨hxI, by omega⟩
  have hregroup : ∀ a ∈ I.filter (fun a => i + 1 ≤ a),
      ∏ l ∈ (I.filter (fun a => i ≤ a)).erase a, f l
        = f i * ∏ l ∈ (I.filter (fun a => i + 1 ≤ a)).erase a, f l := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haI, hai⟩ := ha
    by_cases hiI : i ∈ I
    · have hierase : i ∈ (I.filter (fun a => i ≤ a)).erase a := by
        rw [Finset.mem_erase, Finset.mem_filter]; exact ⟨by omega, hiI, le_refl i⟩
      have hset : ((I.filter (fun a => i ≤ a)).erase a).erase i
          = (I.filter (fun a => i + 1 ≤ a)).erase a := by
        ext x; simp only [Finset.mem_erase, Finset.mem_filter]
        constructor
        · rintro ⟨hxi, hxa, hxI, hle⟩; exact ⟨hxa, hxI, by omega⟩
        · rintro ⟨hxa, hxI, hle⟩; exact ⟨by omega, hxa, hxI, by omega⟩
      rw [← Finset.mul_prod_erase _ f hierase, hset]
    · rw [hfi1 hiI, one_mul]
      refine Finset.prod_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨hxa, hxI, hle⟩
        exact ⟨hxa, hxI, by have : x ≠ i := fun h => hiI (h ▸ hxI); omega⟩
      · rintro ⟨hxa, hxI, hle⟩; exact ⟨hxa, hxI, by omega⟩
  rw [Yun, ← hI, ← hf, derivative_squarefreePart_deflation A (i - 1) hA, ← hI, ← hf, hfilt,
    Yun, ← hI, ← hf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun a _ => by
    show C ((a - i + 1 : ℕ) : D) * derivative (f a)
          * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase a, f l
        - (∏ b ∈ (I.filter (fun a => i ≤ a)).erase a, f b) * derivative (f a)
      = C ((a - i : ℕ) : D) * derivative (f a)
          * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase a, f l
    have hc : C ((a - i + 1 : ℕ) : D) - 1 = C ((a - i : ℕ) : D) := by
      rw [show ((a - i + 1 : ℕ) : D) = ((a - i : ℕ) : D) + 1 from by push_cast; ring,
        map_add, map_one]; ring
    linear_combination (derivative (f a)
      * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase a, f l) * hc)]
  rw [← Finset.sum_erase (I.filter (fun a => i ≤ a))
      (show C ((i - i : ℕ) : D) * derivative (f i)
          * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase i, f l = 0 from by
        rw [Nat.sub_self, Nat.cast_zero, map_zero]; ring), hII]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_filter] at ha
  rw [(by omega : (a - (i + 1) + 1 : ℕ) = a - i), hregroup a (Finset.mem_filter.mpr ha)]
  ring

end Deflation

section GcdField

open UniqueFactorizationMonoid

variable {K : Type*} [Field K] [CharZero K]

open Classical

/-- Over a characteristic-`0` field, `(A⁻⁽ⁱ⁻¹⁾)*` and `Yᵢ` are relatively prime:
`IsRelPrime ((A⁻⁽ⁱ⁻¹⁾)*) (Yᵢ)` (`1 ≤ i`). -/
theorem isRelPrime_squarefreePart_Yun (A : K[X]) (i : ℕ) (hi : 1 ≤ i) (hA : A.primPart ≠ 0) :
    IsRelPrime (squarefreePart (deflation A (i - 1))) (Yun A i) := by
  set I := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with hI
  set f := sqfreeFactPart A with hf
  have hsp := squarefreePart_deflation_eq_prod A (i - 1) hA
  rw [← hI, ← hf] at hsp
  have hne : squarefreePart (deflation A (i - 1)) ≠ 0 := by
    rw [hsp, Finset.prod_ne_zero_iff]; exact fun l _ => sqfreeFactPart_ne_zero A l
  rw [isRelPrime_iff_no_prime_factors hne]
  intro P hPsp hPY hPp
  rw [hsp, hPp.dvd_finsetProd_iff] at hPsp
  obtain ⟨a, haI, hPa⟩ := hPsp
  rw [Finset.mem_filter] at haI
  have haI' : a ∈ I.filter (fun a => i ≤ a) := Finset.mem_filter.mpr ⟨haI.1, by omega⟩
  have hPfa' : ¬ P ∣ derivative (f a) := by
    obtain ⟨m, hm⟩ := hPa
    have hPm : ¬ P ∣ m := by
      rintro ⟨n, hmn⟩
      exact hPp.not_unit ((sqfreeFactPart_squarefree A a) P ⟨n, by rw [← hf, hm, hmn]; ring⟩)
    have hsep : P.Separable := (hPp.irreducible).separable
    have hPP' : ¬ P ∣ derivative P := fun h => hPp.not_unit (hsep.isUnit_of_dvd' (dvd_refl P) h)
    intro hPfad
    rw [hm, derivative_mul] at hPfad
    have hd : P ∣ derivative P * m :=
      (dvd_add_left (dvd_mul_right P (derivative m))).mp hPfad
    rcases hPp.dvd_mul.mp hd with h | h
    · exact hPP' h
    · exact hPm h
  have hPfl : ∀ l, l ≠ a → ¬ P ∣ f l :=
    fun l hla hPl => hPp.not_unit (sqfreeFactPart_isRelPrime A hla hPl hPa)
  set g : ℕ → K[X] := fun b => C ((b - i + 1 : ℕ) : K) * derivative (f b)
    * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase b, f l with hg
  have hga : ¬ P ∣ g a := by
    intro hh
    rcases hPp.dvd_mul.mp hh with h1 | h2
    · rcases hPp.dvd_mul.mp h1 with hc | hd
      · exact hPp.not_unit (isUnit_of_dvd_unit hc
          (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))))
      · exact hPfa' hd
    · rw [hPp.dvd_finsetProd_iff] at h2
      obtain ⟨l, hl, hPl⟩ := h2
      exact hPfl l (Finset.mem_erase.mp hl).1 hPl
  have hPS : P ∣ ∑ b ∈ (I.filter (fun a => i ≤ a)).erase a, g b := by
    refine Finset.dvd_sum (fun b hb => ?_)
    have hab : a ∈ (I.filter (fun a => i ≤ a)).erase b :=
      Finset.mem_erase.mpr ⟨((Finset.mem_erase.mp hb).1).symm, haI'⟩
    exact hg ▸ dvd_mul_of_dvd_right (hPa.trans (Finset.dvd_prod_of_mem f hab)) _
  rw [Yun, ← hI, ← hf, ← Finset.add_sum_erase _ g haI'] at hPY
  exact hga ((dvd_add_left hPS).mp hPY)

/-- The Yun gcd step extracts the `i`-th squarefree-factorization part. -/
theorem gcd_radical_yunStep_assoc (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    Associated
      (gcd (squarefreePart (deflation A (i - 1)))
        (Yun A i - derivative (squarefreePart (deflation A (i - 1)))))
      (sqfreeFactPart A i) := by
  have hsplit := squarefreePart_deflation_mul_sqfreeFactPart A i hi hA
  have hd := Yun_sub_derivative_squarefreePart A i hi hA
  set V := sqfreeFactPart A i with hV
  set S' := squarefreePart (deflation A i) with hS'
  set Y := Yun A (i + 1) with hY
  have hS : squarefreePart (deflation A (i - 1)) = V * S' := by
    rw [hV, hS', mul_comm]; exact hsplit.symm
  rw [hd, hS]
  refine (gcd_mul_left' V S' Y).trans ?_
  have hrp : IsRelPrime S' Y := by
    have h := isRelPrime_squarefreePart_Yun A (i + 1) (by omega) hA
    rwa [Nat.add_sub_cancel] at h
  have hunit : IsUnit (gcd S' Y) := gcd_isUnit_iff_isRelPrime.mpr hrp
  have : Associated (V * gcd S' Y) (V * 1) :=
    (associated_one_iff_isUnit.mpr hunit).mul_left V
  rwa [mul_one] at this

/-! ### The abstract Yun loop state and its recurrence -/

open Classical in
/-- Abstract Yun numerator `Babs A i = squarefreePart (deflation A (i−1))`. -/
noncomputable def Babs {K : Type*} [Field K] (A : K[X]) (i : ℕ) : K[X] :=
  squarefreePart (deflation A (i - 1))

open Classical in
/-- Abstract Yun derivative-polynomial `Dabs A i = Yun A i − (Babs A i)′`. -/
noncomputable def Dabs {K : Type*} [Field K] (A : K[X]) (i : ℕ) : K[X] :=
  Yun A i - derivative (squarefreePart (deflation A (i - 1)))

open Classical in
/-- `Babs A i = sqfreeFactPart A i * Babs A (i+1)`. -/
theorem Babs_eq_mul {K : Type*} [Field K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    Babs A i = sqfreeFactPart A i * Babs A (i + 1) := by
  rw [Babs, Babs, Nat.add_sub_cancel, ← squarefreePart_deflation_mul_sqfreeFactPart A i hi hA,
    mul_comm]

open Classical in
/-- `Dabs A i = sqfreeFactPart A i * Yun A (i+1)`. -/
theorem Dabs_eq_mul {K : Type*} [Field K] [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    Dabs A i = sqfreeFactPart A i * Yun A (i + 1) := by
  rw [Dabs]; exact Yun_sub_derivative_squarefreePart A i hi hA

open UniqueFactorizationMonoid in
open Classical in
/-- `gcd (Babs A i) (Dabs A i) = normalize (sqfreeFactPart A i)`. -/
theorem gcd_Babs_Dabs {K : Type*} [Field K] [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    gcd (Babs A i) (Dabs A i) = normalize (sqfreeFactPart A i) := by
  rw [Babs_eq_mul A i hi hA, Dabs_eq_mul A i hi hA, gcd_mul_left]
  have hrp : IsRelPrime (Babs A (i + 1)) (Yun A (i + 1)) := by
    have h := isRelPrime_squarefreePart_Yun A (i + 1) (by omega) hA
    rw [Babs]; rwa [Nat.add_sub_cancel] at h
  have hunit : IsUnit (gcd (Babs A (i + 1)) (Yun A (i + 1))) :=
    gcd_isUnit_iff_isRelPrime.mpr hrp
  rw [(normalize_eq_one.mpr hunit ▸ (normalize_gcd (Babs A (i + 1)) (Yun A (i + 1))).symm :
    gcd (Babs A (i + 1)) (Yun A (i + 1)) = 1), mul_one]

open Classical in
/-- `p = C p.leadingCoeff * normalize p` over a field. -/
theorem self_eq_C_leadingCoeff_mul_normalize {K : Type*} [Field K] (p : K[X]) (hp : p ≠ 0) :
    p = Polynomial.C p.leadingCoeff * normalize p := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hcn : ((normUnit p.leadingCoeff : K) : K) = p.leadingCoeff⁻¹ := by
    simp [normUnit, hlc]
  rw [normalize_apply, Polynomial.coe_normUnit, hcn]
  rw [show Polynomial.C p.leadingCoeff * (p * Polynomial.C p.leadingCoeff⁻¹)
        = (Polynomial.C p.leadingCoeff * Polynomial.C p.leadingCoeff⁻¹) * p from by ring,
    ← map_mul, mul_inv_cancel₀ hlc, map_one, one_mul]

open Classical in
/-- The Yun loop invariant: `(b,d)` is a common nonzero constant multiple of `(Babs A i,Dabs A i)`. -/
def YunInv {K : Type*} [Field K] (A : K[X]) (i : ℕ) (b d : K[X]) : Prop :=
  ∃ c : K, c ≠ 0 ∧ b = Polynomial.C c * Babs A i ∧ d = Polynomial.C c * Dabs A i

open UniqueFactorizationMonoid in
open Classical in
/-- One Yun step preserves `YunInv` and emits `normalize (sqfreeFactPart A i)`. -/
theorem yunStep_preserves {K : Type*} [Field K] [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) {b d : K[X]} (hinv : YunInv A i b d) :
    gcd b d = normalize (sqfreeFactPart A i) ∧
      YunInv A (i + 1) (b / gcd b d) (d / gcd b d - derivative (b / gcd b d)) := by
  obtain ⟨c, hc, hb, hd⟩ := hinv
  set V := sqfreeFactPart A i with hV
  have hV0 : V ≠ 0 := sqfreeFactPart_ne_zero A i
  set w := V.leadingCoeff with hw
  have hw0 : w ≠ 0 := leadingCoeff_ne_zero.mpr hV0
  set Vn := normalize V with hVn
  have hVn0 : Vn ≠ 0 := by rw [hVn]; simpa using hV0
  have hgcd : gcd b d = Vn := by
    rw [hb, hd, gcd_mul_left, normalize_eq_one.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)),
      one_mul, gcd_Babs_Dabs A i hi hA, ← hV, ← hVn]
  have hVeq : V = Polynomial.C w * Vn := self_eq_C_leadingCoeff_mul_normalize V hV0
  have hbfact : b = Vn * (Polynomial.C (c * w) * Babs A (i + 1)) := by
    rw [hb, Babs_eq_mul A i hi hA, ← hV, hVeq, map_mul]; ring
  have hdfact : d = Vn * (Polynomial.C (c * w) * Yun A (i + 1)) := by
    rw [hd, Dabs_eq_mul A i hi hA, ← hV, hVeq, map_mul]; ring
  have hb' : b / gcd b d = Polynomial.C (c * w) * Babs A (i + 1) := by
    rw [hgcd, hbfact, mul_div_cancel_left₀ _ hVn0]
  have hd' : d / gcd b d = Polynomial.C (c * w) * Yun A (i + 1) := by
    rw [hgcd, hdfact, mul_div_cancel_left₀ _ hVn0]
  refine ⟨hgcd, c * w, mul_ne_zero hc hw0, hb', ?_⟩
  rw [hd', hb', derivative_C_mul, Dabs, Nat.add_sub_cancel, Babs, Nat.add_sub_cancel, mul_sub]

open UniqueFactorizationMonoid in
open Classical in
/-- The factor emitted by one Yun step is associated to the `i`-th squarefree part. -/
theorem yunStep_emit_assoc {K : Type*} [Field K] [CharZero K] (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) {b d : K[X]} (hinv : YunInv A i b d) :
    Associated (gcd b d) (sqfreeFactPart A i) := by
  rw [(yunStep_preserves A i hi hA hinv).1]
  exact normalize_associated (sqfreeFactPart A i)

/-! ### The abstract Yun loop and its factor products -/

open Classical in
/-- Abstract Yun loop emitting `gcd b d` and recursing on the deflated pair. -/
noncomputable def yunLoopAbs {K : Type*} [Field K] (A : K[X]) : K[X] × K[X] → ℕ → ℕ → List K[X]
  | _, _, 0 => []
  | (b, d), i, (n + 1) =>
      gcd b d :: yunLoopAbs A (b / gcd b d, d / gcd b d - derivative (b / gcd b d)) (i + 1) n

open Classical in
/-- The abstract Yun loop is factorwise associated to consecutive squarefree parts. -/
theorem yunLoopAbs_forall₂ {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA : A.primPart ≠ 0) :
    ∀ (n i : ℕ) (b d : K[X]), 1 ≤ i → YunInv A i b d →
      List.Forall₂ Associated (yunLoopAbs A (b, d) i n)
        ((List.range n).map (fun j => sqfreeFactPart A (i + j))) := by
  intro n
  induction n with
  | zero => intro i b d _ _; simp [yunLoopAbs]
  | succ n ih =>
    intro i b d hi hinv
    rw [yunLoopAbs, List.range_succ_eq_map, List.map_cons]
    refine List.Forall₂.cons (yunStep_emit_assoc A i hi hA hinv) ?_
    have hstep := (yunStep_preserves A i hi hA hinv).2
    have htail := ih (i + 1) (b / gcd b d) (d / gcd b d - derivative (b / gcd b d))
      (by omega) hstep
    rw [List.map_map]
    have hreindex : (List.range n).map ((fun j => sqfreeFactPart A (i + j)) ∘ Nat.succ)
        = (List.range n).map (fun j => sqfreeFactPart A ((i + 1) + j)) :=
      List.map_congr_left (fun j _ => by simp only [Function.comp_apply]; congr 1; omega)
    rw [hreindex]
    exact htail

open Classical in
/-- Every factor emitted by the abstract Yun loop is squarefree. -/
theorem yunLoopAbs_squarefree {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) :
    ∀ (n i : ℕ) (b d : K[X]), 1 ≤ i → YunInv A i b d →
      ∀ V ∈ yunLoopAbs A (b, d) i n, Squarefree V := by
  intro n
  induction n with
  | zero => intro i b d _ _ V hV; simp [yunLoopAbs] at hV
  | succ n ih =>
    intro i b d hi hinv V hV
    rw [yunLoopAbs, List.mem_cons] at hV
    rcases hV with rfl | hV
    · exact squarefree_of_associated_sqfreeFactPart A i (yunStep_emit_assoc A i hi hA hinv)
    · exact ih (i + 1) _ _ (by omega) (yunStep_preserves A i hi hA hinv).2 V hV

open Classical in
/-- Distinct-position factors emitted by the abstract Yun loop are relatively prime. -/
theorem yunLoopAbs_pairwise_isRelPrime {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) (n i : ℕ) (b d : K[X]) (hi : 1 ≤ i) (hinv : YunInv A i b d)
    {p q : ℕ} (hpq : p ≠ q) (hp : p < (yunLoopAbs A (b, d) i n).length)
    (hq : q < (yunLoopAbs A (b, d) i n).length) :
    IsRelPrime ((yunLoopAbs A (b, d) i n).get ⟨p, hp⟩)
      ((yunLoopAbs A (b, d) i n).get ⟨q, hq⟩) := by
  have hF := yunLoopAbs_forall₂ A hA n i b d hi hinv
  have hlen : (yunLoopAbs A (b, d) i n).length
      = ((List.range n).map (fun j => sqfreeFactPart A (i + j))).length := hF.length_eq
  have hp' : p < ((List.range n).map (fun j => sqfreeFactPart A (i + j))).length := hlen ▸ hp
  have hq' : q < ((List.range n).map (fun j => sqfreeFactPart A (i + j))).length := hlen ▸ hq
  have hAp : Associated ((yunLoopAbs A (b, d) i n).get ⟨p, hp⟩) (sqfreeFactPart A (i + p)) := by
    have h := hF.get hp hp'
    simpa using h
  have hAq : Associated ((yunLoopAbs A (b, d) i n).get ⟨q, hq⟩) (sqfreeFactPart A (i + q)) := by
    have h := hF.get hq hq'
    simpa using h
  exact isRelPrime_of_associated_sqfreeFactPart A (by omega : i + p ≠ i + q) hAp hAq

open Classical in
/-- The abstract Yun loop product is associated to the product of consecutive squarefree parts. -/
theorem yunLoopAbs_prod_assoc {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) (n i : ℕ) (b d : K[X]) (hi : 1 ≤ i) (hinv : YunInv A i b d) :
    Associated (yunLoopAbs A (b, d) i n).prod
      (((List.range n).map (fun j => sqfreeFactPart A (i + j))).prod) :=
  List.rel_prod (R := Associated) (Associated.refl 1)
    (fun _ _ hx _ _ hy => hx.mul_mul hy) (yunLoopAbs_forall₂ A hA n i b d hi hinv)

open Classical in
/-- Powered product of `[e₀,e₁,…]`: `∏ₖ eₖ^(i+k)`. -/
noncomputable def prodPow {K : Type*} [Field K] (i : ℕ) : List K[X] → K[X]
  | [] => 1
  | e :: es => e ^ i * prodPow (i + 1) es

open Classical in
/-- `prodPow` respects factorwise association. -/
theorem prodPow_associated {K : Type*} [Field K] {l₁ l₂ : List K[X]}
    (h : List.Forall₂ Associated l₁ l₂) (i : ℕ) :
    Associated (prodPow i l₁) (prodPow i l₂) := by
  induction h generalizing i with
  | nil => exact Associated.refl _
  | cons hhd _ ih => exact hhd.pow_pow.mul_mul (ih (i + 1))

open Classical in
/-- `prodPow` over an appended singleton raises the last factor to `i + L.length`. -/
theorem prodPow_append_singleton {K : Type*} [Field K] (i : ℕ) (L : List K[X]) (x : K[X]) :
    prodPow i (L ++ [x]) = prodPow i L * x ^ (i + L.length) := by
  induction L generalizing i with
  | nil => simp [prodPow]
  | cons a L ih =>
    rw [List.cons_append, prodPow, prodPow, ih (i + 1), List.length_cons,
      show i + 1 + L.length = i + (L.length + 1) from by omega]
    ring

open Classical in
/-- `prodPow i` of a `range` map is the corresponding `Finset.range` powered product. -/
theorem prodPow_range_map_eq_finset {K : Type*} [Field K] (i n : ℕ) (f : ℕ → K[X]) :
    prodPow i ((List.range n).map f) = ∏ k ∈ Finset.range n, f k ^ (i + k) := by
  induction n with
  | zero => simp [prodPow]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, prodPow_append_singleton,
      ih, Finset.prod_range_succ, List.length_map, List.length_range]

open Classical UniqueFactorizationMonoid in
/-- `prodPow` over enough squarefree parts reconstructs `A.primPart` up to association. -/
theorem prodPow_one_sqfreeFactPart_range_associated {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) (n : ℕ)
    (hn : (normalizedFactors A.primPart).toFinset.sup
      (fun P => (normalizedFactors A.primPart).count P) ≤ n) :
    Associated (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) A.primPart := by
  rw [prodPow_range_map_eq_finset]
  have hIco : ∏ k ∈ Finset.range n, sqfreeFactPart A (1 + k) ^ (1 + k)
      = ∏ m ∈ Finset.Ico 1 (n + 1), sqfreeFactPart A m ^ m := by
    rw [Finset.prod_Ico_eq_prod_range]
    exact (Finset.prod_congr (by rw [Nat.add_sub_cancel]) (fun k _ => rfl)).symm
  set image := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with himage
  have hsub : image ⊆ Finset.Ico 1 (n + 1) := by
    intro i hi
    rw [himage, Finset.mem_image] at hi
    obtain ⟨P, hP, rfl⟩ := hi
    rw [Finset.mem_Ico]
    refine ⟨Multiset.one_le_count_iff_mem.mpr (Multiset.mem_toFinset.mp hP), ?_⟩
    have : (normalizedFactors A.primPart).count P ≤ (normalizedFactors A.primPart).toFinset.sup
        (fun P => (normalizedFactors A.primPart).count P) :=
      Finset.le_sup (f := fun P => (normalizedFactors A.primPart).count P) hP
    omega
  have hoff : ∀ m ∈ Finset.Ico 1 (n + 1), m ∉ image → sqfreeFactPart A m ^ m = 1 := by
    intro m _ hm
    have h1 : sqfreeFactPart A m = 1 := by
      rw [sqfreeFactPart, Finset.prod_eq_one]
      intro P hP
      rw [Finset.mem_filter] at hP
      exact absurd (hP.2 ▸ Finset.mem_image_of_mem _ hP.1) hm
    rw [h1, one_pow]
  rw [hIco, ← Finset.prod_subset hsub hoff]
  exact (primPart_associated_prod_sqfreeFactPart A hA).symm

open Classical in
/-- The powered product of the abstract Yun loop matches the powered squarefree parts up to association. -/
theorem yunLoopAbs_prodPow_assoc {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA : A.primPart ≠ 0) (n i : ℕ) (b d : K[X]) (hi : 1 ≤ i) (hinv : YunInv A i b d) :
    Associated (prodPow i (yunLoopAbs A (b, d) i n))
      (prodPow i ((List.range n).map (fun j => sqfreeFactPart A (i + j)))) :=
  prodPow_associated (yunLoopAbs_forall₂ A hA n i b d hi hinv) i

/-- Over a characteristic-`0` field: if `Pʲ ∣ p` exactly (`P^{j+1} ∤ p`) for irreducible `P` and
`j ≥ 1`, then `Pʲ ∤ dp/dx`. -/
private theorem pow_not_dvd_derivative_aux (p P : K[X]) (j : ℕ) (hj : 1 ≤ j) (hP : Irreducible P)
    (hdvd : P ^ j ∣ p) (hndvd : ¬ P ^ (j + 1) ∣ p) : ¬ P ^ j ∣ derivative p := by
  obtain ⟨g, hg⟩ := hdvd
  have hPg : ¬ P ∣ g := fun ⟨h, hgh⟩ => hndvd ⟨h, by rw [hg, hgh]; ring⟩
  rw [hg]
  intro hdvd2
  rw [derivative_mul, derivative_pow] at hdvd2
  have hPne : P ^ (j - 1) ≠ 0 := pow_ne_zero _ hP.ne_zero
  have hsplit : P ^ j = P ^ (j - 1) * P := by rw [← pow_succ]; congr 1; omega
  have h1 : P ^ j ∣ C (j : K) * P ^ (j - 1) * derivative P * g :=
    (dvd_add_left (dvd_mul_right (P ^ j) (derivative g))).mp hdvd2
  rw [show C (j : K) * P ^ (j - 1) * derivative P * g
      = P ^ (j - 1) * (C (j : K) * derivative P * g) from by ring, hsplit,
    mul_dvd_mul_iff_left hPne] at h1
  rcases hP.prime.dvd_mul.mp h1 with h | hg'
  · rcases hP.prime.dvd_mul.mp h with hcj | hdP
    · exact hP.prime.not_unit (isUnit_of_dvd_unit hcj
        (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))))
    · exact hP.prime.not_unit ((hP.separable).isUnit_of_dvd' (dvd_refl P) hdP)
  · exact hPg hg'

/-- Over a characteristic-`0` field, `gcd(pp(A), d pp(A)/dx)` is associated to the deflation
`A⁻¹`. -/
theorem deflation_one_eq_gcd (A : K[X]) (hA : A.primPart ≠ 0) :
    Associated (gcd A.primPart (derivative A.primPart)) (deflation A 1) := by
  set I := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with hI
  set f := sqfreeFactPart A with hf
  have hfact : Associated A.primPart (∏ i ∈ I, (f i) ^ i) :=
    primPart_associated_prod_sqfreeFactPart A hA
  have hD1 : deflation A 1 = ∏ i ∈ I, (f i) ^ (i - 1) := deflation_eq_prod_sqfreeFactPart A 1
  have hpair : ∀ e : ℕ → ℕ,
      (↑I : Set ℕ).Pairwise (Function.onFun IsRelPrime fun i => (f i) ^ (e i)) :=
    fun e i _ j _ hij => (((sqfreeFactPart_isRelPrime A hij).isCoprime).pow_left.pow_right).isRelPrime
  have hI_dvd : deflation A 1 ∣ derivative A.primPart := by
    rw [hD1]
    refine Finset.prod_dvd_of_isRelPrime (hpair (fun i => i - 1)) (fun i hi => ?_)
    exact pow_sub_one_dvd_derivative_of_pow_dvd
      ((Finset.dvd_prod_of_mem (fun i => (f i) ^ i) hi).trans hfact.symm.dvd)
  obtain ⟨s, hs⟩ := id hI_dvd
  have hgcdne : gcd A.primPart (derivative A.primPart) ≠ 0 :=
    fun h => hA (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hcop : IsCoprime (gcd A.primPart (derivative A.primPart)) s := by
    rw [← isRelPrime_iff_isCoprime, isRelPrime_iff_no_prime_factors hgcdne]
    intro P hPg hPs hPp
    have hPpp : P ∣ A.primPart := hPg.trans (gcd_dvd_left _ _)
    have hPprod : P ∣ ∏ i ∈ I, (f i) ^ i := hPpp.trans hfact.dvd
    rw [hPp.dvd_finsetProd_iff] at hPprod
    obtain ⟨j, hjI, hPfjpow⟩ := hPprod
    have hPfj : P ∣ f j := hPp.dvd_of_dvd_pow hPfjpow
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · rw [hj0, pow_zero] at hPfjpow; exact absurd (isUnit_of_dvd_one hPfjpow) hPp.not_unit
      · exact hj0
    obtain ⟨c, hc⟩ := hPfj
    have hPc : ¬ P ∣ c := fun ⟨d, hd⟩ =>
      hPp.not_unit ((sqfreeFactPart_squarefree A j) P ⟨d, by rw [← hf, hc, hd]; ring⟩)
    have hcoperase : IsCoprime P (∏ i ∈ I.erase j, (f i) ^ i) := by
      refine IsCoprime.prod_right (fun i hi => ?_)
      have hij : j ≠ i := fun h => (Finset.mem_erase.mp hi).1 h.symm
      exact (((sqfreeFactPart_isRelPrime A hij).isCoprime).of_isCoprime_of_dvd_left
        ⟨c, hc⟩).pow_right
    have hndvd : ¬ P ^ (j + 1) ∣ A.primPart := by
      intro hd
      rw [hfact.dvd_iff_dvd_right, ← Finset.mul_prod_erase I (fun i => (f i) ^ i) hjI] at hd
      have h2 : P ^ (j + 1) ∣ (f j) ^ j := (hcoperase.pow_left).dvd_of_dvd_mul_right hd
      rw [hc, mul_pow, pow_succ] at h2
      exact hPc (hPp.dvd_of_dvd_pow ((mul_dvd_mul_iff_left (pow_ne_zero j hPp.ne_zero)).mp h2))
    have hdvdj : P ^ j ∣ A.primPart :=
      ((pow_dvd_pow_of_dvd ⟨c, hc⟩ j).trans
        (Finset.dvd_prod_of_mem (fun i => (f i) ^ i) hjI)).trans hfact.symm.dvd
    have hpdvd : P ^ j ∣ derivative A.primPart := by
      rw [hs, show j = (j - 1) + 1 from by omega, pow_succ]
      exact mul_dvd_mul ((pow_dvd_pow_of_dvd ⟨c, hc⟩ (j - 1)).trans
        (hD1 ▸ Finset.dvd_prod_of_mem (fun i => (f i) ^ (i - 1)) hjI)) hPs
    exact pow_not_dvd_derivative_aux A.primPart P j hj1 hPp.irreducible hdvdj hndvd hpdvd
  exact associated_of_dvd_dvd (hcop.dvd_of_dvd_mul_right (hs ▸ gcd_dvd_right _ _))
    (dvd_gcd (deflation_dvd_primPart A 1 hA) ⟨s, hs⟩)

/-! ### The abstract Yun loop base case -/

open UniqueFactorizationMonoid in
open Classical in
/-- `squarefreePart (deflation A k)` is monic. -/
theorem squarefreePart_deflation_monic {K : Type*} [Field K] (A : K[X]) (k : ℕ)
    (hA : A.primPart ≠ 0) : (squarefreePart (deflation A k)).Monic := by
  rw [squarefreePart_deflation A k hA]
  refine monic_prod_of_monic _ _ (fun P hP => ?_)
  have hmem := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1
  rw [← normalize_normalized_factor P hmem]
  exact monic_normalize (irreducible_of_normalized_factor P hmem).ne_zero

open UniqueFactorizationMonoid in
open Classical in
/-- `deflation A k` is monic. -/
theorem deflation_monic {K : Type*} [Field K] (A : K[X]) (k : ℕ) :
    (deflation A k).Monic := by
  rw [deflation]
  refine monic_prod_of_monic _ _ (fun P hP => ?_)
  have hmem := Multiset.mem_toFinset.mp hP
  refine (?_ : (P).Monic).pow _
  rw [← normalize_normalized_factor P hmem]
  exact monic_normalize (irreducible_of_normalized_factor P hmem).ne_zero

open UniqueFactorizationMonoid in
open Classical in
/-- `A.primPart` is associated to `A` over a field. -/
theorem associated_primPart_self {K : Type*} [Field K] (A : K[X]) (hA0 : A ≠ 0) :
    Associated A.primPart A := by
  have hc : IsUnit (Polynomial.C A.content) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact fun h => hA0 (by rw [A.eq_C_content_mul_primPart, h, map_zero, zero_mul])
  refine ⟨hc.unit, ?_⟩
  rw [IsUnit.unit_spec]
  conv_rhs => rw [A.eq_C_content_mul_primPart]
  ring

open UniqueFactorizationMonoid in
open Classical in
/-- `deflation A 0 = normalize A` over a field. -/
theorem deflation_zero_eq_normalize {K : Type*} [Field K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) : deflation A 0 = normalize A := by
  refine eq_of_monic_of_associated (deflation_monic A 0)
    ((monic_normalize hA0)) ?_
  exact ((deflation_zero A hA).trans (associated_primPart_self A hA0)).trans
    (associated_normalize A)

open UniqueFactorizationMonoid in
open Classical in
/-- `derivative A = C (content A) * derivative A.primPart`. -/
theorem derivative_eq_C_content_mul_derivative_primPart {K : Type*} [Field K] (A : K[X]) :
    derivative A = Polynomial.C A.content * derivative A.primPart := by
  conv_lhs => rw [A.eq_C_content_mul_primPart]
  rw [derivative_mul, derivative_C, zero_mul, zero_add]

open UniqueFactorizationMonoid in
open Classical in
/-- `gcd A (derivative A) = deflation A 1` over a characteristic-zero field. -/
theorem gcd_self_derivative_eq_deflation_one {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) :
    gcd A (derivative A) = deflation A 1 := by
  have hgne : gcd A (derivative A) ≠ 0 :=
    fun h => hA0 (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hgmonic : (gcd A (derivative A)).Monic := by
    rw [← normalize_eq_self_iff_monic hgne]; exact normalize_gcd A (derivative A)
  refine eq_of_monic_of_associated hgmonic (deflation_monic A 1) ?_
  have hAp : Associated A A.primPart := (associated_primPart_self A hA0).symm
  have hc : IsUnit (Polynomial.C A.content) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact fun h => hA0 (by rw [A.eq_C_content_mul_primPart, h, map_zero, zero_mul])
  have hAp' : Associated (derivative A) (derivative A.primPart) := by
    rw [derivative_eq_C_content_mul_derivative_primPart A]
    exact associated_unit_mul_left (derivative A.primPart) (Polynomial.C A.content) hc
  exact (Associated.gcd hAp hAp').trans (deflation_one_eq_gcd A hA)

open UniqueFactorizationMonoid in
open Classical in
/-- `squarefreePart (deflation A 0) * deflation A 1 = deflation A 0`. -/
theorem squarefreePart_mul_deflation_one {K : Type*} [Field K] (A : K[X]) (hA : A.primPart ≠ 0) :
    squarefreePart (deflation A 0) * deflation A 1 = deflation A 0 := by
  refine eq_of_monic_of_associated
    ((squarefreePart_deflation_monic A 0 hA).mul (deflation_monic A 1)) (deflation_monic A 0) ?_
  exact squarefreePart_mul_deflation_succ A 0 hA

open UniqueFactorizationMonoid in
open Classical in
/-- The Yun loop initialization satisfies `YunInv A 1`. -/
theorem yunInv_base {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) :
    YunInv A 1 (A / gcd A (derivative A))
      (derivative A / gcd A (derivative A) - derivative (A / gcd A (derivative A))) := by
  have hg : gcd A (derivative A) = deflation A 1 := gcd_self_derivative_eq_deflation_one A hA0 hA
  have hd1ne : deflation A 1 ≠ 0 := deflation_ne_zero A 1
  have hlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have hAeq : A = Polynomial.C A.leadingCoeff * deflation A 0 := by
    rw [deflation_zero_eq_normalize A hA0 hA]
    exact self_eq_C_leadingCoeff_mul_normalize A hA0
  have hbabs : Babs A 1 = squarefreePart (deflation A 0) := by rw [Babs]
  have hAfact : A = (Polynomial.C A.leadingCoeff * squarefreePart (deflation A 0)) * deflation A 1 := by
    rw [mul_assoc, squarefreePart_mul_deflation_one A hA, ← hAeq]
  have hb1 : A / gcd A (derivative A) = Polynomial.C A.leadingCoeff * Babs A 1 := by
    rw [hg, hbabs]
    nth_rewrite 1 [hAfact]
    rw [mul_div_cancel_right₀ _ hd1ne]
  have hAderiv : derivative A = Polynomial.C A.leadingCoeff * (deflation A 1 * Yun A 1) := by
    have hdp := derivative_deflation_pred A 1 (le_refl 1)
    rw [Nat.sub_self] at hdp
    conv_lhs => rw [hAeq, derivative_C_mul, hdp]
  have hd1div : derivative A / gcd A (derivative A) = Polynomial.C A.leadingCoeff * Yun A 1 := by
    rw [hg]
    nth_rewrite 1 [hAderiv]
    rw [mul_comm (deflation A 1) (Yun A 1), ← mul_assoc, mul_div_cancel_right₀ _ hd1ne]
  refine ⟨A.leadingCoeff, hlc, hb1, ?_⟩
  rw [hd1div, hb1, derivative_C_mul, Dabs, Nat.sub_self, ← hbabs, mul_sub]

/-! ### Unconditional abstract Yun factorization -/

open Classical in
/-- Abstract Yun factorization from the standard initialization. -/
noncomputable def yunFactorizationAbs {K : Type*} [Field K] (A : K[X]) (n : ℕ) : List K[X] :=
  yunLoopAbs A (A / gcd A (derivative A),
    derivative A / gcd A (derivative A) - derivative (A / gcd A (derivative A))) 1 n

open Classical in
/-- `yunFactorizationAbs` is factorwise associated to consecutive squarefree parts. -/
theorem yunFactorizationAbs_forall₂ {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) (n : ℕ) :
    List.Forall₂ Associated (yunFactorizationAbs A n)
      ((List.range n).map (fun j => sqfreeFactPart A (1 + j))) :=
  yunLoopAbs_forall₂ A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA)

open Classical in
/-- Every factor in `yunFactorizationAbs` is squarefree. -/
theorem yunFactorizationAbs_squarefree {K : Type*} [Field K] [CharZero K] (A : K[X]) (hA0 : A ≠ 0)
    (hA : A.primPart ≠ 0) (n : ℕ) : ∀ V ∈ yunFactorizationAbs A n, Squarefree V :=
  yunLoopAbs_squarefree A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA)

open Classical in
/-- Distinct-position factors in `yunFactorizationAbs` are relatively prime. -/
theorem yunFactorizationAbs_pairwise_isRelPrime {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) {p q : ℕ} (hpq : p ≠ q)
    (hp : p < (yunFactorizationAbs A n).length) (hq : q < (yunFactorizationAbs A n).length) :
    IsRelPrime ((yunFactorizationAbs A n).get ⟨p, hp⟩) ((yunFactorizationAbs A n).get ⟨q, hq⟩) :=
  yunLoopAbs_pairwise_isRelPrime A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA) hpq hp hq

open Classical in
/-- The powered product of `yunFactorizationAbs` matches the powered squarefree parts up to association. -/
theorem yunFactorizationAbs_prodPow_assoc {K : Type*} [Field K] [CharZero K] (A : K[X])
    (hA0 : A ≠ 0) (hA : A.primPart ≠ 0) (n : ℕ) :
    Associated (prodPow 1 (yunFactorizationAbs A n))
      (prodPow 1 ((List.range n).map (fun j => sqfreeFactPart A (1 + j)))) :=
  yunLoopAbs_prodPow_assoc A hA n 1 _ _ (le_refl 1) (yunInv_base A hA0 hA)

end GcdField

section SquarefreeAlgorithm

open UniqueFactorizationMonoid

variable {K : Type*} [Field K]

open Classical

/-- Over a field, `gcd((A⁻⁽ᵏ⁻¹⁾)*, A⁻ᵏ)` is associated to the deflation squarefree part
`(A⁻ᵏ)*` (`1 ≤ k`). -/
theorem gcd_squarefreePart_deflation (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0) :
    Associated (gcd (squarefreePart (deflation A (k - 1))) (deflation A k))
      (squarefreePart (deflation A k)) := by
  have hcop : IsCoprime (sqfreeFactPart A k) (deflation A k) := by
    rw [deflation_eq_prod_sqfreeFactPart A k]
    refine IsCoprime.prod_right (fun i _ => ?_)
    by_cases hik : i = k
    · rw [hik, Nat.sub_self, pow_zero]; exact isCoprime_one_right
    · exact ((sqfreeFactPart_isRelPrime A (Ne.symm hik)).isCoprime).pow_right
  have h15 : squarefreePart (deflation A (k - 1))
      = sqfreeFactPart A k * squarefreePart (deflation A k) := by
    rw [← squarefreePart_deflation_mul_sqfreeFactPart A k hk hA, mul_comm]
  have hWdvd : squarefreePart (deflation A k) ∣ deflation A k :=
    (dvd_mul_right _ (deflation A (k + 1))).trans (squarefreePart_mul_deflation_succ A k hA).dvd
  rw [h15]
  refine associated_of_dvd_dvd ?_ (dvd_gcd (dvd_mul_left _ _) hWdvd)
  have hgc : IsCoprime (gcd (sqfreeFactPart A k * squarefreePart (deflation A k)) (deflation A k))
      (sqfreeFactPart A k) := hcop.symm.of_isCoprime_of_dvd_left (gcd_dvd_right _ _)
  exact hgc.dvd_of_dvd_mul_left (gcd_dvd_left _ _)

/-- Executable squarefree-factorization loop on `fuel`: while `Sminus` is non-constant, emit
`Sstar / gcd(Sstar, Sminus)` and recurse on `(gcd, Sminus/gcd)`; otherwise emit `Sstar`. -/
noncomputable def squarefreeLoop (Sstar Sminus : K[X]) : ℕ → List K[X]
  | 0 => [Sstar]
  | (n + 1) =>
    if Sminus.natDegree = 0 then [Sstar]
    else (Sstar / gcd Sstar Sminus)
      :: squarefreeLoop (gcd Sstar Sminus) (Sminus / gcd Sstar Sminus) n

/-- The squarefree-factorization parts of `A`, computed by `squarefreeLoop` from
`gcd(pp A, d pp A/dx)` and `pp A / gcd`. -/
noncomputable def squarefreeFactorization (A : K[X]) : List K[X] :=
  squarefreeLoop (A.primPart / gcd A.primPart (derivative A.primPart))
    (gcd A.primPart (derivative A.primPart)) A.primPart.natDegree

/-- Division by an associate, up to associates: for `Y ∣ X` (`Y ≠ 0`), `X/Y ~ c ↔ X ~ Y·c`. -/
theorem associated_div_iff {X Y c : K[X]} (hY : Y ≠ 0) (hdvd : Y ∣ X) :
    Associated (X / Y) c ↔ Associated X (Y * c) := by
  have hmul : Y * (X / Y) = X := EuclideanDomain.mul_div_cancel' hY hdvd
  constructor
  · intro h; exact hmul ▸ h.mul_left Y
  · intro h; exact (hmul.symm ▸ h).of_mul_left (Associated.refl Y) hY

/-- The emitted loop part `(A⁻⁽ᵏ⁻¹⁾)* / gcd((A⁻⁽ᵏ⁻¹⁾)*, A⁻ᵏ)` is associated to `Aₖ` (`1 ≤ k`). -/
theorem squarefreeLoop_head_assoc (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0) :
    Associated (squarefreePart (deflation A (k - 1))
        / gcd (squarefreePart (deflation A (k - 1))) (deflation A k))
      (sqfreeFactPart A k) := by
  have hYass := gcd_squarefreePart_deflation A k hk hA
  have hY : gcd (squarefreePart (deflation A (k - 1))) (deflation A k) ≠ 0 :=
    fun h => deflation_ne_zero A k (eq_zero_of_zero_dvd (h ▸ gcd_dvd_right _ _))
  have hsplit := squarefreePart_deflation_mul_sqfreeFactPart A k hk hA
  rw [associated_div_iff hY (hYass.dvd.trans ⟨sqfreeFactPart A k, hsplit.symm⟩)]
  exact hsplit ▸ hYass.symm.mul_right (sqfreeFactPart A k)

/-- The updated loop deflation `A⁻ᵏ / gcd((A⁻⁽ᵏ⁻¹⁾)*, A⁻ᵏ)` is associated to `A⁻⁽ᵏ⁺¹⁾` (`1 ≤ k`). -/
theorem squarefreeLoop_tail_assoc (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0) :
    Associated (deflation A k
        / gcd (squarefreePart (deflation A (k - 1))) (deflation A k))
      (deflation A (k + 1)) := by
  have hYass := gcd_squarefreePart_deflation A k hk hA
  have hY : gcd (squarefreePart (deflation A (k - 1))) (deflation A k) ≠ 0 :=
    fun h => deflation_ne_zero A k (eq_zero_of_zero_dvd (h ▸ gcd_dvd_right _ _))
  have h13 := squarefreePart_mul_deflation_succ A k hA
  rw [associated_div_iff hY (hYass.dvd.trans ((dvd_mul_right _ _).trans h13.dvd))]
  exact h13.symm.trans (hYass.symm.mul_right (deflation A (k + 1)))

/-! ### Total correctness of the executable algorithm
`squarefreeFactorization A` equals the squarefree-factorization parts `[A₁, …, Aₘ]` up to
associates. -/

private theorem deflation_natDegree_eq_zero_iff (A : K[X]) (k : ℕ) :
    (deflation A k).natDegree = 0 ↔ ∀ P ∈ (normalizedFactors A.primPart).toFinset,
      (normalizedFactors A.primPart).count P ≤ k := by
  rw [deflation, natDegree_prod _ _ (fun P hP => pow_ne_zero _
    (irreducible_of_normalized_factor P (Multiset.mem_toFinset.mp hP)).ne_zero),
    Finset.sum_eq_zero_iff]
  refine forall₂_congr (fun P hP => ?_)
  rw [natDegree_pow, Nat.mul_eq_zero]
  have := (irreducible_of_normalized_factor P (Multiset.mem_toFinset.mp hP)).natDegree_pos
  omega

theorem squarefreePart_deflation_natDegree_eq_zero_iff (A : K[X]) (k : ℕ)
    (hA : A.primPart ≠ 0) :
    (squarefreePart (deflation A k)).natDegree = 0 ↔ ∀ P ∈ (normalizedFactors A.primPart).toFinset,
      (normalizedFactors A.primPart).count P ≤ k := by
  rw [squarefreePart_deflation A k hA, natDegree_prod _ _ (fun P hP =>
    (irreducible_of_normalized_factor P
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).ne_zero), Finset.sum_eq_zero_iff]
  constructor
  · intro h P hP
    by_contra hlt
    exact absurd (h P (Finset.mem_filter.mpr ⟨hP, by omega⟩))
      (irreducible_of_normalized_factor P (Multiset.mem_toFinset.mp hP)).natDegree_pos.ne'
  · intro h P hP
    have h1 := h P (Finset.mem_filter.mp hP).1
    have h2 := (Finset.mem_filter.mp hP).2
    omega

/-- The remaining Yun radical `squarefreePart (deflation A k)` is constant iff `k` has reached the
maximum multiplicity: `natDegree = 0 ↔ maxmult ≤ k`. Governs when Yun's loop terminates. -/
theorem squarefreePart_deflation_natDegree_eq_zero_iff_maxmult (A : K[X]) (k : ℕ)
    (hA : A.primPart ≠ 0) :
    (squarefreePart (deflation A k)).natDegree = 0 ↔
      (normalizedFactors A.primPart).toFinset.sup
        (fun P => (normalizedFactors A.primPart).count P) ≤ k :=
  (squarefreePart_deflation_natDegree_eq_zero_iff A k hA).trans Finset.sup_le_iff.symm

open UniqueFactorizationMonoid in
/-- The maximum multiplicity is bounded by the degree of the primitive part:
`maxmult ≤ natDegree pp(A)`. A prime `P` of multiplicity `m` contributes `P^m ∣ pp(A)`, and
`m ≤ m·deg P ≤ deg pp(A)`. -/
theorem sup_count_le_natDegree_primPart (A : K[X]) (hA : A.primPart ≠ 0) :
    (normalizedFactors A.primPart).toFinset.sup
        (fun P => (normalizedFactors A.primPart).count P) ≤ A.primPart.natDegree := by
  apply Finset.sup_le
  intro P hP
  have hmem := Multiset.mem_toFinset.mp hP
  have hle : Multiset.replicate ((normalizedFactors A.primPart).count P) P
      ≤ normalizedFactors A.primPart := Multiset.le_count_iff_replicate_le.mp le_rfl
  have hdvd1 : P ^ (normalizedFactors A.primPart).count P
      ∣ (normalizedFactors A.primPart).prod := by
    rw [← Multiset.prod_replicate]; exact Multiset.prod_dvd_prod_of_le hle
  have hdvd : P ^ (normalizedFactors A.primPart).count P ∣ A.primPart :=
    hdvd1.trans (prod_normalizedFactors hA).dvd
  have hnd := natDegree_le_of_dvd hdvd hA
  rw [natDegree_pow] at hnd
  have hpos : 1 ≤ P.natDegree := (irreducible_of_normalized_factor P hmem).natDegree_pos
  nlinarith [hnd, hpos]

private theorem natDegree_eq_of_associated {p q : K[X]} (h : Associated p q) (hq : q ≠ 0) :
    p.natDegree = q.natDegree :=
  le_antisymm (natDegree_le_of_dvd h.dvd hq)
    (natDegree_le_of_dvd h.symm.dvd (fun hp => hq (h.eq_zero_iff.mp hp)))

private theorem squarefreePart_deflation_ne_zero (A : K[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    squarefreePart (deflation A k) ≠ 0 := by
  rw [squarefreePart_deflation A k hA, Finset.prod_ne_zero_iff]
  exact fun P hP => (irreducible_of_normalized_factor P
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).ne_zero

private theorem head_gen (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0)
    {Sstar Sminus : K[X]} (hSs : Associated Sstar (squarefreePart (deflation A (k - 1))))
    (hSm : Associated Sminus (deflation A k)) :
    Associated (Sstar / gcd Sstar Sminus) (sqfreeFactPart A k) := by
  have hSmne : Sminus ≠ 0 := fun h => deflation_ne_zero A k (hSm.eq_zero_iff.mp h)
  have hY : gcd Sstar Sminus ≠ 0 := fun h => hSmne (eq_zero_of_zero_dvd (h ▸ gcd_dvd_right _ _))
  have hgcd : Associated (gcd Sstar Sminus) (squarefreePart (deflation A k)) :=
    (hSs.gcd hSm).trans (gcd_squarefreePart_deflation A k hk hA)
  have hsplit := squarefreePart_deflation_mul_sqfreeFactPart A k hk hA
  rw [associated_div_iff hY
    (hgcd.dvd.trans (dvd_trans (show squarefreePart (deflation A k)
        ∣ squarefreePart (deflation A (k - 1)) from ⟨sqfreeFactPart A k, hsplit.symm⟩)
      hSs.symm.dvd))]
  exact hSs.trans (hsplit ▸ hgcd.symm.mul_right (sqfreeFactPart A k))

private theorem tail_gen (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0)
    {Sstar Sminus : K[X]} (hSs : Associated Sstar (squarefreePart (deflation A (k - 1))))
    (hSm : Associated Sminus (deflation A k)) :
    Associated (Sminus / gcd Sstar Sminus) (deflation A (k + 1)) := by
  have hSmne : Sminus ≠ 0 := fun h => deflation_ne_zero A k (hSm.eq_zero_iff.mp h)
  have hY : gcd Sstar Sminus ≠ 0 := fun h => hSmne (eq_zero_of_zero_dvd (h ▸ gcd_dvd_right _ _))
  have hgcd : Associated (gcd Sstar Sminus) (squarefreePart (deflation A k)) :=
    (hSs.gcd hSm).trans (gcd_squarefreePart_deflation A k hk hA)
  have h13 := squarefreePart_mul_deflation_succ A k hA
  rw [associated_div_iff hY
    (hgcd.dvd.trans ((dvd_mul_right _ _).trans (h13.dvd.trans hSm.symm.dvd)))]
  exact hSm.trans (h13.symm.trans (hgcd.symm.mul_right (deflation A (k + 1))))

private theorem deflation_succ_natDegree_lt (A : K[X]) (k : ℕ) (hA : A.primPart ≠ 0)
    (hpos : (deflation A k).natDegree ≠ 0) :
    (deflation A (k + 1)).natDegree < (deflation A k).natDegree := by
  have h13 := squarefreePart_mul_deflation_succ A k hA
  have heq : (deflation A k).natDegree
      = (squarefreePart (deflation A k)).natDegree + (deflation A (k + 1)).natDegree :=
    (natDegree_eq_of_associated h13.symm (mul_ne_zero
        (squarefreePart_deflation_ne_zero A k hA) (deflation_ne_zero A (k + 1)))).trans
      (natDegree_mul (squarefreePart_deflation_ne_zero A k hA) (deflation_ne_zero A (k + 1)))
  have hsd : (squarefreePart (deflation A k)).natDegree ≠ 0 := by
    rw [ne_eq, squarefreePart_deflation_natDegree_eq_zero_iff A k hA,
      ← deflation_natDegree_eq_zero_iff A k]
    exact hpos
  omega

private theorem squarefreePart_deflation_eq_one (A : K[X]) (k : ℕ) (hA : A.primPart ≠ 0)
    (h : ∀ P ∈ (normalizedFactors A.primPart).toFinset, (normalizedFactors A.primPart).count P ≤ k) :
    squarefreePart (deflation A k) = 1 := by
  rw [squarefreePart_deflation A k hA,
    Finset.filter_eq_empty_iff.mpr (fun P hP => not_lt.mpr (h P hP)), Finset.prod_empty]

private theorem loop_correct (A : K[X]) (hA : A.primPart ≠ 0) (m : ℕ)
    (hterm : ∀ k, (deflation A k).natDegree = 0 ↔ m ≤ k)
    (hbase : squarefreePart (deflation A (m - 1)) = sqfreeFactPart A m) :
    ∀ (fuel k : ℕ) (Sstar Sminus : K[X]), 1 ≤ k → k ≤ m →
      Associated Sstar (squarefreePart (deflation A (k - 1))) →
      Associated Sminus (deflation A k) → (deflation A k).natDegree ≤ fuel →
      List.Forall₂ Associated (squarefreeLoop Sstar Sminus fuel)
        ((List.range (m + 1 - k)).map (fun i => sqfreeFactPart A (k + i))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k Sstar Sminus hk hkm hSs hSm hfuel
    have hkeq : k = m := le_antisymm hkm ((hterm k).mp (Nat.le_zero.mp hfuel))
    subst hkeq
    rw [squarefreeLoop, show k + 1 - k = 1 from by omega]
    simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
    rw [hbase] at hSs
    exact List.Forall₂.cons hSs List.Forall₂.nil
  | succ n ih =>
    intro k Sstar Sminus hk hkm hSs hSm hfuel
    rw [squarefreeLoop]
    have hdeg : Sminus.natDegree = (deflation A k).natDegree :=
      natDegree_eq_of_associated hSm (deflation_ne_zero A k)
    by_cases hd0 : Sminus.natDegree = 0
    · rw [if_pos hd0]
      have hkeq : k = m := le_antisymm hkm ((hterm k).mp (hdeg ▸ hd0))
      subst hkeq
      rw [show k + 1 - k = 1 from by omega]
      simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
      rw [hbase] at hSs
      exact List.Forall₂.cons hSs List.Forall₂.nil
    · rw [if_neg hd0]
      have hpos : (deflation A k).natDegree ≠ 0 := hdeg ▸ hd0
      have hkm' : k < m := lt_of_not_ge (fun hge => hpos ((hterm k).mpr hge))
      have htgt : (List.range (m + 1 - k)).map (fun i => sqfreeFactPart A (k + i))
          = sqfreeFactPart A k
            :: (List.range (m + 1 - (k + 1))).map (fun i => sqfreeFactPart A (k + 1 + i)) := by
        rw [show m + 1 - k = (m - k) + 1 from by omega, List.range_succ_eq_map, List.map_cons]
        refine congrArg₂ _ (by simp) ?_
        rw [List.map_map, show m + 1 - (k + 1) = m - k from by omega]
        exact List.map_congr_left (fun i _ => by simp only [Function.comp_apply]; congr 1; omega)
      rw [htgt]
      refine List.Forall₂.cons (head_gen A k hk hA hSs hSm) ?_
      refine ih (k + 1) (gcd Sstar Sminus) (Sminus / gcd Sstar Sminus)
        (by omega) (by omega)
        ((hSs.gcd hSm).trans (gcd_squarefreePart_deflation A k hk hA))
        (tail_gen A k hk hA hSs hSm) ?_
      have := deflation_succ_natDegree_lt A k hA hpos
      omega

theorem squarefreeFactorization_forall₂ [CharZero K] (A : K[X]) (hA : A.primPart ≠ 0)
    (hm1 : 1 ≤ (normalizedFactors A.primPart).toFinset.sup
      (fun P => (normalizedFactors A.primPart).count P)) :
    List.Forall₂ Associated (squarefreeFactorization A)
      ((List.range ((normalizedFactors A.primPart).toFinset.sup
        (fun P => (normalizedFactors A.primPart).count P))).map
        (fun i => sqfreeFactPart A (i + 1))) := by
  set m := (normalizedFactors A.primPart).toFinset.sup
    (fun P => (normalizedFactors A.primPart).count P) with hmdef
  have hterm : ∀ k, (deflation A k).natDegree = 0 ↔ m ≤ k :=
    fun k => (deflation_natDegree_eq_zero_iff A k).trans Finset.sup_le_iff.symm
  have hbase : squarefreePart (deflation A (m - 1)) = sqfreeFactPart A m := by
    have h1 := squarefreePart_deflation_eq_one A m hA (fun P hP => Finset.le_sup (f := fun P => (normalizedFactors A.primPart).count P) hP)
    have h15 := squarefreePart_deflation_mul_sqfreeFactPart A m hm1 hA
    rw [h1, one_mul] at h15; exact h15.symm
  have hg14 := deflation_one_eq_gcd A hA
  have hgne : gcd A.primPart (derivative A.primPart) ≠ 0 :=
    fun h => hA (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hSstar : Associated (A.primPart / gcd A.primPart (derivative A.primPart))
      (squarefreePart (deflation A 0)) := by
    rw [associated_div_iff hgne (gcd_dvd_left _ _)]
    refine ((deflation_zero A hA).symm.trans (squarefreePart_mul_deflation_succ A 0 hA).symm).trans ?_
    exact (hg14.symm.mul_left (squarefreePart (deflation A 0))).trans (by rw [mul_comm])
  have key := loop_correct A hA m hterm hbase A.primPart.natDegree 1
    (A.primPart / gcd A.primPart (derivative A.primPart)) (gcd A.primPart (derivative A.primPart))
    (le_refl 1) hm1 hSstar hg14
    (natDegree_le_of_dvd (deflation_dvd_primPart A 1 hA) hA)
  rw [squarefreeFactorization]
  simpa [show m + 1 - 1 = m from by omega, Nat.add_comm] using key

end SquarefreeAlgorithm

end DeepWiki.SymbolicIntegration
