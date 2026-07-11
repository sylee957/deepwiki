import Mathlib.Algebra.Squarefree.Basic
import DeepWiki.Algebra.SquarefreeDeflation

/-! # Polynomial squarefree-factorization parts

Multiplicity-indexed squarefree factors of primitive polynomial parts.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section SquarefreeParts
open UniqueFactorizationMonoid
variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D]

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

end SquarefreeParts

end DeepWiki.SymbolicIntegration
