import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # Polynomial squarefree deflations

Core definitions for squarefree parts and multiplicity deflations of primitive polynomial factors.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

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

end Deflation

end DeepWiki.SymbolicIntegration
