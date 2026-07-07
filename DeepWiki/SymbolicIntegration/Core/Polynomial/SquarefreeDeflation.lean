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

end Deflation

end DeepWiki.SymbolicIntegration
