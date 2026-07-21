import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect
import DeepWiki.Algebra.SubresultantPRS

/-! # One computable pseudo-remainder subresultant step

The abstract subresultant reduction induced by one computable `GBPolyCore.gbpsremainderCore` pseudo-division step.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-- `Sⱼ(A, C c · B) = c^(n−j) · Sⱼ(A, B)` when `j ≤ m` and `j ≤ n`. -/
theorem subresultant_C_mul_right {R : Type*} [CommRing R] (c : R) (A B : R[X]) (n m j : ℕ)
    (hjm : j ≤ m) (hjn : j ≤ n) :
    subresultant A (C c * B) n m j = C (c ^ (n - j)) * subresultant A B n m j := by
  have h := subresultant_C_mul 1 c A B n m j hjm hjn
  rw [map_one, one_mul, one_pow, one_mul] at h
  rw [h]

/-- One subresultant-PRS step through `DensePoly.toPoly`: from the pseudo-division identity for `(s, c)`,
`C((DensePoly.toPoly c)^(m−j)) · Sⱼ(A,B; n,m) = (-1)^((m−j)(n−j)) · Sⱼ(B, Rem; m,n)` under the degree bounds. -/
theorem subresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (p q : GBPolyCore ℚ) (n m j : ℕ)
    (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hsc : Polynomial.C (DensePoly.toPoly c) * DensePoly.toPoly p
        = DensePoly.toPoly s * DensePoly.toPoly q + DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel p q))
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (DensePoly.toPoly q).natDegree ≤ m)
    (hQ : (DensePoly.toPoly s).natDegree + m ≤ n) :
    Polynomial.C ((DensePoly.toPoly c) ^ (m - j)) * subresultant (DensePoly.toPoly p) (DensePoly.toPoly q) n m j
      = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
        * subresultant (DensePoly.toPoly q) (DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel p q)) m n j := by
  rw [← subresultant_C_mul_left (DensePoly.toPoly c) (DensePoly.toPoly p) (DensePoly.toPoly q) n m j hjm (le_of_lt hjn)]
  exact subresultant_rem (Polynomial.C (DensePoly.toPoly c) * DensePoly.toPoly p) (DensePoly.toPoly q) (DensePoly.toPoly s)
    (DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel p q)) n m j hjm hjn hB hQ (by rw [hsc]; ring)

/-- Existence form: some quotient/content `(s, c)` realize the pseudo-division identity and, given the
quotient-degree bound, the subresultant reduction. -/
theorem exists_subresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (p q : GBPolyCore ℚ) (n m j : ℕ)
    (hjm : j ≤ m) (hjn : j < n) (hB : (DensePoly.toPoly q).natDegree ≤ m) :
    ∃ (s : GBPolyCore ℚ) (c : DensePoly ℚ),
      Polynomial.C (DensePoly.toPoly c) * DensePoly.toPoly p
          = DensePoly.toPoly s * DensePoly.toPoly q + DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel p q)
        ∧ ((DensePoly.toPoly s).natDegree + m ≤ n →
          Polynomial.C ((DensePoly.toPoly c) ^ (m - j)) * subresultant (DensePoly.toPoly p) (DensePoly.toPoly q) n m j
            = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
              * subresultant (DensePoly.toPoly q) (DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel p q)) m n j) := by
  obtain ⟨s, c, hsc⟩ := GBPolyCore.toPolyG_gbpsremainderCore fuel p q
  exact ⟨s, c, hsc, fun hQs =>
    subresultant_C_mul_eq_rem_of_bpsremainder fuel p q n m j s c hsc hjm hjn hB hQs⟩

end DeepWiki.SymbolicIntegration.Compute
