import DeepWiki.ComputableAlgebra.PolyReprResultant

/-! # Resultant ↔ coprimality (linking the resultant and gcd subsystems)

Over a computable *field*, a nonzero computable resultant certifies coprimality, via the resultant
bridge `toR_cResultant` (= `Polynomial.resultant`) and Mathlib's `resultant_eq_zero_iff`. In a separate
file with field-path-only `[CField]/[CFieldSpec]` variables (so `CRingSpec.R α = CFieldSpec.K α` is a
`Field` and there is no ambient-`CCommRing` diamond). See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPoly

variable {P : Type u → Type u} [CPoly P] {α : Type u} [CField α] [CFieldSpec α]

/-- **Nonzero resultant ⇒ coprime:** if `p, q` are not both zero and the computable resultant denotes a
nonzero value, then `toPoly p` and `toPoly q` are coprime. Links the computable resultant to the
gcd/coprimality subsystem. -/
theorem isCoprime_of_cResultant_ne_zero (p q : P α) (hpq : toPoly p ≠ 0 ∨ toPoly q ≠ 0)
    (h : CRingSpec.toR (cResultant p q) ≠ 0) : IsCoprime (toPoly p) (toPoly q) := by
  rw [toR_cResultant, cdeg_eq_natDegree, cdeg_eq_natDegree] at h
  by_contra hnc
  exact h (Polynomial.resultant_eq_zero_iff.mpr ⟨hpq, hnc⟩)

end DeepWiki.SymbolicIntegration.CPoly
