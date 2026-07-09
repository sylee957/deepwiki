import DeepWiki.ComputableAlgebra.PolyReprDivision

/-! # The reduction step strictly decreases degree (division termination heart)

Over a computable *field*, one Euclidean-division cancellation step against `q` sends `p` to a
polynomial of strictly smaller `degree` (the zero polynomial's `degree = ⊥` handled by `WithBot`), by
leading-coefficient cancellation. This is what a fuel bound of `cdeg p + 1` needs to guarantee the
`cdivmod` remainder is fully reduced — the missing piece for a full generic gcd correctness.

The declarations here take `[CField α] [CFieldSpec α]` (with `CCommRing`/`CRingSpec` coming from the
field path, so `CRingSpec.toR = CFieldSpec.toK` definitionally), *not* the ambient `[CCommRing α]` the
rest of the file uses — hence the fresh `variable` block. See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPolyRepr

variable {P : Type u → Type u} [CPolyRepr P] {α : Type u} [CField α] [CFieldSpec α]

/-- **One division step strictly lowers degree:** with `p, q ≠ 0` and `cdeg q ≤ cdeg p`, cancelling
`p`'s leading term against `q` gives a polynomial of strictly smaller `degree`. -/
theorem degree_reduce_step_lt (p q : P α)
    (hp : ¬ cisZero (P := P) p = true) (hq : ¬ cisZero (P := P) q = true) (hle : cdeg q ≤ cdeg p) :
    (toPoly (csub p (mul
        (cmonomial (P := P) (CField.div (clead p) (clead q)) (cdeg p - cdeg q)) q))).degree
      < (toPoly p).degree := by
  have hP : toPoly p ≠ 0 := fun h => hp ((cisZero_iff p).mpr h)
  have hQ : toPoly q ≠ 0 := fun h => hq ((cisZero_iff q).mpr h)
  have hlcP : (toPoly p).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hlcQ : (toPoly q).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  rw [toPoly_csub, toPoly_mul, toPoly_cmonomial]
  set c := CRingSpec.toR (CField.div (clead p) (clead q)) with hc
  set k := cdeg p - cdeg q with hk
  have hcval : c = (toPoly p).leadingCoeff / (toPoly q).leadingCoeff := by
    rw [hc, show CRingSpec.toR (CField.div (clead p) (clead q))
          = CFieldSpec.toK (CField.div (clead p) (clead q)) from rfl, CFieldSpec.toK_div,
      show CFieldSpec.toK (clead p) = CRingSpec.toR (clead p) from rfl,
      show CFieldSpec.toK (clead q) = CRingSpec.toR (clead q) from rfl,
      toR_clead_eq_leadingCoeff, toR_clead_eq_leadingCoeff]
  have hcne : c ≠ 0 := by rw [hcval]; exact div_ne_zero hlcP hlcQ
  have hCc : Polynomial.C c ≠ 0 := by rwa [Ne, Polynomial.C_eq_zero]
  have hdegR : (Polynomial.C c * X ^ k * toPoly q).degree = (toPoly p).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul, Polynomial.degree_C hcne,
      Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hQ, Polynomial.degree_eq_natDegree hP,
      ← cdeg_eq_natDegree, ← cdeg_eq_natDegree, hk, zero_add, ← Nat.cast_add]
    norm_cast; omega
  have hlcR : (Polynomial.C c * X ^ k * toPoly q).leadingCoeff = (toPoly p).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one, hcval, div_mul_cancel₀ _ hlcQ]
  exact Polynomial.degree_sub_lt hdegR.symm hP hlcR.symm

end DeepWiki.SymbolicIntegration.CPolyRepr
