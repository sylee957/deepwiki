import DeepWiki.ComputableAlgebra.PolyEngineLawful
import DeepWiki.ComputableAlgebra.PolyReprSparse

/-! # Sparse computable-polynomial engine

The sparse `CPolyEngine` instance selects the representation-generic `CPoly` algorithms and
certifies them through `LawfulCPolyEngine`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- **The `SparsePoly` instance** supplies the generic `ofFn`-based ops, so a migrated declaration also
runs on the sparse carrier — the representation-independence payoff at the engine level. -/
instance instEngineSparse : CPolyEngine CPoly.SparsePoly where
  add := CPoly.add
  mul := CPoly.mul
  neg := CPoly.neg
  monomial := CPoly.cmonomial
  coeffList p := (List.range (CPoly.degBound p)).map (CPoly.coeff p)
  ofCoeffList xs := CPoly.ofFn xs.length (fun i => xs.getD i CCommRing.zero)
  mapCoeffs f p := CPoly.ofFn (CPoly.degBound p) (fun i => f (CPoly.coeff p i))
  deriv := CPoly.cderiv
  scale := CPoly.scale
  cnorm := CPoly.cnorm
  cisZero := CPoly.cisZero
  cdeg := CPoly.cdeg
  clead := CPoly.clead
  eval p x := CPoly.ceval x p

/-- The generic sparse engine operations satisfy the generic denotation laws. -/
instance instLawfulEngineSparse : LawfulCPolyEngine CPoly.SparsePoly where
  toPoly_add p q := by change CPoly.toPoly (CPoly.add p q) = _; exact CPoly.toPoly_add p q
  toPoly_mul p q := by change CPoly.toPoly (CPoly.mul p q) = _; exact CPoly.toPoly_mul p q
  toPoly_neg p := by change CPoly.toPoly (CPoly.neg p) = _; exact CPoly.toPoly_neg p
  toPoly_monomial c k := by
    change CPoly.toPoly (CPoly.cmonomial c k) = _
    exact CPoly.toPoly_cmonomial c k
  toPoly_coeffList p := by
    change CPoly.toPoly
        (CPoly.ofList ((List.range (CPoly.degBound p)).map (CPoly.coeff p))) = CPoly.toPoly p
    apply Polynomial.ext
    intro i
    rw [CPoly.coeff_toPoly, CPoly.coeff_toPoly, CPoly.coeff_ofList]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : i < CPoly.degBound p
    · rw [List.getElem?_range hi, Option.map_some, Option.getD_some]
    · rw [List.getElem?_eq_none (by simpa using hi), Option.map_none, Option.getD_none,
        CPoly.coeff_ge p i (Nat.le_of_not_gt hi), CRingSpec.toR_zero]
  toPoly_ofCoeffList xs := by
    change CPoly.toPoly (CPoly.ofList xs) = CPoly.toPoly (CPoly.ofList xs)
    rfl
  toR_coeff_mapCoeffs f hzero p i := by
    change CRingSpec.toR
        (CPoly.coeff
          (CPoly.ofFn (CPoly.degBound p) (fun j => f (CPoly.coeff p j))) i) = _
    rw [CPoly.coeff_ofFn]
    split
    · rfl
    · rename_i hi
      rw [CPoly.coeff_ge p i (Nat.le_of_not_gt hi), CRingSpec.toR_zero, hzero]
  toPoly_deriv p := by
    change CPoly.toPoly (CPoly.cderiv p) = (CPoly.toPoly p).derivative
    exact CPoly.toPoly_cderiv p
  toPoly_scale c p := by change CPoly.toPoly (CPoly.scale c p) = _; exact CPoly.toPoly_scale c p
  toPoly_cnorm p := by change CPoly.toPoly (CPoly.cnorm p) = _; exact CPoly.toPoly_cnorm p
  cisZero_iff p := by change CPoly.cisZero p = true ↔ _; exact CPoly.cisZero_iff p
  cdeg_eq_natDegree p := by change CPoly.cdeg p = _; exact CPoly.cdeg_eq_natDegree p
  toR_clead_eq_leadingCoeff p := by
    change CRingSpec.toR (CPoly.clead p) = _
    exact CPoly.toR_clead_eq_leadingCoeff p
  toR_eval p x := by
    change CRingSpec.toR (CPoly.ceval x p) = (CPoly.toPoly p).eval (CRingSpec.toR x)
    exact CPoly.toR_ceval x p

end DeepWiki.SymbolicIntegration
