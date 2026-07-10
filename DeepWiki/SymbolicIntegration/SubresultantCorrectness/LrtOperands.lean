import DeepWiki.SymbolicIntegration.Compute.Subresultant
import DeepWiki.SymbolicIntegration.SubresultantCorrectness.PseudoRemainderStep
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtSubresultant

/-! # LRT operands for subresultant correctness
Identifies the computable LRT inputs inside `GBPolyCore ℚ` and specializes the first
pseudo-remainder subresultant step to those operands. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Identifying the LRT operands: the computable lifts realize `D.map C`, `A - t*D'` -/

/-- `DensePoly.toPoly (liftCtoBPoly p) = (toPoly p).map C`: `liftCtoBPoly` realizes the coefficient embedding. -/
theorem toBPoly_liftCtoBPoly (p : DensePoly ℚ) :
    DensePoly.toPoly (liftCtoBPoly p) = (toPoly p).map (Polynomial.C : ℚ →+* ℚ[X]) := by
  induction p with
  | nil => simp [liftCtoBPoly]
  | cons a as ih =>
    show DensePoly.toPoly (cnorm [a] :: liftCtoBPoly as) = _
    rw [DensePoly.toPolyG_cons_dense, ih]
    rw [DensePoly.toPolyG_cnormG, DensePoly.toPolyG_cons,
      DensePoly.toPolyG_nil, mul_zero, add_zero, toR_eq_toK, CFieldSpec.toK_rat]
    rw [DensePoly.toPolyG_cons, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C, toR_eq_toK, CFieldSpec.toK_rat]

/-- `toPoly ctVar = X`: the computable `t`-variable lifts to the indeterminate `X ∈ ℚ[t]`. -/
@[simp] theorem toPoly_ctVar : toPoly ctVar = (Polynomial.X : ℚ[X]) := by
  rw [ctVar]
  simp

/-- `DensePoly.toPoly (bArgAmtD' A D) = (toPoly A).map C - C X * (derivative (toPoly D)).map C`: the LRT second
operand `A - t*D'`. -/
theorem toBPoly_bArgAmtD' (A D : DensePoly ℚ) :
    DensePoly.toPoly (bArgAmtD' A D)
      = (toPoly A).map (Polynomial.C : ℚ →+* ℚ[X])
        - Polynomial.C Polynomial.X * (derivative (toPoly D)).map (Polynomial.C : ℚ →+* ℚ[X]) := by
  rw [bArgAmtD', DensePoly.toPolyG_csubG, toBPoly_liftCtoBPoly,
    DensePoly.toPolyG_cscaleG, toBPoly_liftCtoBPoly]
  change _ - Polynomial.C (toPoly ctVar) * _ = _
  rw [toPoly_ctVar]
  rw [DensePoly.toPolyG_cderivG]

/-- `lrtSubresultant A D j` is the abstract subresultant of the `DensePoly.toPoly` images of the computable
operands at formal degrees `deg D`, `deg D - 1`. -/
theorem lrtSubresultant_eq_subresultant_toBPoly (A D : DensePoly ℚ) (j : ℕ) :
    lrtSubresultant (toPoly A) (toPoly D) j
      = subresultant (DensePoly.toPoly (liftCtoBPoly D)) (DensePoly.toPoly (bArgAmtD' A D))
          (toPoly D).natDegree ((toPoly D).natDegree - 1) j := by
  rw [lrtSubresultant, toBPoly_liftCtoBPoly, toBPoly_bArgAmtD']

/-! ### The LRT subresultant reduced to the first computable pseudo-remainder -/

/-- LRT subresultant after one computable pseudo-division step:
`C((toPoly c)^(m-j)) * lrtSubresultant A D j = (-1)^((m-j)(n-j)) * S_j(Q, prem(P,Q); m, n)` with
`n = deg D`, `m = deg D - 1`, `P = liftCtoBPoly D`, `Q = bArgAmtD' A D`. -/
theorem lrtSubresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (A D : DensePoly ℚ) (j : ℕ)
    (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hsc : Polynomial.C (toPoly c) * DensePoly.toPoly (liftCtoBPoly D)
        = DensePoly.toPoly s * DensePoly.toPoly (bArgAmtD' A D)
          + DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel (liftCtoBPoly D) (bArgAmtD' A D)))
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (DensePoly.toPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (DensePoly.toPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    Polynomial.C ((toPoly c) ^ (((toPoly D).natDegree - 1) - j))
        * lrtSubresultant (toPoly A) (toPoly D) j
      = (-1 : (ℚ[X])[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
        * subresultant (DensePoly.toPoly (bArgAmtD' A D))
            (DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel (liftCtoBPoly D) (bArgAmtD' A D)))
            ((toPoly D).natDegree - 1) (toPoly D).natDegree j := by
  rw [lrtSubresultant_eq_subresultant_toBPoly]
  exact subresultant_C_mul_eq_rem_of_bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)
    (toPoly D).natDegree ((toPoly D).natDegree - 1) j s c hsc hjm hjn hB hQ

end DeepWiki.SymbolicIntegration.Compute
