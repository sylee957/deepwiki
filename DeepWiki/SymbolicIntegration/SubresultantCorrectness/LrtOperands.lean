import DeepWiki.SymbolicIntegration.SubresultantCorrectness.PseudoRemainderStep
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtSubresultant

/-! # LRT operands for subresultant correctness
Identifies the computable LRT inputs inside `BPoly` and specializes the first
pseudo-remainder subresultant step to those operands. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Identifying the LRT operands: the computable lifts realize `D.map C`, `A - t*D'` -/

/-- `toPoly (cC c) = C c`: the constant-`CPoly` lift realizes the `ℚ[X]` constant. -/
@[simp] theorem toPoly_cC (c : ℚ) : toPoly (cC c) = Polynomial.C c := by
  rw [cC, toPoly_cnorm]
  simp [toPoly_cons]

/-- `toBPoly (liftCtoBPoly p) = (toPoly p).map C`: `liftCtoBPoly` realizes the coefficient embedding. -/
theorem toBPoly_liftCtoBPoly (p : CPoly) :
    toBPoly (liftCtoBPoly p) = (toPoly p).map (Polynomial.C : ℚ →+* ℚ[X]) := by
  induction p with
  | nil => simp [liftCtoBPoly]
  | cons a as ih =>
    show toBPoly (cC a :: liftCtoBPoly as) = _
    rw [toBPoly_cons, toPoly_cons, ih, toPoly_cC, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C]

/-- `toPoly ctVar = X`: the computable `t`-variable lifts to the indeterminate `X ∈ ℚ[t]`. -/
@[simp] theorem toPoly_ctVar : toPoly ctVar = (Polynomial.X : ℚ[X]) := by
  rw [ctVar]; simp [toPoly_cons]

/-- `toBPoly (bArgAmtD' A D) = (toPoly A).map C - C X * (derivative (toPoly D)).map C`: the LRT second
operand `A - t*D'`. -/
theorem toBPoly_bArgAmtD' (A D : CPoly) :
    toBPoly (bArgAmtD' A D)
      = (toPoly A).map (Polynomial.C : ℚ →+* ℚ[X])
        - Polynomial.C Polynomial.X * (derivative (toPoly D)).map (Polynomial.C : ℚ →+* ℚ[X]) := by
  rw [bArgAmtD', toBPoly_bsub, toBPoly_liftCtoBPoly, toBPoly_bscaleC, toBPoly_liftCtoBPoly,
    toPoly_ctVar, toPoly_cderiv]

/-- `lrtSubresultant A D j` is the abstract subresultant of the `toBPoly` images of the computable
operands at formal degrees `deg D`, `deg D - 1`. -/
theorem lrtSubresultant_eq_subresultant_toBPoly (A D : CPoly) (j : ℕ) :
    lrtSubresultant (toPoly A) (toPoly D) j
      = subresultant (toBPoly (liftCtoBPoly D)) (toBPoly (bArgAmtD' A D))
          (toPoly D).natDegree ((toPoly D).natDegree - 1) j := by
  rw [lrtSubresultant, toBPoly_liftCtoBPoly, toBPoly_bArgAmtD']

/-! ### The LRT subresultant reduced to the first computable pseudo-remainder -/

/-- LRT subresultant after one computable pseudo-division step:
`C((toPoly c)^(m-j)) * lrtSubresultant A D j = (-1)^((m-j)(n-j)) * S_j(Q, prem(P,Q); m, n)` with
`n = deg D`, `m = deg D - 1`, `P = liftCtoBPoly D`, `Q = bArgAmtD' A D`. -/
theorem lrtSubresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (A D : CPoly) (j : ℕ)
    (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly (liftCtoBPoly D)
        = toBPoly s * toBPoly (bArgAmtD' A D)
          + toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (toBPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (toBPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    Polynomial.C ((toPoly c) ^ (((toPoly D).natDegree - 1) - j))
        * lrtSubresultant (toPoly A) (toPoly D) j
      = (-1 : (ℚ[X])[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
        * subresultant (toBPoly (bArgAmtD' A D))
            (toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
            ((toPoly D).natDegree - 1) (toPoly D).natDegree j := by
  rw [lrtSubresultant_eq_subresultant_toBPoly]
  exact subresultant_C_mul_eq_rem_of_bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)
    (toPoly D).natDegree ((toPoly D).natDegree - 1) j s c hsc hjm hjn hB hQ

end DeepWiki.SymbolicIntegration.Compute
