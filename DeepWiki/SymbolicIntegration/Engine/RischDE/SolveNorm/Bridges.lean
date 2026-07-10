import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveNorm.Construction

/-! # Denotation bridges for weak-normalized Risch-DE solving

Field-level readings of the weak-normalized solver's `CFrac` constructions. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CRischField β] in
/-- `towerFractionFieldDerivG_toCFracG`: `towerFractionFieldDeriv [1]` agrees with
`towerDerivCFrac [1]` through `toCFrac`. -/
theorem towerFractionFieldDerivG_toCFracG (x : DenseFrac β) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β) (toCFrac x)
      = toCFrac (towerDerivCFrac ([CCommRing.one] : DensePoly β) x) := by
  rw [towerFractionFieldDeriv, toCFracG_towerDerivCFracG]

omit [CRischField β] in
/-- `toCFracG_weakNormalizedF`: `toCFrac (weakNormalizedF f q') = toCFrac f −
towerFractionFieldDeriv [1] (toCFrac q') / toCFrac q'`. -/
theorem toCFracG_weakNormalizedF (f q' : DenseFrac β) :
    toCFrac (weakNormalizedF f q')
      = toCFrac f
        - towerFractionFieldDeriv ([CCommRing.one] : DensePoly β) (toCFrac q') / toCFrac q' := by
  rw [weakNormalizedF, toCFracG_qsubNZG, toCFracG_qmulNZG, toCFracG_qinvNZG,
    towerFractionFieldDerivG_toCFracG, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- `toCFracG_solution`: `toCFrac (qmulNZ ytilde (qinvNZ q')) = toCFrac ytilde / toCFrac q'`. -/
theorem toCFracG_solution (ytilde q' : DenseFrac β) :
    toCFrac (qmulNZ ytilde (qinvNZ q'))
      = toCFrac ytilde / toCFrac q' := by
  rw [toCFracG_qmulNZG, toCFracG_qinvNZG, div_eq_mul_inv]

end DeepWiki.SymbolicIntegration
