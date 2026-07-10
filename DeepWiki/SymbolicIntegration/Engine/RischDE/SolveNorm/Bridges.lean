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
/-- `towerFractionFieldDeriv_toRatFunc`: `towerFractionFieldDeriv [1]` agrees with
`towerDerivCFrac [1]` through `toRatFunc`. -/
theorem towerFractionFieldDeriv_toRatFunc (x : DenseFrac β) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β) (toRatFunc x)
      = toRatFunc (towerDerivCFrac ([CCommRing.one] : DensePoly β) x) := by
  rw [towerFractionFieldDeriv]
  unfold towerDerivCFrac
  rw [toRatFunc_towerDerivCFracWith]
  simp only [toPoly_list_eq]

omit [CRischField β] in
/-- `toRatFunc_weakNormalizedF`: `toRatFunc (weakNormalizedF f q') = toRatFunc f −
towerFractionFieldDeriv [1] (toRatFunc q') / toRatFunc q'`. -/
theorem toRatFunc_weakNormalizedF (f q' : DenseFrac β) :
    toRatFunc (weakNormalizedF f q')
      = toRatFunc f
        - towerFractionFieldDeriv ([CCommRing.one] : DensePoly β) (toRatFunc q') / toRatFunc q' := by
  rw [weakNormalizedF, toRatFunc_qsubNZ, toRatFunc_qmulNZ, toRatFunc_qinvNZ,
    towerFractionFieldDeriv_toRatFunc, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- `toRatFunc_solution`: `toRatFunc (qmulNZ ytilde (qinvNZ q')) = toRatFunc ytilde / toRatFunc q'`. -/
theorem toRatFunc_solution (ytilde q' : DenseFrac β) :
    toRatFunc (qmulNZ ytilde (qinvNZ q'))
      = toRatFunc ytilde / toRatFunc q' := by
  rw [toRatFunc_qmulNZ, toRatFunc_qinvNZ, div_eq_mul_inv]

end DeepWiki.SymbolicIntegration
