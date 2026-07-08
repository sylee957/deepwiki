import DeepWiki.SymbolicIntegration.Computable.RischDE.SolveNorm.Construction

/-! # Denotation bridges for weak-normalized Risch-DE solving

Field-level readings of the weak-normalized solver's `QFunNZG` constructions. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CRischField β] in
/-- `towerFractionFieldDerivG_toQFunNZG`: `towerFractionFieldDerivG [1]` agrees with
`towerDerivQFunNZG [1]` through `toQFunNZG`. -/
theorem towerFractionFieldDerivG_toQFunNZG (x : QFunNZG β) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG x)
      = toQFunNZG (towerDerivQFunNZG ([CField.one] : CPolyG β) x) := by
  rw [towerFractionFieldDerivG, toQFunNZG_towerDerivQFunNZG]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β]
  [Algebra ℚ (CFieldSpec.K β)] in
/-- `toQFunNZG_qOfPolyNZG_ne_zero`: the lift `q' = q/1` has nonzero field image when `q` is nonzero. -/
theorem toQFunNZG_qOfPolyNZG_ne_zero (q : CPolyG β) (hq : CPolyG.cisZeroG q = false) :
    toQFunNZG (qOfPolyNZG q) ≠ 0 := by
  rw [toQFunNZG]
  show amG β (toPolyG q) / amG β (toPolyG ([CField.one] : CPolyG β)) ≠ 0
  simp only [denote, map_one, mul_zero, add_zero, div_one]
  exact amG_toPolyG_ne_zero (CPolyG.toPolyG_ne_zero_of_cisZeroG_false hq)

omit [CRischField β] in
/-- `toQFunNZG_weakNormalizedF`: `toQFunNZG (weakNormalizedF f q') = toQFunNZG f −
towerFractionFieldDerivG [1] (toQFunNZG q') / toQFunNZG q'`. -/
theorem toQFunNZG_weakNormalizedF (f q' : QFunNZG β) :
    toQFunNZG (weakNormalizedF f q')
      = toQFunNZG f
        - towerFractionFieldDerivG ([CField.one] : CPolyG β) (toQFunNZG q') / toQFunNZG q' := by
  rw [weakNormalizedF, toQFunNZG_qsubNZG, toQFunNZG_qmulNZG, toQFunNZG_qinvNZG,
    towerFractionFieldDerivG_toQFunNZG, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- `toQFunNZG_solution`: `toQFunNZG (qmulNZG ytilde (qinvNZG q')) = toQFunNZG ytilde / toQFunNZG q'`. -/
theorem toQFunNZG_solution (ytilde q' : QFunNZG β) :
    toQFunNZG (qmulNZG ytilde (qinvNZG q'))
      = toQFunNZG ytilde / toQFunNZG q' := by
  rw [toQFunNZG_qmulNZG, toQFunNZG_qinvNZG, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- `toQFunNZG_scaledRHS`: `toQFunNZG (qmulNZG q' g) = toQFunNZG q' * toQFunNZG g`. -/
theorem toQFunNZG_scaledRHS (q' g : QFunNZG β) :
    toQFunNZG (qmulNZG q' g) = toQFunNZG q' * toQFunNZG g :=
  toQFunNZG_qmulNZG q' g

end DeepWiki.SymbolicIntegration
