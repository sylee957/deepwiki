import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveNorm.Construction

/-! # Denotation bridges for weak-normalized Risch-DE solving

Field-level readings of the weak-normalized solver's `QFunNZ` constructions. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZ GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CRischField β] in
/-- `towerFractionFieldDerivG_toQFunNZG`: `towerFractionFieldDeriv [1]` agrees with
`towerDerivQFunNZ [1]` through `toQFunNZ`. -/
theorem towerFractionFieldDerivG_toQFunNZG (x : QFunNZ β) :
    towerFractionFieldDeriv ([CField.one] : CPoly β) (toQFunNZ x)
      = toQFunNZ (towerDerivQFunNZ ([CField.one] : CPoly β) x) := by
  rw [towerFractionFieldDeriv, toQFunNZG_towerDerivQFunNZG]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β]
  [Algebra ℚ (CFieldSpec.K β)] in
/-- `toQFunNZG_qOfPolyNZG_ne_zero`: the lift `q' = q/1` has nonzero field image when `q` is nonzero. -/
theorem toQFunNZG_qOfPolyNZG_ne_zero (q : CPoly β) (hq : CPoly.cisZero q = false) :
    toQFunNZ (qOfPolyNZ q) ≠ 0 := by
  rw [toQFunNZ]
  show am β (toPoly q) / am β (toPoly ([CField.one] : CPoly β)) ≠ 0
  simp only [denote, map_one, mul_zero, add_zero, div_one]
  exact amG_toPolyG_ne_zero (CPoly.toPolyG_ne_zero_of_cisZeroG_false hq)

omit [CRischField β] in
/-- `toQFunNZG_weakNormalizedF`: `toQFunNZ (weakNormalizedF f q') = toQFunNZ f −
towerFractionFieldDeriv [1] (toQFunNZ q') / toQFunNZ q'`. -/
theorem toQFunNZG_weakNormalizedF (f q' : QFunNZ β) :
    toQFunNZ (weakNormalizedF f q')
      = toQFunNZ f
        - towerFractionFieldDeriv ([CField.one] : CPoly β) (toQFunNZ q') / toQFunNZ q' := by
  rw [weakNormalizedF, toQFunNZG_qsubNZG, toQFunNZG_qmulNZG, toQFunNZG_qinvNZG,
    towerFractionFieldDerivG_toQFunNZG, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- `toQFunNZG_solution`: `toQFunNZ (qmulNZ ytilde (qinvNZ q')) = toQFunNZ ytilde / toQFunNZ q'`. -/
theorem toQFunNZG_solution (ytilde q' : QFunNZ β) :
    toQFunNZ (qmulNZ ytilde (qinvNZ q'))
      = toQFunNZ ytilde / toQFunNZ q' := by
  rw [toQFunNZG_qmulNZG, toQFunNZG_qinvNZG, div_eq_mul_inv]

omit [CDiffField β] [CDiffFieldSpec β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] in
/-- `toQFunNZG_scaledRHS`: `toQFunNZ (qmulNZ q' g) = toQFunNZ q' * toQFunNZ g`. -/
theorem toQFunNZG_scaledRHS (q' g : QFunNZ β) :
    toQFunNZ (qmulNZ q' g) = toQFunNZ q' * toQFunNZ g :=
  toQFunNZG_qmulNZG q' g

end DeepWiki.SymbolicIntegration
