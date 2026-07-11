import DeepWiki.SymbolicIntegration.Engine.RischSolverTowerLrt
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec

/-! # Depth-indexed recursive LRT towers

Packages the dictionaries carried by `DenseFrac` so the recursive LRT construction can be stated and
proved uniformly at an arbitrary tower depth. -/

namespace DeepWiki.SymbolicIntegration

/-- A carrier together with the lawful computable field and differential dictionaries needed by a tower step. -/
structure DenseTowerCarrier where
  /-- The executable carrier at this tower depth. -/
  Carrier : Type
  /-- Computable field operations on the carrier. -/
  cfield : CField Carrier
  /-- Denotation of the computable field into a mathematical field. -/
  cfieldSpec : @CFieldSpec Carrier cfield
  /-- Computable derivation on the carrier. -/
  cdiffField : @CDiffField Carrier cfield
  /-- Denotational law for the computable derivation. -/
  algebraQ : let _ : CField Carrier := cfield
    let _ : CFieldSpec Carrier := cfieldSpec
    Algebra ℚ (CFieldSpec.K Carrier)
  /-- Characteristic-zero law at the denotation field. -/
  charZero : let _ : CField Carrier := cfield
    let _ : CFieldSpec Carrier := cfieldSpec
    CharZero (CFieldSpec.K Carrier)
  /-- Denotational differential-field contract on the carrier. -/
  cdiffFieldSpec : @CDiffFieldSpec Carrier cfield cfieldSpec cdiffField

/-- The constant-field base of the dense recursive fraction tower. -/
noncomputable def denseTowerBase : DenseTowerCarrier where
  Carrier := ℚ
  cfield := inferInstance
  cfieldSpec := inferInstance
  cdiffField := inferInstance
  algebraQ := inferInstance
  charZero := inferInstance
  cdiffFieldSpec := inferInstance

/-- Extend a packaged carrier by one dense represented-fraction level. -/
noncomputable def DenseTowerCarrier.step (T : DenseTowerCarrier) : DenseTowerCarrier := by
  letI : CField T.Carrier := T.cfield
  letI : CFieldSpec T.Carrier := T.cfieldSpec
  letI : CDiffField T.Carrier := T.cdiffField
  letI : Algebra ℚ (CFieldSpec.K T.Carrier) := T.algebraQ
  letI : CharZero (CFieldSpec.K T.Carrier) := T.charZero
  letI : CDiffFieldSpec T.Carrier := T.cdiffFieldSpec
  exact {
    Carrier := DenseFrac T.Carrier
    cfield := inferInstance
    cfieldSpec := inferInstance
    cdiffField := inferInstance
    algebraQ := inferInstance
    charZero := inferInstance
    cdiffFieldSpec := inferInstance
  }

/-- The packaged dense represented-fraction carrier obtained after `n` recursive tower steps. -/
noncomputable def denseTowerCarrier : ℕ → DenseTowerCarrier
  | 0 => denseTowerBase
  | n + 1 => (denseTowerCarrier n).step

/-- The executable dense represented-fraction carrier at tower depth `n`. -/
abbrev DenseFracTower (n : ℕ) : Type := (denseTowerCarrier n).Carrier

/-- The depth-indexed dense tower carries computable field operations. -/
noncomputable instance instCFieldDenseFracTower (n : ℕ) : CField (DenseFracTower n) :=
  (denseTowerCarrier n).cfield

/-- The depth-indexed dense tower carries a lawful field denotation. -/
noncomputable instance instCFieldSpecDenseFracTower (n : ℕ) : CFieldSpec (DenseFracTower n) :=
  (denseTowerCarrier n).cfieldSpec

/-- The depth-indexed dense tower carries a computable derivation. -/
noncomputable instance instCDiffFieldDenseFracTower (n : ℕ) : CDiffField (DenseFracTower n) :=
  (denseTowerCarrier n).cdiffField

/-- The denotation field at every dense tower depth is a `ℚ`-algebra. -/
noncomputable instance instAlgebraQDenseFracTower (n : ℕ) :
    Algebra ℚ (CFieldSpec.K (DenseFracTower n)) :=
  (denseTowerCarrier n).algebraQ

/-- The denotation field at every dense tower depth has characteristic zero. -/
noncomputable instance instCharZeroDenseFracTower (n : ℕ) :
    CharZero (CFieldSpec.K (DenseFracTower n)) :=
  (denseTowerCarrier n).charZero

/-- The depth-indexed dense tower derivation satisfies its denotational contract. -/
noncomputable instance instCDiffFieldSpecDenseFracTower (n : ℕ) :
    CDiffFieldSpec (DenseFracTower n) :=
  (denseTowerCarrier n).cdiffFieldSpec

/-- Tower depth zero is the constant field `ℚ`. -/
theorem denseFracTower_zero : DenseFracTower 0 = ℚ := rfl

/-- A successor tower depth is one dense represented-fraction extension of the preceding depth. -/
theorem denseFracTower_succ (n : ℕ) :
    DenseFracTower (n + 1) = DenseFrac (DenseFracTower n) := rfl

open DensePoly CFrac

/-- One recursive LRT tower step preserves formal soundness at every depth. -/
theorem lrtTowerStep_sound (n : ℕ)
    [CPolyGcd DensePoly (DenseFracTower n)]
    [CPolySplitFactor DensePoly (DenseFracTower n)]
    [CPolySquarefree DensePoly (DenseFracTower n)]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [C : CRischLevelLrt (DenseFracTower n)] [LawfulCRischLevelLrt C]
    [CRischField (DenseFracTower (n + 1))]
    [CPolyGcd DensePoly (DenseFracTower (n + 1))]
    [CPolySplitFactor DensePoly (DenseFracTower (n + 1))]
    [LawfulCPolySplitFactor DensePoly (DenseFracTower (n + 1))]
    [CPolySquarefree DensePoly (DenseFracTower (n + 1))]
    [PrimitiveFrontierLrt (DenseFracTower (n + 1))]
    (Dt a d : DensePoly (DenseFracTower (n + 1)))
    (res : LrtResult (DenseFracTower (n + 1)))
    (h : (inferInstance : CRischLevelLrt (DenseFracTower (n + 1))).integrate Dt a d = some res) :
    IsIntegralResultLrt Dt a d res :=
  (inferInstance : CRischLevelLrt (DenseFracTower (n + 1))).soundFormalLrt Dt a d res h

/-- At every successor depth, the recursive LRT step is relatively complete on its explicit decomposition domain. -/
theorem lrtTowerStep_succeeds_iff_integrable (n : ℕ)
    [CPolyGcd DensePoly (DenseFracTower n)]
    [CPolySplitFactor DensePoly (DenseFracTower n)]
    [CPolySquarefree DensePoly (DenseFracTower n)]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [C : CRischLevelLrt (DenseFracTower n)] [LawfulCRischLevelLrt C]
    [CRischField (DenseFracTower (n + 1))]
    [CPolyGcd DensePoly (DenseFracTower (n + 1))]
    [CPolySplitFactor DensePoly (DenseFracTower (n + 1))]
    [LawfulCPolySplitFactor DensePoly (DenseFracTower (n + 1))]
    [CPolySquarefree DensePoly (DenseFracTower (n + 1))]
    [PrimitiveFrontierLrt (DenseFracTower (n + 1))]
    (Dt a d : DensePoly (DenseFracTower (n + 1)))
    (hdomain : primitiveRischLevelLrtDomain
      (inferInstance : CRischLevelLrt (DenseFracTower (n + 1))) Dt a d)
    (hd : toPoly d ≠ 0) :
    IsElementaryIntegrableLrt Dt a d ↔
      ∃ res, (inferInstance : CRischLevelLrt (DenseFracTower (n + 1))).integrate Dt a d = some res :=
  rischLevelLrt_succeeds_iff_integrable
    (inferInstance : CRischLevelLrt (DenseFracTower (n + 1)))
    (primitiveRischLevelLrtDomain
      (inferInstance : CRischLevelLrt (DenseFracTower (n + 1))))
    Dt a d hdomain hd

end DeepWiki.SymbolicIntegration
