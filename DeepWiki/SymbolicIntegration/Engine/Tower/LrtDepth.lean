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

/-- Representation leaves and mathematical frontier required by the LRT solver at one dense tower depth. -/
structure DenseLrtLevelCapabilities (n : ℕ) where
  /-- Risch differential-equation solver at this depth. -/
  rischField : CRischField (DenseFracTower n)
  /-- Selected polynomial gcd operation at this depth. -/
  gcd : CPolyGcd DensePoly (DenseFracTower n)
  /-- Selected polynomial split-factor operation at this depth. -/
  splitFactor : CPolySplitFactor DensePoly (DenseFracTower n)
  /-- Denotational contract for the selected split-factor operation. -/
  lawfulSplitFactor : let _ : CPolySplitFactor DensePoly (DenseFracTower n) := splitFactor
    LawfulCPolySplitFactor DensePoly (DenseFracTower n)
  /-- Selected squarefree-decomposition operation at this depth. -/
  squarefree : CPolySquarefree DensePoly (DenseFracTower n)
  /-- Reduced algebraic-residue soundness frontier at this depth. -/
  frontier : let _ : CPolyGcd DensePoly (DenseFracTower n) := gcd
    let _ : CPolySplitFactor DensePoly (DenseFracTower n) := splitFactor
    let _ : CPolySquarefree DensePoly (DenseFracTower n) := squarefree
    PrimitiveFrontierLrt (DenseFracTower n)

/-- A selected LRT operation and its denotational contract at one dense tower depth. -/
structure LawfulDenseLrtLevel (n : ℕ) where
  /-- Leaf capabilities used to build this level. -/
  capabilities : DenseLrtLevelCapabilities n
  /-- The selected executable Risch-level operation. -/
  operation : let _ : CRischField (DenseFracTower n) := capabilities.rischField
    let _ : CPolyGcd DensePoly (DenseFracTower n) := capabilities.gcd
    let _ : CPolySplitFactor DensePoly (DenseFracTower n) := capabilities.splitFactor
    let _ : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := capabilities.lawfulSplitFactor
    let _ : CPolySquarefree DensePoly (DenseFracTower n) := capabilities.squarefree
    let _ : PrimitiveFrontierLrt (DenseFracTower n) := capabilities.frontier
    CRischLevelLrt (DenseFracTower n)
  /-- Denotational soundness of the selected operation. -/
  lawful : let _ : CRischField (DenseFracTower n) := capabilities.rischField
    let _ : CPolyGcd DensePoly (DenseFracTower n) := capabilities.gcd
    let _ : CPolySplitFactor DensePoly (DenseFracTower n) := capabilities.splitFactor
    let _ : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := capabilities.lawfulSplitFactor
    let _ : CPolySquarefree DensePoly (DenseFracTower n) := capabilities.squarefree
    let _ : PrimitiveFrontierLrt (DenseFracTower n) := capabilities.frontier
    LawfulCRischLevelLrt operation

/-- Build the constant-field LRT level from its representation leaves and reduced frontier. -/
noncomputable def lawfulDenseLrtBase (capabilities : DenseLrtLevelCapabilities 0) :
    LawfulDenseLrtLevel 0 := by
  letI : CRischField (DenseFracTower 0) := capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower 0) := capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower 0) := capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower 0) := capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower 0) := capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower 0) := capabilities.frontier
  exact { capabilities, operation := inferInstance, lawful := inferInstance }

/-- Extend a lawful LRT level by one recursive dense represented-fraction step. -/
noncomputable def LawfulDenseLrtLevel.step {n : ℕ} (_below : LawfulDenseLrtLevel n)
    (capabilities : DenseLrtLevelCapabilities (n + 1)) : LawfulDenseLrtLevel (n + 1) := by
  letI : CRischField (DenseFracTower n) := _below.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := _below.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := _below.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := _below.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := _below.capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := _below.capabilities.frontier
  letI : CRischLevelLrt (DenseFracTower n) := _below.operation
  letI : LawfulCRischLevelLrt _below.operation := _below.lawful
  letI : CRischField (DenseFracTower (n + 1)) := capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower (n + 1)) := capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower (n + 1)) := capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower (n + 1)) := capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower (n + 1)) := capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower (n + 1)) := capabilities.frontier
  exact { capabilities, operation := inferInstance, lawful := inferInstance }

/-- Build the selected lawful recursive LRT operation at depth `n` by induction over a capability family. -/
noncomputable def lawfulDenseLrtTower (capabilities : ∀ n, DenseLrtLevelCapabilities n) :
    (n : ℕ) → LawfulDenseLrtLevel n
  | 0 => lawfulDenseLrtBase (capabilities 0)
  | n + 1 => (lawfulDenseLrtTower capabilities n).step (capabilities (n + 1))

/-- The recursively selected LRT solver is formally sound at every tower depth. -/
theorem lawfulDenseLrtTower_sound (capabilities : ∀ n, DenseLrtLevelCapabilities n) (n : ℕ) :
    let level := lawfulDenseLrtTower capabilities n
    letI : CRischField (DenseFracTower n) := level.capabilities.rischField
    letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
    letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
    letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
    letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
    letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
    ∀ (Dt a d : DensePoly (DenseFracTower n)) (res : LrtResult (DenseFracTower n)),
      level.operation.integrate Dt a d = some res → IsIntegralResultLrt Dt a d res := by
  let level := lawfulDenseLrtTower capabilities n
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  letI : LawfulCRischLevelLrt level.operation := level.lawful
  dsimp only
  intro Dt a d res h
  exact level.operation.soundFormalLrt Dt a d res h

/-- At every tower depth, the recursively selected solver decides integrability on its explicit decomposition domain. -/
theorem lawfulDenseLrtTower_succeeds_iff_integrable
    (capabilities : ∀ n, DenseLrtLevelCapabilities n) (n : ℕ) :
    let level := lawfulDenseLrtTower capabilities n
    letI : CRischField (DenseFracTower n) := level.capabilities.rischField
    letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
    letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
    letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
    letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
    letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
    ∀ (Dt a d : DensePoly (DenseFracTower n)),
      primitiveRischLevelLrtDomain level.operation Dt a d → toPoly d ≠ 0 →
        (IsElementaryIntegrableLrt Dt a d ↔
          ∃ res, level.operation.integrate Dt a d = some res) := by
  let level := lawfulDenseLrtTower capabilities n
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  letI : LawfulCRischLevelLrt level.operation := level.lawful
  dsimp only
  intro Dt a d hdomain hd
  exact rischLevelLrt_succeeds_iff_integrable level.operation
    (primitiveRischLevelLrtDomain level.operation)
    Dt a d hdomain hd

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
