import DeepWiki.SymbolicIntegration.Engine.RischSolverTowerLrt
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec
import DeepWiki.SymbolicIntegration.Engine.Tower.Compositional
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Depth-indexed recursive LRT towers

Packages the dictionaries carried by `DenseFrac` so the recursive LRT construction can be stated and
proved uniformly at an arbitrary tower depth. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-- Representation leaves and mathematical frontier required by the LRT solver at one dense tower depth. -/
structure DenseLrtLevelCapabilities (n : ℕ) where
  /-- Risch differential-equation solver at this depth. -/
  rischField : CRischField (DenseFracTower n)
  /-- Selected polynomial gcd operation at this depth. -/
  gcd : CPolyGcd DensePoly (DenseFracTower n)
  /-- Denotational contract for the selected polynomial gcd operation. -/
  lawfulGcd : let _ : CPolyGcd DensePoly (DenseFracTower n) := gcd
    LawfulCPolyGcd.{0, 0} DensePoly (DenseFracTower n)
  /-- Selected polynomial split-factor operation at this depth. -/
  splitFactor : CPolySplitFactor DensePoly (DenseFracTower n)
  /-- Denotational contract for the selected split-factor operation. -/
  lawfulSplitFactor : let _ : CPolySplitFactor DensePoly (DenseFracTower n) := splitFactor
    LawfulCPolySplitFactor DensePoly (DenseFracTower n)
  /-- Selected squarefree-decomposition operation at this depth. -/
  squarefree : CPolySquarefree DensePoly (DenseFracTower n)
  /-- Denotational squarefree-decomposition contract for the selected operation. -/
  lawfulSquarefree : let _ : CPolySquarefree DensePoly (DenseFracTower n) := squarefree
    LawfulCPolySquarefree DensePoly (DenseFracTower n)
  /-- Liouville descent for genuine algebraic-residue integrability at this selected level. -/
  liouville : let _ : CPolySquarefree DensePoly (DenseFracTower n) := squarefree
    LrtLiouvilleFrontier.{0, 0, 0} (DenseFracTower n)
  /-- Reduced algebraic-residue soundness frontier at this depth. -/
  frontier : let _ : CPolyGcd DensePoly (DenseFracTower n) := gcd
    let _ : CPolySplitFactor DensePoly (DenseFracTower n) := splitFactor
    let _ : CPolySquarefree DensePoly (DenseFracTower n) := squarefree
    PrimitiveFrontierLrt (DenseFracTower n)
  /-- The selected root-free residue criterion turns a passing normal residue guard into constant logs. -/
  residueCriterion : let _ : CPolyGcd DensePoly (DenseFracTower n) := gcd
    let _ : CPolySplitFactor DensePoly (DenseFracTower n) := splitFactor
    let _ : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := lawfulSplitFactor
    let _ : CPolySquarefree DensePoly (DenseFracTower n) := squarefree
    let _ : LawfulCPolySquarefree DensePoly (DenseFracTower n) := lawfulSquarefree
    ∀ (Dt a d : DensePoly (DenseFracTower n)),
      toPoly (cResidueResultantTower Dt
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.1
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2) ≠ 0 →
      cResidueConstantGuard Dt (crNormNum Dt a d) (crNormDen Dt a d) = true →
      AllResiduesConstantLrt
        (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d))

/-- The fraction-free dense Yun realization supplies the primitive root-free residue criterion. -/
theorem primitiveLrtResidueCriterionWf {α : Type} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    [CharZero (CFieldSpec.K α)] [CFracGcdCoreWf α]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α)
    (hresultant : toPoly (cResidueResultantTower Dt
      (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.1
      (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2) ≠ 0)
    (hguard : cResidueConstantGuard Dt (crNormNum Dt a d) (crNormDen Dt a d) = true) :
    AllResiduesConstantLrt
      (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)) :=
  allResiduesConstantLrtG_of_guard hgcd Dt (crNormNum Dt a d) (crNormDen Dt a d)
    hresultant hguard

set_option maxHeartbeats 1600000 in
/-- A genuine primitive monomial supports every proper normal residual: it either has no poles or has a
nonzero residue resultant. -/
theorem normalResidueSupport_of_genuineMonomial {α : Type} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    [CharZero (CFieldSpec.K α)] [CFracGcdCoreWf α]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hden : toPoly d ≠ 0)
    (hDt0 : (toPoly Dt).natDegree = 0)
    (hproper : (toPoly a).degree < (toPoly d).degree)
    (hmonomial : GenuinePrimitiveMonomialLrt Dt) :
    toPoly (cResidueResultantTower Dt
      (cHermiteReduceTower Dt a d).2.1 (cHermiteReduceTower Dt a d).2.2) ≠ 0 ∨
      cdeg (cHermiteReduceTower Dt a d).2.2 = 0 := by
  by_cases hDstar : (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree = 0
  · right
    rw [cdegG_eq_natDegree]
    exact hDstar
  · left
    have hADdegree := hAD_degree_of_genuineMonomial hgcd Dt a d hden
      (Polynomial.primPart_ne_zero _) (by omega) hproper hmonomial
    have hAD : (toPoly (cHermiteReduceTower Dt a d).2.1).natDegree
        < (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree := by
      by_cases hnum : toPoly (cHermiteReduceTower Dt a d).2.1 = 0
      · rw [hnum, Polynomial.natDegree_zero]
        omega
      · exact Polynomial.natDegree_lt_natDegree hnum hADdegree
    exact hR0_of_normalityData hgcd Dt a d hden (Polynomial.primPart_ne_zero _) hDt0 hAD
      (lrtPoleNormalityData_of_genuineMonomial hmonomial)

/-- Assemble the standard dense LRT capabilities from the Wf gcd realization and the selected Risch,
splitting, squarefree, and Liouville frontiers. -/
noncomputable def denseLrtLevelCapabilitiesWf (n : ℕ)
    [CRischField (DenseFracTower n)]
    [CPolySplitFactor DensePoly (DenseFracTower n)]
    [LawfulCPolySplitFactor DensePoly (DenseFracTower n)]
    [CPolySquarefree DensePoly (DenseFracTower n)]
    [LawfulCPolySquarefree DensePoly (DenseFracTower n)]
    [LrtLiouvilleFrontier (DenseFracTower n)]
    [PrimitiveFrontierLrt (DenseFracTower n)] : DenseLrtLevelCapabilities n where
  rischField := inferInstance
  gcd := instCPolyGcdDenseWf
  lawfulGcd := inferInstance
  splitFactor := inferInstance
  lawfulSplitFactor := inferInstance
  squarefree := inferInstance
  lawfulSquarefree := inferInstance
  liouville := inferInstance
  frontier := inferInstance
  residueCriterion := primitiveLrtResidueCriterionWf
    (cgcdFFCoreWf_correct_of_lawful (γ := DenseFracTower n))

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

/-- A certified dense primitive stage retains LRT's algebraic-residue logarithm representation. -/
structure DenseLrtStage (n : ℕ) where
  /-- The selected executable LRT level and its denotational contract. -/
  selected : LawfulDenseLrtLevel n

/-- Run the selected LRT level after installing its representation capabilities. -/
noncomputable def DenseLrtStage.integrate (S : DenseLrtStage n) :
    DensePoly (DenseFracTower n) → DensePoly (DenseFracTower n) → DensePoly (DenseFracTower n) →
      Option (LrtResult (DenseFracTower n)) := by
  let level := S.selected
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : LawfulCPolyGcd DensePoly (DenseFracTower n) := level.capabilities.lawfulGcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  exact level.operation.integrate

/-- Run a selected LRT stage only when its returned algebraic residues are constant. -/
noncomputable def DenseLrtStage.integrateGenuine (S : DenseLrtStage n)
    (Dt a d : DensePoly (DenseFracTower n)) : Option (LrtResult (DenseFracTower n)) :=
  (S.integrate Dt a d).bind fun res =>
    if allResiduesConstantLrt res then some res else none

/-- The semantic primitive decomposition domain selected for an LRT stage. -/
noncomputable def DenseLrtStage.domain (S : DenseLrtStage n) :
    RischLevelLrtDomain (DenseFracTower n) := by
  let level := S.selected
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  exact primitiveRischLevelLrtDomain level.operation

/-- The constant-residue invariant of this stage's selected canonical normal remainder. -/
noncomputable def DenseLrtStage.normalResidueInvariant (S : DenseLrtStage n) :
    RischLevelLrtDomain (DenseFracTower n) := by
  let level := S.selected
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  exact fun Dt a d => AllResiduesConstantLrt
    (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d))

set_option maxHeartbeats 1600000

/-- A constant Hermite residual denominator has no poles, hence the symbolic LRT log list is empty and all
residues are vacuously constant. -/
theorem allResiduesConstantLrt_of_noPoles {α : Type} [CField α] [CFieldSpec α] [CDiffField α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [CFracGcdCoreWf α] (Dt a d : DensePoly α)
    (hDstar : cdeg (cHermiteReduceTower Dt a d).2.2 = 0) :
    AllResiduesConstantLrt (cIntegrateReducedLrt Dt a d) := by
  unfold AllResiduesConstantLrt allResiduesConstantLrt
  rw [cIntegrateReducedLrt]
  have hlogs : cLrtLogArg Dt (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2 = [] := by
    exact cLrtLogArgG_eq_nil_of_cdegG_zero Dt _ _ hDstar
  rw [hlogs]

set_option maxHeartbeats 200000

/-- The root-free Liouville residue guard of this stage's selected canonical normal remainder. -/
noncomputable def DenseLrtStage.normalResidueGuard (S : DenseLrtStage n) :
    RischLevelLrtDomain (DenseFracTower n) := by
  let level := S.selected
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : LawfulCPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.lawfulSquarefree
  exact fun Dt a d => cResidueConstantGuard Dt (crNormNum Dt a d) (crNormDen Dt a d) = true

/-- Nonvanishing of the selected canonical normal residue resultant. -/
noncomputable def DenseLrtStage.normalResidueResultantNonzero (S : DenseLrtStage n) :
    RischLevelLrtDomain (DenseFracTower n) := by
  let level := S.selected
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : LawfulCPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.lawfulSquarefree
  exact fun Dt a d => toPoly (cResidueResultantTower Dt
    (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.1
    (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2) ≠ 0

/-- The canonical normal residue part is supported either by a nonzero residue resultant or by having no
poles at all. The latter branch has an empty symbolic log list. -/
noncomputable def DenseLrtStage.normalResidueSupport (S : DenseLrtStage n) :
    RischLevelLrtDomain (DenseFracTower n) := by
  let level := S.selected
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : LawfulCPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.lawfulSquarefree
  exact fun Dt a d => S.normalResidueResultantNonzero Dt a d ∨
    cdeg (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2 = 0

/-- A genuine primitive monomial supplies normal-residue support for the selected canonical normal part. -/
theorem DenseLrtStage.normalResidueSupport_of_genuineMonomial (S : DenseLrtStage n)
    (Dt a d : DensePoly (DenseFracTower n)) (hdomain : S.domain Dt a d)
    (hden : toPoly d ≠ 0) (hmonomial : GenuinePrimitiveMonomialLrt Dt) :
    S.normalResidueSupport Dt a d := by
  let level := S.selected
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : LawfulCPolyGcd DensePoly (DenseFracTower n) := level.capabilities.lawfulGcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : LawfulCPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.lawfulSquarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  change primitiveRischLevelLrtDomain level.operation Dt a d at hdomain
  change S.normalResidueResultantNonzero Dt a d ∨
    cdeg (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2 = 0
  exact normalResidueSupport_of_genuineMonomial
    (cgcdFFCoreWf_correct_of_lawful (γ := DenseFracTower n)) Dt
    (crNormNum Dt a d) (crNormDen Dt a d)
    (crNormDen_ne_zero_of_lawfulSplit Dt a d hden) hdomain.1
    (crNormNum_degree_lt_crNormDen_of_lawfulSplit Dt a d hden) hmonomial

/-- Full genuine integrability descends through the certified special reconstruction to the canonical
normal remainder, so the selected root-free Liouville residue guard passes automatically. -/
theorem DenseLrtStage.normalResidueGuard_of_genuine (S : DenseLrtStage n)
    (Dt a d : DensePoly (DenseFracTower n)) (hdomain : S.domain Dt a d)
    (hden : toPoly d ≠ 0) (hintegrable : IsElementaryIntegrableGenuineLrt Dt a d) :
    S.normalResidueGuard Dt a d := by
  let level := S.selected
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : LawfulCPolyGcd DensePoly (DenseFracTower n) := level.capabilities.lawfulGcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : LawfulCPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.lawfulSquarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  letI : LawfulCRischLevelLrt level.operation := level.lawful
  letI : LrtLiouvilleFrontier (DenseFracTower n) := level.capabilities.liouville
  change primitiveRischLevelLrtDomain level.operation Dt a d at hdomain
  obtain ⟨full, hfull⟩ := hintegrable
  obtain ⟨snum, sden, hspecialRun⟩ := hdomain.2 ⟨full, hfull.1⟩
  obtain ⟨hsden, v, hderiv, hrecon⟩ := LawfulCRischLevelLrt.specialSound Dt a d snum sden hden
    hspecialRun
  have hspecial : towerFractionFieldDeriv Dt (fieldFrac snum sden)
      + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d := by
    rw [hderiv]
    exact hrecon
  have hnormal : IsElementaryIntegrableGenuineLrt Dt (crNormNum Dt a d) (crNormDen Dt a d) :=
    isElementaryIntegrableGenuineLrt_normal_of_full_of_special Dt a d
      (crNormNum Dt a d) (crNormDen Dt a d) snum sden full hsden hspecial hfull
  change cResidueConstantGuard Dt (crNormNum Dt a d) (crNormDen Dt a d) = true
  exact LrtLiouvilleFrontier.descendGenuineLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)
    (crNormDen_ne_zero_of_lawfulSplit Dt a d hden) hnormal

/-- The selected Liouville residue criterion establishes constant canonical normal residues. -/
theorem DenseLrtStage.normalResidueInvariant_of_guard (S : DenseLrtStage n)
    (Dt a d : DensePoly (DenseFracTower n))
    (hresultant : S.normalResidueResultantNonzero Dt a d)
    (hguard : S.normalResidueGuard Dt a d) : S.normalResidueInvariant Dt a d := by
  let level := S.selected
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : LawfulCPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.lawfulSquarefree
  change toPoly (cResidueResultantTower Dt
    (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.1
    (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2) ≠ 0 at hresultant
  change cResidueConstantGuard Dt (crNormNum Dt a d) (crNormDen Dt a d) = true at hguard
  change AllResiduesConstantLrt
    (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d))
  exact level.capabilities.residueCriterion Dt a d hresultant hguard

/-- The normal residue invariant follows from either the residue-resultant criterion or the no-poles
empty-log branch. -/
theorem DenseLrtStage.normalResidueInvariant_of_support (S : DenseLrtStage n)
    (Dt a d : DensePoly (DenseFracTower n))
    (hsupport : S.normalResidueSupport Dt a d)
    (hguard : S.normalResidueGuard Dt a d) : S.normalResidueInvariant Dt a d := by
  let level := S.selected
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : LawfulCPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.lawfulSquarefree
  change S.normalResidueResultantNonzero Dt a d ∨
    cdeg (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2 = 0 at hsupport
  rcases hsupport with hresultant | hnoPoles
  · exact S.normalResidueInvariant_of_guard Dt a d hresultant hguard
  · change AllResiduesConstantLrt
      (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d))
    exact allResiduesConstantLrt_of_noPoles Dt (crNormNum Dt a d) (crNormDen Dt a d) hnoPoles

/-- The semantic full-input domain for genuine primitive integration: special decomposition and the
input-independent genuine primitive-monomial condition. -/
noncomputable def DenseLrtStage.genuineFullDomain (S : DenseLrtStage n) :
  RischLevelLrtDomain (DenseFracTower n) := fun Dt a d =>
  S.domain Dt a d ∧ GenuinePrimitiveMonomialLrt Dt

/-- Every raw stage result inherits the constant-residue invariant of its canonical normal remainder. -/
theorem DenseLrtStage.allResiduesConstant_of_run (S : DenseLrtStage n)
    (Dt a d : DensePoly (DenseFracTower n)) (res : LrtResult (DenseFracTower n))
    (hsupport : S.normalResidueSupport Dt a d)
    (hguard : S.normalResidueGuard Dt a d)
    (hrun : S.integrate Dt a d = some res) : AllResiduesConstantLrt res := by
  let level := S.selected
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : LawfulCPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.lawfulSquarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  change level.operation.integrate Dt a d = some res at hrun
  exact level.operation.allResiduesConstant_of_integrate Dt a d res hrun
    (S.normalResidueInvariant_of_support Dt a d hsupport hguard)

/-- Successful primitive LRT stages satisfy the algebraic-residue integral identity. -/
theorem DenseLrtStage.sound (S : DenseLrtStage n) (Dt a d : DensePoly (DenseFracTower n))
    (res : LrtResult (DenseFracTower n))
    (hrun : S.integrate Dt a d = some res) :
    IsIntegralResultLrt Dt a d res := by
  let level := S.selected
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  letI : LawfulCRischLevelLrt level.operation := level.lawful
  change level.operation.integrate Dt a d = some res at hrun
  exact level.operation.soundFormalLrt Dt a d res hrun

/-- A successful guarded LRT stage is a genuine algebraic-residue integral result. -/
theorem DenseLrtStage.genuine_sound (S : DenseLrtStage n) (Dt a d : DensePoly (DenseFracTower n))
    (res : LrtResult (DenseFracTower n))
    (hrun : S.integrateGenuine Dt a d = some res) :
    IsGenuineIntegralResultLrt Dt a d res := by
  unfold integrateGenuine at hrun
  rw [Option.bind_eq_some_iff] at hrun
  obtain ⟨out, hraw, haccepted⟩ := hrun
  split at haccepted
  · rename_i hconstant
    simp only [Option.some.injEq] at haccepted
    subst res
    exact ⟨S.sound Dt a d out hraw, hconstant⟩
  · simp at haccepted

/-- Primitive LRT stages are relatively complete on their selected decomposition domain. -/
theorem DenseLrtStage.complete (S : DenseLrtStage n) (Dt a d : DensePoly (DenseFracTower n))
    (hdomain : S.domain Dt a d) (hden : toPoly d ≠ 0)
    (hintegrable : IsElementaryIntegrableLrt Dt a d) :
    ∃ res, S.integrate Dt a d = some res := by
  let level := S.selected
  letI : CRischField (DenseFracTower n) := level.capabilities.rischField
  letI : CPolyGcd DensePoly (DenseFracTower n) := level.capabilities.gcd
  letI : CPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.splitFactor
  letI : LawfulCPolySplitFactor DensePoly (DenseFracTower n) := level.capabilities.lawfulSplitFactor
  letI : CPolySquarefree DensePoly (DenseFracTower n) := level.capabilities.squarefree
  letI : PrimitiveFrontierLrt (DenseFracTower n) := level.capabilities.frontier
  letI : LawfulCRischLevelLrt level.operation := level.lawful
  change primitiveRischLevelLrtDomain level.operation Dt a d at hdomain
  change ∃ res, level.operation.integrate Dt a d = some res
  let complete : CompleteCRischLevelLrt level.operation
      (primitiveRischLevelLrtDomain level.operation) :=
    instCompleteCRischLevelLrtPrimitiveDomain level.operation
  exact complete.relative_complete Dt a d hdomain hden hintegrable

/-- The tower-facing primitive completeness theorem derives both the normal Liouville guard and normal-residue
support from full genuine integrability and the genuine primitive-monomial condition. -/
theorem DenseLrtStage.genuine_complete_of_fullDomain (S : DenseLrtStage n)
    (Dt a d : DensePoly (DenseFracTower n)) (hdomain : S.genuineFullDomain Dt a d)
    (hden : toPoly d ≠ 0) (hintegrable : IsElementaryIntegrableGenuineLrt Dt a d) :
    ∃ res, S.integrateGenuine Dt a d = some res := by
  have hguard := S.normalResidueGuard_of_genuine Dt a d hdomain.1 hden hintegrable
  have hsupport := S.normalResidueSupport_of_genuineMonomial Dt a d hdomain.1 hden hdomain.2
  obtain ⟨witness, hwitness, _⟩ := hintegrable
  obtain ⟨res, hrun⟩ := S.complete Dt a d hdomain.1 hden ⟨witness, hwitness⟩
  refine ⟨res, ?_⟩
  unfold integrateGenuine
  simp only [hrun, Option.bind_some]
  exact if_pos (S.allResiduesConstant_of_run Dt a d res hsupport hguard hrun)

/-- Export a guarded LRT stage through the common representation-independent integration-stage contract. -/
noncomputable def DenseLrtStage.asIntegrationStage (S : DenseLrtStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (LrtResult (DenseFracTower n))
      (fun input => IsElementaryIntegrableGenuineLrt input.Dt input.num input.den)
      (fun input res => IsGenuineIntegralResultLrt input.Dt input.num input.den res) where
  run _fuel input := S.integrateGenuine input.Dt input.num input.den
  domain input := S.genuineFullDomain input.Dt input.num input.den
  sound _fuel input output hdomain hrun :=
    S.genuine_sound input.Dt input.num input.den output hrun
  complete input hdomain hintegrable := by
    have hden : toPoly input.den ≠ 0 := by
      simpa only [toPoly_list_eq] using input.den_nonzero
    obtain ⟨output, hrun⟩ := S.genuine_complete_of_fullDomain input.Dt input.num input.den hdomain
      hden hintegrable
    exact ⟨0, output, hrun⟩

/-- A sparse LRT stage is a certified sparse-input adapter of its dense root-free backend. Its native
algebraic-residue result remains dense because LRT's residue and subresultant construction is dense. -/
structure SparseLrtStage (n : ℕ) where
  /-- Dense root-free LRT backend. -/
  dense : DenseLrtStage n

/-- Convert a sparse represented Risch input to the dense backend representation. -/
noncomputable def sparseLrtInputToDense
    (input : RischStageInput CPoly.SparsePoly (DenseFracTower n)) :
    RischStageInput DensePoly (DenseFracTower n) where
  Dt := CPolyEngine.convert input.Dt
  num := CPolyEngine.convert input.num
  den := CPolyEngine.convert input.den
  den_nonzero := by simpa only [CPolyEngine.toPoly_convert] using input.den_nonzero

/-- View a dense LRT stage as its certified sparse-input adapter. -/
noncomputable def DenseLrtStage.toSparse (S : DenseLrtStage n) : SparseLrtStage n := ⟨S⟩

/-- Export the sparse LRT adapter through the common stage interface without coercing algebraic-residue logs
into ordinary logarithms. -/
noncomputable def SparseLrtStage.asIntegrationStage (S : SparseLrtStage n) :
    IntegrationStage (RischStageInput CPoly.SparsePoly (DenseFracTower n))
      (LrtResult (DenseFracTower n))
      (fun input =>
        IsElementaryIntegrableGenuineLrt (sparseLrtInputToDense input).Dt
          (sparseLrtInputToDense input).num (sparseLrtInputToDense input).den)
      (fun input res =>
        IsGenuineIntegralResultLrt (sparseLrtInputToDense input).Dt
          (sparseLrtInputToDense input).num (sparseLrtInputToDense input).den res) where
  run _fuel input := S.dense.integrateGenuine (sparseLrtInputToDense input).Dt
    (sparseLrtInputToDense input).num (sparseLrtInputToDense input).den
  domain input := S.dense.genuineFullDomain (sparseLrtInputToDense input).Dt
    (sparseLrtInputToDense input).num (sparseLrtInputToDense input).den
  sound _fuel input output _hdomain hrun :=
    S.dense.genuine_sound (sparseLrtInputToDense input).Dt (sparseLrtInputToDense input).num
      (sparseLrtInputToDense input).den output hrun
  complete input hdomain hintegrable := by
    obtain ⟨output, hrun⟩ := S.dense.genuine_complete_of_fullDomain
      (sparseLrtInputToDense input).Dt (sparseLrtInputToDense input).num
      (sparseLrtInputToDense input).den hdomain (sparseLrtInputToDense input).den_nonzero hintegrable
    exact ⟨0, output, hrun⟩

/-- The recursively selected LRT operation at any depth is a certified primitive stage. -/
noncomputable def denseLrtTowerStage (capabilities : ∀ n, DenseLrtLevelCapabilities n) (n : ℕ) :
    DenseLrtStage n :=
  ⟨lawfulDenseLrtTower capabilities n⟩

/-- Every selected finite primitive LRT stage is sound with its algebraic-residue logarithms. -/
theorem denseLrtTowerStage_sound (capabilities : ∀ n, DenseLrtLevelCapabilities n) (n : ℕ)
    (Dt a d : DensePoly (DenseFracTower n)) (res : LrtResult (DenseFracTower n))
    (hrun : (denseLrtTowerStage capabilities n).integrate Dt a d = some res) :
    IsIntegralResultLrt Dt a d res :=
  (denseLrtTowerStage capabilities n).sound Dt a d res hrun

/-- Every successful guarded finite primitive stage has constant algebraic residues. -/
theorem denseLrtTowerStage_genuine_sound (capabilities : ∀ n, DenseLrtLevelCapabilities n) (n : ℕ)
    (Dt a d : DensePoly (DenseFracTower n)) (res : LrtResult (DenseFracTower n))
    (hrun : (denseLrtTowerStage capabilities n).integrateGenuine Dt a d = some res) :
    IsGenuineIntegralResultLrt Dt a d res :=
  (denseLrtTowerStage capabilities n).genuine_sound Dt a d res hrun

/-- Every selected finite primitive LRT stage is relatively complete on its decomposition domain. -/
theorem denseLrtTowerStage_complete (capabilities : ∀ n, DenseLrtLevelCapabilities n) (n : ℕ)
    (Dt a d : DensePoly (DenseFracTower n))
    (hdomain : (denseLrtTowerStage capabilities n).domain Dt a d) (hden : toPoly d ≠ 0)
    (hintegrable : IsElementaryIntegrableLrt Dt a d) :
    ∃ res, (denseLrtTowerStage capabilities n).integrate Dt a d = some res :=
  (denseLrtTowerStage capabilities n).complete Dt a d hdomain hden hintegrable

/-- Every finite primitive stage is relatively complete on its full genuine domain. -/
theorem denseLrtTowerStage_genuine_complete_of_fullDomain
    (capabilities : ∀ n, DenseLrtLevelCapabilities n) (n : ℕ)
    (Dt a d : DensePoly (DenseFracTower n))
    (hdomain : (denseLrtTowerStage capabilities n).genuineFullDomain Dt a d) (hden : toPoly d ≠ 0)
    (hintegrable : IsElementaryIntegrableGenuineLrt Dt a d) :
    ∃ res, (denseLrtTowerStage capabilities n).integrateGenuine Dt a d = some res :=
  (denseLrtTowerStage capabilities n).genuine_complete_of_fullDomain Dt a d hdomain hden hintegrable

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
