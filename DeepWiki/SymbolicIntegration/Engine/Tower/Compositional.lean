import DeepWiki.SymbolicIntegration.Engine.RischLevelConvert
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementary
import DeepWiki.SymbolicIntegration.Engine.Tower.Stage

/-! # Finite compositional Risch towers

A selected Risch level packages its executable operation with soundness, genuine-log, and relative
completeness contracts. A finite dense tower is built recursively; each successor receives the
immediately lower certified stage, which exposes the canonical coefficient adapter. Sparse levels
are adapters of dense stages, never separate tower algorithms.
-/

namespace DeepWiki.SymbolicIntegration

variable {n : ℕ}

/-- A represented Risch input with its required nonzero denominator certificate. -/
structure RischStageInput (P : Type → Type) [CPoly P] (α : Type) [CCommRing α] [CRingSpec α] where
  /-- Monomial derivative. -/
  Dt : P α
  /-- Numerator of the integrand. -/
  num : P α
  /-- Denominator of the integrand. -/
  den : P α
  /-- The represented denominator denotes a nonzero polynomial. -/
  den_nonzero : CPoly.toPoly den ≠ 0

/-- A represented `IntegralResult` with genuine constant coefficients and nonzero logarithm arguments. -/
def IsGenuineRischStageResult {P : Type → Type} [CPoly P] [CPolyEngine P]
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] (input : RischStageInput P α)
    (res : IntegralResult α P) : Prop :=
  IsIntegralResultP input.Dt input.num input.den res ∧
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
    (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0)

/-- A selected dense Risch level and its semantic contracts at a fixed fraction-tower depth. -/
structure DenseRischStage (n : ℕ) where
  /-- Executable level solver selected at this depth. -/
  level : CRischLevel DensePoly (DenseFracTower n)
  /-- Semantic domain selected for this level. -/
  domain : RischLevelDomain DensePoly (DenseFracTower n)
  /-- Denotational soundness of the selected level. -/
  lawful : LawfulCRischLevel level domain
  /-- Genuine Liouville logarithms of successful outputs. -/
  genuine : let _ : LawfulCRischLevel level domain := lawful
    LawfulGenuineCRischLevel level domain
  /-- Relative completeness on the selected semantic domain. -/
  complete : let _ : LawfulCRischLevel level domain := lawful
    CompleteCRischLevel level domain

/-- A selected sparse Risch level and its transported semantic contracts at a fixed depth. -/
structure SparseRischStage (n : ℕ) where
  /-- Executable sparse level solver selected at this depth. -/
  level : CRischLevel CPoly.SparsePoly (DenseFracTower n)
  /-- Semantic sparse domain selected for this level. -/
  domain : RischLevelDomain CPoly.SparsePoly (DenseFracTower n)
  /-- Denotational soundness of the selected sparse level. -/
  lawful : LawfulCRischLevel level domain
  /-- Genuine Liouville logarithms of successful sparse outputs. -/
  genuine : let _ : LawfulCRischLevel level domain := lawful
    LawfulGenuineCRischLevel level domain
  /-- Relative completeness on the selected sparse semantic domain. -/
  complete : let _ : LawfulCRischLevel level domain := lawful
    CompleteCRischLevel level domain

/-- Export a selected dense Risch level through the common integration-stage interface. -/
noncomputable def DenseRischStage.asIntegrationStage (S : DenseRischStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (IntegralResult (DenseFracTower n))
      (fun input => IsRischLevelIntegrable input.Dt input.num input.den)
      IsGenuineRischStageResult := by
  letI : LawfulCRischLevel S.level S.domain := S.lawful
  letI : LawfulGenuineCRischLevel S.level S.domain := S.genuine
  letI : CompleteCRischLevel S.level S.domain := S.complete
  refine
    { run := fun fuel input => S.level.integrate fuel input.Dt input.num input.den
      domain := fun input => S.domain input.Dt input.num input.den
      sound := ?_
      complete := ?_ }
  · intro fuel input output hdomain hrun
    refine ⟨LawfulCRischLevel.sound fuel input.Dt input.num input.den output hdomain
      input.den_nonzero hrun, ?_, ?_⟩
    · exact LawfulGenuineCRischLevel.coefficients_constant fuel input.Dt input.num input.den output
        hdomain input.den_nonzero hrun
    · exact LawfulGenuineCRischLevel.arguments_nonzero fuel input.Dt input.num input.den output
        hdomain input.den_nonzero hrun
  · intro input hdomain hintegrable
    exact CompleteCRischLevel.relative_complete input.Dt input.num input.den hdomain
      input.den_nonzero hintegrable

/-- Export a selected sparse adapter through the same common integration-stage interface. -/
noncomputable def SparseRischStage.asIntegrationStage (S : SparseRischStage n) :
    IntegrationStage (RischStageInput CPoly.SparsePoly (DenseFracTower n))
      (IntegralResult (DenseFracTower n) CPoly.SparsePoly)
      (fun input => IsRischLevelIntegrable input.Dt input.num input.den)
      IsGenuineRischStageResult := by
  letI : LawfulCRischLevel S.level S.domain := S.lawful
  letI : LawfulGenuineCRischLevel S.level S.domain := S.genuine
  letI : CompleteCRischLevel S.level S.domain := S.complete
  refine
    { run := fun fuel input => S.level.integrate fuel input.Dt input.num input.den
      domain := fun input => S.domain input.Dt input.num input.den
      sound := ?_
      complete := ?_ }
  · intro fuel input output hdomain hrun
    refine ⟨LawfulCRischLevel.sound fuel input.Dt input.num input.den output hdomain
      input.den_nonzero hrun, ?_, ?_⟩
    · exact LawfulGenuineCRischLevel.coefficients_constant fuel input.Dt input.num input.den output
        hdomain input.den_nonzero hrun
    · exact LawfulGenuineCRischLevel.arguments_nonzero fuel input.Dt input.num input.den output
        hdomain input.den_nonzero hrun
  · intro input hdomain hintegrable
    exact CompleteCRischLevel.relative_complete input.Dt input.num input.den hdomain
      input.den_nonzero hintegrable

/-- The recursive elementary coefficient domain induced by a certified lower dense Risch level. -/
def DenseRischStage.coefficientDomain (S : DenseRischStage n) :
    RecursiveElementaryDomain (α := DenseFrac (DenseFracTower n)) :=
  recursiveElementaryOfRischLevelCompositionalDomain S.domain

/-- The lower selected level supplies a complete certificate-checked coefficient adapter. -/
theorem DenseRischStage.coefficient_complete (S : DenseRischStage n) :
    CompleteCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel S.level)
      S.coefficientDomain := by
  letI : LawfulCRischLevel S.level S.domain := S.lawful
  letI : LawfulGenuineCRischLevel S.level S.domain := S.genuine
  letI : CompleteCRischLevel S.level S.domain := S.complete
  exact completeCRecursiveElementaryIntegratorOfRischLevelCompositional S.level S.domain

/-- Convert a certified dense level into its certified sparse adapter. -/
noncomputable def DenseRischStage.toSparse (S : DenseRischStage n) : SparseRischStage n := by
  letI : LawfulCRischLevel S.level S.domain := S.lawful
  letI : LawfulGenuineCRischLevel S.level S.domain := S.genuine
  letI : CompleteCRischLevel S.level S.domain := S.complete
  let sparseLevel := convertRischLevel (Q := CPoly.SparsePoly) S.level
  let sparseDomain := convertRischLevelDomain (Q := CPoly.SparsePoly) S.domain
  letI : LawfulCRischLevel sparseLevel sparseDomain := inferInstance
  letI : LawfulGenuineCRischLevel sparseLevel sparseDomain := inferInstance
  letI : CompleteCRischLevel sparseLevel sparseDomain := inferInstance
  exact ⟨sparseLevel, sparseDomain, inferInstance, inferInstance, inferInstance⟩

/-- A finite dense tower is built from a base stage by a successor constructor that receives the
immediately lower certified stage. -/
structure DenseRischTowerScheme where
  /-- Certified selected level at the constant base. -/
  base : DenseRischStage 0
  /-- Build the next selected level from the immediately lower certified level. -/
  step : ∀ n, DenseRischStage n → DenseRischStage (n + 1)

/-- The certified dense stage selected by a tower scheme at depth `n`. -/
def DenseRischTowerScheme.stage (T : DenseRischTowerScheme) : (n : ℕ) → DenseRischStage n
  | 0 => T.base
  | n + 1 => T.step n (T.stage n)

/-- Induction over the finite tower exposes soundness at every selected depth. -/
theorem DenseRischTowerScheme.stage_lawful (T : DenseRischTowerScheme) (n : ℕ) :
    LawfulCRischLevel (T.stage n).level (T.stage n).domain := by
  induction n with
  | zero => exact T.base.lawful
  | succ n _ => exact (T.step n (T.stage n)).lawful

/-- Induction over the finite tower exposes genuine logarithms at every selected depth. -/
theorem DenseRischTowerScheme.stage_genuine (T : DenseRischTowerScheme) (n : ℕ) :
    let _ : LawfulCRischLevel (T.stage n).level (T.stage n).domain := T.stage_lawful n
    LawfulGenuineCRischLevel (T.stage n).level (T.stage n).domain := by
  induction n with
  | zero => exact T.base.genuine
  | succ n _ => exact (T.step n (T.stage n)).genuine

/-- Induction over the finite tower exposes relative completeness at every selected depth. -/
theorem DenseRischTowerScheme.stage_complete (T : DenseRischTowerScheme) (n : ℕ) :
    let _ : LawfulCRischLevel (T.stage n).level (T.stage n).domain := T.stage_lawful n
    CompleteCRischLevel (T.stage n).level (T.stage n).domain := by
  induction n with
  | zero => exact T.base.complete
  | succ n _ => exact (T.step n (T.stage n)).complete

/-- View a concrete dense Risch tower through the representation-independent stage recursion. -/
noncomputable def DenseRischTowerScheme.asIntegrationTowerScheme (T : DenseRischTowerScheme) :
    IntegrationTowerScheme (fun n => RischStageInput DensePoly (DenseFracTower n)) where
  Output _ := IntegralResult (DenseFracTower _)
  Integrable _ input := IsRischLevelIntegrable input.Dt input.num input.den
  Correct _ input result := IsGenuineRischStageResult input result
  base := T.base.asIntegrationStage
  step n _ := (T.step n (T.stage n)).asIntegrationStage

/-- The common stage selected from a concrete dense tower is its original certified stage adapter. -/
theorem DenseRischTowerScheme.asIntegrationTowerScheme_stage (T : DenseRischTowerScheme) (n : ℕ) :
    (T.asIntegrationTowerScheme.stage n).run = (T.stage n).asIntegrationStage.run := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [IntegrationTowerScheme.stage, asIntegrationTowerScheme]
    rfl

/-- The generic tower theorem yields soundness for every selected concrete dense stage. -/
theorem DenseRischTowerScheme.stage_sound (T : DenseRischTowerScheme) (n fuel : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n)) (result : IntegralResult (DenseFracTower n))
    (hdomain : ((T.asIntegrationTowerScheme).stage n).domain input)
    (hrun : ((T.asIntegrationTowerScheme).stage n).run fuel input = some result) :
    IsGenuineRischStageResult input result :=
  (T.asIntegrationTowerScheme).stage_sound n fuel input result hdomain hrun

/-- The generic tower theorem yields relative completeness for every selected concrete dense stage. -/
theorem DenseRischTowerScheme.stage_relative_complete (T : DenseRischTowerScheme) (n : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : ((T.asIntegrationTowerScheme).stage n).domain input)
    (hintegrable : IsRischLevelIntegrable input.Dt input.num input.den) :
    ∃ fuel result, ((T.asIntegrationTowerScheme).stage n).run fuel input = some result :=
  (T.asIntegrationTowerScheme).stage_complete n input hdomain hintegrable

/-- The selected sparse stage at every finite depth is the adapter of the dense selected stage. -/
noncomputable def DenseRischTowerScheme.sparseStage (T : DenseRischTowerScheme) (n : ℕ) : SparseRischStage n :=
  (T.stage n).toSparse

end DeepWiki.SymbolicIntegration
