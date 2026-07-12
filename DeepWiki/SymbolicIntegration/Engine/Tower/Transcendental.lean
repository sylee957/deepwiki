import DeepWiki.SymbolicIntegration.Engine.Hyperexp.TowerStage
import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentDepth
import DeepWiki.SymbolicIntegration.Engine.Tower.LrtDepth

/-! # Mixed finite transcendental integration towers

Primitive, hyperexponential, and tangent extensions select different certified stage packages but share the
same represented input. This module preserves their native result types and applies the common finite-tower
induction to an arbitrary mixed selector.
-/

namespace DeepWiki.SymbolicIntegration

variable {n : ℕ}

/-- A certified stage selected for one primitive, hyperexponential, or tangent tower extension. -/
inductive TranscendentalStage (n : ℕ) where
  /-- Primitive integration with algebraic-residue logarithms. -/
  | primitive (stage : DenseLrtStage n) : TranscendentalStage n
  /-- Hyperexponential integration with ordinary logarithms. -/
  | hyperexponential (stage : DenseRischStage n) : TranscendentalStage n
  /-- Tangent integration with ordinary logarithms. -/
  | tangent (stage : DenseRischStage n) : TranscendentalStage n

/-- The native result representation selected by a transcendental stage. -/
def TranscendentalStage.Output : TranscendentalStage n → Type
  | .primitive _ => LrtResult (DenseFracTower n)
  | .hyperexponential _ => IntegralResult (DenseFracTower n)
  | .tangent _ => IntegralResult (DenseFracTower n)

/-- The semantic integrability predicate selected by a transcendental stage. -/
def TranscendentalStage.Integrable (S : TranscendentalStage n) :
    RischStageInput DensePoly (DenseFracTower n) → Prop :=
  match S with
  | .primitive _ => fun input =>
      IsElementaryIntegrableGenuineLrt input.Dt input.num input.den
  | .hyperexponential _ | .tangent _ => fun input =>
      IsRischLevelIntegrable input.Dt input.num input.den

/-- The native genuine-result contract selected by a transcendental stage. -/
def TranscendentalStage.Correct (S : TranscendentalStage n)
    (input : RischStageInput DensePoly (DenseFracTower n)) : S.Output → Prop :=
  match S with
  | .primitive _ => fun result =>
      IsGenuineIntegralResultLrt input.Dt input.num input.den result
  | .hyperexponential _ | .tangent _ => fun result =>
      IsGenuineRischStageResult input result

/-- Export every selected transcendental case through the common integration-stage interface. -/
noncomputable def TranscendentalStage.asIntegrationStage (S : TranscendentalStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n)) S.Output S.Integrable S.Correct := by
  cases S with
  | primitive stage => exact stage.asIntegrationStage
  | hyperexponential stage => exact stage.asIntegrationStage
  | tangent stage => exact stage.asIntegrationStage

/-- A finite tower chooses a primitive, hyperexponential, or tangent stage at its base and successors. -/
structure TranscendentalTowerScheme where
  /-- Certified selected stage at the base depth. -/
  base : TranscendentalStage 0
  /-- Select the next extension stage from the immediately lower selected stage. -/
  step : ∀ n, TranscendentalStage n → TranscendentalStage (n + 1)

/-- The certified transcendental stage selected at a finite tower depth. -/
def TranscendentalTowerScheme.stage (T : TranscendentalTowerScheme) : (n : ℕ) → TranscendentalStage n
  | 0 => T.base
  | n + 1 => T.step n (T.stage n)

/-- Export a mixed transcendental selector through the generic finite integration-tower recursion. -/
noncomputable def TranscendentalTowerScheme.asIntegrationTowerScheme (T : TranscendentalTowerScheme) :
    IntegrationTowerScheme (fun n => RischStageInput DensePoly (DenseFracTower n)) where
  Output n := (T.stage n).Output
  Integrable n := (T.stage n).Integrable
  Correct n := (T.stage n).Correct
  base := T.base.asIntegrationStage
  step n _ := (T.step n (T.stage n)).asIntegrationStage

/-- Every accepted mixed-tower result satisfies the genuine contract of its selected extension case. -/
theorem TranscendentalTowerScheme.stage_sound (T : TranscendentalTowerScheme) (n fuel : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : (T.stage n).Output)
    (hdomain : (T.asIntegrationTowerScheme.stage n).domain input)
    (hrun : (T.asIntegrationTowerScheme.stage n).run fuel input = some result) :
    (T.stage n).Correct input result :=
  T.asIntegrationTowerScheme.stage_sound n fuel input result hdomain hrun

/-- Every integrable mixed-tower input in the selected semantic domain eventually succeeds. -/
theorem TranscendentalTowerScheme.stage_complete (T : TranscendentalTowerScheme) (n : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : (T.asIntegrationTowerScheme.stage n).domain input)
    (hintegrable : (T.stage n).Integrable input) :
    ∃ fuel result, (T.asIntegrationTowerScheme.stage n).run fuel input = some result :=
  T.asIntegrationTowerScheme.stage_complete n input hdomain hintegrable

/-- Select a primitive algebraic-residue LRT stage in a mixed transcendental tower. -/
def primitiveTranscendentalStage (S : DenseLrtStage n) : TranscendentalStage n := .primitive S

/-- Select a semantic hyperexponential dense stage in a mixed transcendental tower. -/
noncomputable def hyperexpTranscendentalStage (n : ℕ)
    (R : CPolynomialReduction DensePoly (DenseFracTower n))
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly (DenseFracTower n))
    [LawfulCPolynomialReduction R] [CompleteCPolynomialReduction R polynomialDomain]
    [CCanonicalRepresentation DensePoly (DenseFracTower n)]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n)]
    [CRischField (DenseFracTower n)] [CRischFieldSpec (DenseFracTower n)]
    [CPolyGcd DensePoly (DenseFracTower n)] [CPolySquarefree DensePoly (DenseFracTower n)]
    [CPolyResultant DensePoly] [CResidueSource DensePoly (DenseFracTower n)]
    (hfield : CRischFieldComplete (DenseFracTower n)) : TranscendentalStage n :=
  .hyperexponential (hyperexpDenseRischStage n R kind polynomialDomain hfield)

/-- Select a compositional tangent dense stage in a mixed transcendental tower. -/
noncomputable def tangentTranscendentalStage (C : DenseTangentLevelCapabilities n)
    (solverDomain : TangentCoefficientDomain (α := DenseFracTower n))
    [LawfulCTangentCoefficientSolver C.coupled]
    [CompleteCTangentCoefficientSolver C.coupled solverDomain]
    (coefficientDomain : RecursiveElementaryDomain (α := DenseFracTower n))
    [LawfulCRecursiveElementaryIntegrator C.coefficient]
    [CompleteCRecursiveElementaryIntegrator C.coefficient coefficientDomain] : TranscendentalStage n :=
  .tangent (denseTangentCompositionalStage C solverDomain coefficientDomain)

end DeepWiki.SymbolicIntegration
