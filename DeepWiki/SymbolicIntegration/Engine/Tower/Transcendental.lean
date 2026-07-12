import DeepWiki.SymbolicIntegration.Engine.Hyperexp.TowerStage
import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentDepth
import DeepWiki.SymbolicIntegration.Engine.Tower.LrtDepth
import DeepWiki.SymbolicIntegration.Engine.Tower.TranscendentalResult

/-! # Mixed finite transcendental integration towers

Primitive, hyperexponential, and tangent extensions select different certified stage packages but share one
layered result invariant. This module applies the common finite-tower induction to an arbitrary mixed selector.
-/

namespace DeepWiki.SymbolicIntegration

variable {n : ℕ}

/-- A dense ordinary Risch stage rendered into the common layered transcendental result language. -/
noncomputable def DenseRischStage.asLayeredIntegrationStage (S : DenseRischStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TranscendentalIntegralResult (DenseFracTower n))
      (fun input => IsRischLevelIntegrable input.Dt input.num input.den)
      (fun input result =>
        IsTranscendentalIntegralResult input.Dt input.num input.den result ∧ result.LogsGenuine) := by
  let native := S.asIntegrationStage
  refine
    { run := fun fuel input => (native.run fuel input).map TranscendentalIntegralResult.ofIntegralResult
      domain := native.domain
      sound := ?_
      complete := ?_ }
  · intro fuel input output hdomain hrun
    obtain ⟨ordinary, hordinary, rfl⟩ := Option.map_eq_some_iff.mp hrun
    have hnative := native.sound fuel input ordinary hdomain hordinary
    exact ⟨isTranscendentalIntegralResult_ofIntegralResult input.Dt input.num input.den ordinary
      hnative.1,
      TranscendentalIntegralResult.logsGenuine_ofIntegralResult ordinary hnative.2.1 hnative.2.2⟩
  · intro input hdomain hintegrable
    obtain ⟨fuel, ordinary, hrun⟩ := native.complete input hdomain hintegrable
    exact ⟨fuel, TranscendentalIntegralResult.ofIntegralResult ordinary, by simp [hrun]⟩

/-- A dense primitive LRT stage rendered into the common layered transcendental result language. -/
noncomputable def DenseLrtStage.asLayeredIntegrationStage (S : DenseLrtStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TranscendentalIntegralResult (DenseFracTower n))
      (fun input => IsElementaryIntegrableGenuineLrt input.Dt input.num input.den)
      (fun input result =>
        IsTranscendentalIntegralResult input.Dt input.num input.den result ∧ result.LogsGenuine) := by
  let native := S.asIntegrationStage
  refine
    { run := fun fuel input => (native.run fuel input).map TranscendentalIntegralResult.ofLrtResult
      domain := native.domain
      sound := ?_
      complete := ?_ }
  · intro fuel input output hdomain hrun
    obtain ⟨lrt, hlrt, rfl⟩ := Option.map_eq_some_iff.mp hrun
    have hnative := native.sound fuel input lrt hdomain hlrt
    exact ⟨isTranscendentalIntegralResult_ofLrtResult input.Dt input.num input.den lrt hnative.1,
      TranscendentalIntegralResult.logsGenuine_ofLrtResult lrt hnative.2⟩
  · intro input hdomain hintegrable
    obtain ⟨fuel, lrt, hrun⟩ := native.complete input hdomain hintegrable
    exact ⟨fuel, TranscendentalIntegralResult.ofLrtResult lrt, by simp [hrun]⟩

/-- A primitive, hyperexponential, or tangent stage with one common layered-output representation. -/
inductive LayeredTranscendentalStage (n : ℕ) where
  /-- Primitive stage with root-free current-extension logarithms. -/
  | primitive (stage : DenseLrtStage n) : LayeredTranscendentalStage n
  /-- Hyperexponential stage with ordinary current-extension logarithms. -/
  | hyperexponential (stage : DenseRischStage n) : LayeredTranscendentalStage n
  /-- Tangent stage with ordinary current-extension logarithms. -/
  | tangent (stage : DenseRischStage n) : LayeredTranscendentalStage n

/-- The integrability predicate selected by a common layered-output stage. -/
def LayeredTranscendentalStage.Integrable (S : LayeredTranscendentalStage n) :
    RischStageInput DensePoly (DenseFracTower n) → Prop :=
  match S with
  | .primitive _ => fun input => IsElementaryIntegrableGenuineLrt input.Dt input.num input.den
  | .hyperexponential _ | .tangent _ => fun input => IsRischLevelIntegrable input.Dt input.num input.den

/-- The semantic invariant selected by a common layered-output stage. -/
def LayeredTranscendentalStage.Correct (input : RischStageInput DensePoly (DenseFracTower n))
    (result : TranscendentalIntegralResult (DenseFracTower n)) : Prop :=
  IsTranscendentalIntegralResult input.Dt input.num input.den result ∧ result.LogsGenuine

/-- Export every layered stage through the common integration-stage interface. -/
noncomputable def LayeredTranscendentalStage.asIntegrationStage (S : LayeredTranscendentalStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TranscendentalIntegralResult (DenseFracTower n)) S.Integrable S.Correct := by
  cases S with
  | primitive stage => exact stage.asLayeredIntegrationStage
  | hyperexponential stage => exact stage.asLayeredIntegrationStage
  | tangent stage => exact stage.asLayeredIntegrationStage

/-- A finite tower choosing common layered-output stages at its base and successors. -/
structure LayeredTranscendentalTowerScheme where
  /-- Selected base stage. -/
  base : LayeredTranscendentalStage 0
  /-- Select the next extension stage from the previous selected stage. -/
  step : ∀ n, LayeredTranscendentalStage n → LayeredTranscendentalStage (n + 1)

/-- The common layered-output stage selected at a finite tower depth. -/
def LayeredTranscendentalTowerScheme.stage (T : LayeredTranscendentalTowerScheme) :
    (n : ℕ) → LayeredTranscendentalStage n
  | 0 => T.base
  | n + 1 => T.step n (T.stage n)

/-- Export a layered selector through generic finite integration-tower recursion. -/
noncomputable def LayeredTranscendentalTowerScheme.asIntegrationTowerScheme
    (T : LayeredTranscendentalTowerScheme) :
    IntegrationTowerScheme (fun n => RischStageInput DensePoly (DenseFracTower n)) where
  Output n := TranscendentalIntegralResult (DenseFracTower n)
  Integrable n := (T.stage n).Integrable
  Correct n := LayeredTranscendentalStage.Correct
  base := T.base.asIntegrationStage
  step n _ := (T.step n (T.stage n)).asIntegrationStage

/-- Every accepted layered tower result satisfies the common semantic and genuine-log invariant. -/
theorem LayeredTranscendentalTowerScheme.stage_sound (T : LayeredTranscendentalTowerScheme)
    (n fuel : ℕ) (input : RischStageInput DensePoly (DenseFracTower n))
    (result : TranscendentalIntegralResult (DenseFracTower n))
    (hdomain : (T.asIntegrationTowerScheme.stage n).domain input)
    (hrun : (T.asIntegrationTowerScheme.stage n).run fuel input = some result) :
    LayeredTranscendentalStage.Correct input result :=
  T.asIntegrationTowerScheme.stage_sound n fuel input result hdomain hrun

/-- Every integrable in-domain layered tower input eventually returns a common semantic result. -/
theorem LayeredTranscendentalTowerScheme.stage_complete (T : LayeredTranscendentalTowerScheme)
    (n : ℕ) (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : (T.asIntegrationTowerScheme.stage n).domain input)
    (hintegrable : (T.stage n).Integrable input) :
    ∃ fuel result, (T.asIntegrationTowerScheme.stage n).run fuel input = some result :=
  T.asIntegrationTowerScheme.stage_complete n input hdomain hintegrable

/-- Select a primitive root-free stage in the common layered-output language. -/
def primitiveLayeredTranscendentalStage (S : DenseLrtStage n) : LayeredTranscendentalStage n :=
  .primitive S

/-- Select a semantic hyperexponential dense stage in the common layered-output language. -/
noncomputable def hyperexpLayeredTranscendentalStage (n : ℕ)
    (R : CPolynomialReduction DensePoly (DenseFracTower n))
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly (DenseFracTower n))
    [LawfulCPolynomialReduction R] [CompleteCPolynomialReduction R polynomialDomain]
    [CCanonicalRepresentation DensePoly (DenseFracTower n)]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFracTower n)]
    [CRischField (DenseFracTower n)] [CRischFieldSpec (DenseFracTower n)]
    [CPolyGcd DensePoly (DenseFracTower n)] [CPolySquarefree DensePoly (DenseFracTower n)]
    [CPolyResultant DensePoly] [CResidueSource DensePoly (DenseFracTower n)]
    (hfield : CRischFieldComplete (DenseFracTower n)) : LayeredTranscendentalStage n :=
  .hyperexponential (hyperexpDenseRischStage n R kind polynomialDomain hfield)

/-- Select a compositional tangent dense stage in the common layered-output language. -/
noncomputable def tangentLayeredTranscendentalStage (C : DenseTangentLevelCapabilities n)
    (solverDomain : TangentCoefficientDomain (α := DenseFracTower n))
    [LawfulCTangentCoefficientSolver C.coupled]
    [CompleteCTangentCoefficientSolver C.coupled solverDomain]
    (coefficientDomain : RecursiveElementaryDomain (α := DenseFracTower n))
    [LawfulCRecursiveElementaryIntegrator C.coefficient]
    [CompleteCRecursiveElementaryIntegrator C.coefficient coefficientDomain] :
    LayeredTranscendentalStage n :=
  .tangent (denseTangentCompositionalStage C solverDomain coefficientDomain)

end DeepWiki.SymbolicIntegration
