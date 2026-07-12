import DeepWiki.SymbolicIntegration.Engine.Hyperexp.TowerStage
import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentDepth
import DeepWiki.SymbolicIntegration.Engine.Tower.LrtDepth
import DeepWiki.SymbolicIntegration.Engine.Tower.LogTower

/-! # Mixed finite transcendental integration towers

Primitive, hyperexponential, and tangent extensions select different certified stage packages but share one
layered result invariant. This module applies the common finite-tower induction to an arbitrary mixed selector.
-/

namespace DeepWiki.SymbolicIntegration

variable {n : ℕ}

/-- Present a lower-field fraction as a unit-monomial Risch input at the preceding tower depth. -/
noncomputable def denseFracTowerCoefficientInput (n : ℕ) (c : DenseFracTower (n + 1)) :
    RischStageInput DensePoly (DenseFracTower n) where
  Dt := CPoly.one
  num := CFrac.num c
  den := CFrac.den c
  den_nonzero := CFrac.toPoly_den_ne_zero_generic c

/-- A dense ordinary Risch stage rendered into the recursive tower-result language. -/
noncomputable def DenseRischStage.asTowerIntegrationStage (S : DenseRischStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TowerIntegralResult n)
      (fun input => IsRischLevelIntegrable input.Dt input.num input.den)
      (fun input result =>
        IsTowerIntegralResult input.Dt input.num input.den result ∧ result.LogsGenuine) := by
  let native := S.asIntegrationStage
  refine
    { run := fun fuel input =>
        (native.run fuel input).map (TowerIntegralResult.ofIntegralResult input.Dt)
      domain := native.domain
      sound := ?_
      complete := ?_ }
  · intro fuel input output hdomain hrun
    obtain ⟨ordinary, hordinary, rfl⟩ := Option.map_eq_some_iff.mp hrun
    have hnative := native.sound fuel input ordinary hdomain hordinary
    exact ⟨isTowerIntegralResult_ofIntegralResult input.Dt input.num input.den ordinary
      hnative.1,
      TowerIntegralResult.logsGenuine_ofIntegralResult input.Dt ordinary hnative.2.1 hnative.2.2⟩
  · intro input hdomain hintegrable
    obtain ⟨fuel, ordinary, hrun⟩ := native.complete input hdomain hintegrable
    exact ⟨fuel, TowerIntegralResult.ofIntegralResult input.Dt ordinary, by simp [hrun]⟩

/-- A dense primitive LRT stage rendered into the recursive tower-result language. -/
noncomputable def DenseLrtStage.asTowerIntegrationStage (S : DenseLrtStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TowerIntegralResult n)
      (fun input => IsElementaryIntegrableGenuineLrt input.Dt input.num input.den)
      (fun input result =>
        IsTowerIntegralResult input.Dt input.num input.den result ∧ result.LogsGenuine) := by
  let native := S.asIntegrationStage
  refine
    { run := fun fuel input =>
        (native.run fuel input).map (TowerIntegralResult.ofLrtResult input.Dt)
      domain := native.domain
      sound := ?_
      complete := ?_ }
  · intro fuel input output hdomain hrun
    obtain ⟨lrt, hlrt, rfl⟩ := Option.map_eq_some_iff.mp hrun
    have hnative := native.sound fuel input lrt hdomain hlrt
    exact ⟨isTowerIntegralResult_ofLrtResult input.Dt input.num input.den lrt hnative.1,
      TowerIntegralResult.logsGenuine_ofLrtResult input.Dt lrt hnative.2⟩
  · intro input hdomain hintegrable
    obtain ⟨fuel, lrt, hrun⟩ := native.complete input hdomain hintegrable
    exact ⟨fuel, TowerIntegralResult.ofLrtResult input.Dt lrt, by simp [hrun]⟩

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

/-- The semantic invariant selected by a common recursive-output stage. -/
def LayeredTranscendentalStage.Correct (input : RischStageInput DensePoly (DenseFracTower n))
    (result : TowerIntegralResult n) : Prop :=
  IsTowerIntegralResult input.Dt input.num input.den result ∧ result.LogsGenuine

/-- Export every layered stage through the common integration-stage interface. -/
noncomputable def LayeredTranscendentalStage.asIntegrationStage (S : LayeredTranscendentalStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TowerIntegralResult n) S.Integrable S.Correct := by
  cases S with
  | primitive stage => exact stage.asTowerIntegrationStage
  | hyperexponential stage => exact stage.asTowerIntegrationStage
  | tangent stage => exact stage.asTowerIntegrationStage

/-- A certified common-output integration level at one fraction-tower depth. -/
structure LayeredTranscendentalLevel (n : ℕ) where
  /-- The semantic integrability predicate supported by this level. -/
  Integrable : RischStageInput DensePoly (DenseFracTower n) → Prop
  /-- Executable stage with the common semantic and genuine-log postcondition. -/
  stage : IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
    (TowerIntegralResult n) Integrable LayeredTranscendentalStage.Correct

/-- Promote a selected primitive, hyperexponential, or tangent stage to a certified common-output level. -/
noncomputable def LayeredTranscendentalLevel.ofSelected (S : LayeredTranscendentalStage n) :
    LayeredTranscendentalLevel n where
  Integrable := S.Integrable
  stage := S.asIntegrationStage

/-- Run a lower certified level as a coefficient integrator with monomial derivative `1`. -/
noncomputable def LayeredTranscendentalLevel.runCoefficient
    (L : LayeredTranscendentalLevel n) (fuel : ℕ) (c : DenseFracTower (n + 1)) :
    Option (TowerIntegralResult n) :=
  L.stage.run fuel (denseFracTowerCoefficientInput n c)

/-- The lower stage's domain viewed at a coefficient-field fraction. -/
def LayeredTranscendentalLevel.coefficientDomain
    (L : LayeredTranscendentalLevel n) (c : DenseFracTower (n + 1)) : Prop :=
  L.stage.domain (denseFracTowerCoefficientInput n c)

/-- Every accepted lower coefficient run has the common recursive-result certificate. -/
theorem LayeredTranscendentalLevel.runCoefficient_sound
    (L : LayeredTranscendentalLevel n) (fuel : ℕ) (c : DenseFracTower (n + 1))
    (result : TowerIntegralResult n) (hdomain : L.coefficientDomain c)
    (hrun : L.runCoefficient fuel c = some result) :
    LayeredTranscendentalStage.Correct (denseFracTowerCoefficientInput n c) result :=
  L.stage.sound fuel (denseFracTowerCoefficientInput n c) result hdomain hrun

/-- A lower coefficient input satisfying its selected integrability predicate eventually succeeds. -/
theorem LayeredTranscendentalLevel.runCoefficient_complete
    (L : LayeredTranscendentalLevel n) (c : DenseFracTower (n + 1))
    (hdomain : L.coefficientDomain c)
    (hintegrable : L.Integrable (denseFracTowerCoefficientInput n c)) :
    ∃ fuel result, L.runCoefficient fuel c = some result :=
  L.stage.complete (denseFracTowerCoefficientInput n c) hdomain hintegrable

/-- A finite tower whose successor constructor receives the complete certified lower level. -/
structure LayeredTranscendentalTowerScheme where
  /-- Certified base level. -/
  base : LayeredTranscendentalLevel 0
  /-- Build a successor from its entire lower-level executable and semantic contract. -/
  step : ∀ n, LayeredTranscendentalLevel n → LayeredTranscendentalLevel (n + 1)

/-- The complete certified level selected at a finite tower depth. -/
def LayeredTranscendentalTowerScheme.level (T : LayeredTranscendentalTowerScheme) :
    (n : ℕ) → LayeredTranscendentalLevel n
  | 0 => T.base
  | n + 1 => T.step n (T.level n)

/-- Every accepted layered tower result satisfies the common semantic and genuine-log invariant. -/
theorem LayeredTranscendentalTowerScheme.stage_sound (T : LayeredTranscendentalTowerScheme)
    (n fuel : ℕ) (input : RischStageInput DensePoly (DenseFracTower n))
    (result : TowerIntegralResult n)
    (hdomain : (T.level n).stage.domain input)
    (hrun : (T.level n).stage.run fuel input = some result) :
    LayeredTranscendentalStage.Correct input result :=
  (T.level n).stage.sound fuel input result hdomain hrun

/-- Every integrable in-domain layered tower input eventually returns a common semantic result. -/
theorem LayeredTranscendentalTowerScheme.stage_complete (T : LayeredTranscendentalTowerScheme)
    (n : ℕ) (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : (T.level n).stage.domain input)
    (hintegrable : (T.level n).Integrable input) :
    ∃ fuel result, (T.level n).stage.run fuel input = some result :=
  (T.level n).stage.complete input hdomain hintegrable

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
