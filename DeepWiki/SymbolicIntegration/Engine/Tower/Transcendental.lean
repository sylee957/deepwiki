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

/-- Present a lower-field fraction as a Risch input at the preceding tower depth. -/
noncomputable def denseFracTowerCoefficientInput (n : ℕ)
    (derivative : DensePoly (DenseFracTower n)) (c : DenseFracTower (n + 1)) :
    RischStageInput DensePoly (DenseFracTower n) where
  Dt := derivative
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

/-- A dense ordinary Risch stage with realization-indexed soundness. -/
noncomputable def DenseRischStage.asRealizedTowerIntegrationStage (S : DenseRischStage n)
    (R : TowerRealization N) (hn : n ≤ N) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TowerIntegralResult n)
      (fun input => IsRischLevelIntegrable input.Dt input.num input.den)
      (fun input result =>
        IsRealizedTowerIntegralResult R hn input.Dt input.num input.den result ∧ result.LogsGenuine) := by
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
    exact ⟨isRealizedTowerIntegralResult_ofIntegralResult R hn input.Dt input.num input.den ordinary
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

/-- A dense primitive LRT stage with realization-indexed soundness. -/
noncomputable def DenseLrtStage.asRealizedTowerIntegrationStage (S : DenseLrtStage n)
    (R : TowerRealization N) (hn : n ≤ N) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TowerIntegralResult n)
      (fun input => IsElementaryIntegrableGenuineLrt input.Dt input.num input.den)
      (fun input result =>
        IsRealizedTowerIntegralResult R hn input.Dt input.num input.den result ∧ result.LogsGenuine) := by
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
    exact ⟨isRealizedTowerIntegralResult_ofLrtResult R hn input.Dt input.num input.den lrt hnative.1,
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

/-- The realization-indexed semantic invariant selected by a common recursive-output stage. -/
def LayeredTranscendentalStage.RealizedCorrect (R : TowerRealization N) (hn : n ≤ N)
    (input : RischStageInput DensePoly (DenseFracTower n)) (result : TowerIntegralResult n) : Prop :=
  IsRealizedTowerIntegralResult R hn input.Dt input.num input.den result ∧ result.LogsGenuine

/-- Export every layered stage through the common integration-stage interface. -/
noncomputable def LayeredTranscendentalStage.asIntegrationStage (S : LayeredTranscendentalStage n) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TowerIntegralResult n) S.Integrable S.Correct := by
  cases S with
  | primitive stage => exact stage.asTowerIntegrationStage
  | hyperexponential stage => exact stage.asTowerIntegrationStage
  | tangent stage => exact stage.asTowerIntegrationStage

/-- Export every selected stage through the realization-indexed common interface. -/
noncomputable def LayeredTranscendentalStage.asRealizedIntegrationStage
    (S : LayeredTranscendentalStage n) (R : TowerRealization N) (hn : n ≤ N) :
    IntegrationStage (RischStageInput DensePoly (DenseFracTower n))
      (TowerIntegralResult n) S.Integrable (S.RealizedCorrect R hn) := by
  cases S with
  | primitive stage => exact stage.asRealizedTowerIntegrationStage R hn
  | hyperexponential stage => exact stage.asRealizedTowerIntegrationStage R hn
  | tangent stage => exact stage.asRealizedTowerIntegrationStage R hn

/-- The legacy and realization-indexed selected-stage adapters have the same executable run. -/
theorem LayeredTranscendentalStage.asIntegrationStage_run_eq_realized
    (S : LayeredTranscendentalStage n) (R : TowerRealization N) (hn : n ≤ N)
    (fuel : ℕ) (input : RischStageInput DensePoly (DenseFracTower n)) :
    S.asIntegrationStage.run fuel input = S.asRealizedIntegrationStage R hn |>.run fuel input := by
  cases S <;> rfl

/-- The legacy and realization-indexed selected-stage adapters have the same input domain. -/
theorem LayeredTranscendentalStage.asIntegrationStage_domain_eq_realized
    (S : LayeredTranscendentalStage n) (R : TowerRealization N) (hn : n ≤ N)
    (input : RischStageInput DensePoly (DenseFracTower n)) :
    S.asIntegrationStage.domain input = S.asRealizedIntegrationStage R hn |>.domain input := by
  cases S <;> rfl

/-- Package a selected lower stage as an executable coefficient stage certified in one realization. -/
noncomputable def LayeredTranscendentalStage.asRealizedTowerCoefficientStage
    (S : LayeredTranscendentalStage n) (R : TowerRealization N) (hn : n + 1 ≤ N) :
    RealizedTowerCoefficientStage R hn := by
  let derivative := R.monomialDerivative n hn
  let input : DenseFracTower (n + 1) → RischStageInput DensePoly (DenseFracTower n) :=
    denseFracTowerCoefficientInput n derivative
  let base := S.asIntegrationStage
  let realized := S.asRealizedIntegrationStage R (Nat.le_trans (Nat.le_succ n) hn)
  let executable : TowerCoefficientStage n :=
    { derivative := derivative
      Integrable := fun c => S.Integrable (input c)
      stage :=
        { run := fun fuel c => base.run fuel (input c)
          domain := fun c => base.domain (input c)
          sound := by
            intro fuel c result hdomain hrun
            exact base.sound fuel (input c) result hdomain hrun
          complete := by
            intro c hdomain hintegrable
            exact base.complete (input c) hdomain hintegrable } }
  refine { executable := executable, realized := ?_ }
  constructor
  · rfl
  · intro fuel c result hdomain hrun
    have hdomain' : realized.domain (input c) := by
      rw [← S.asIntegrationStage_domain_eq_realized R (Nat.le_trans (Nat.le_succ n) hn)]
      exact hdomain
    have hrun' : realized.run fuel (input c) = some result := by
      rw [← S.asIntegrationStage_run_eq_realized R (Nat.le_trans (Nat.le_succ n) hn)]
      exact hrun
    exact realized.sound fuel (input c) result hdomain' hrun'

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

/-- Run a lower certified level as a coefficient integrator at its actual monomial derivative. -/
noncomputable def LayeredTranscendentalLevel.runCoefficient
    (L : LayeredTranscendentalLevel n) (derivative : DensePoly (DenseFracTower n))
    (fuel : ℕ) (c : DenseFracTower (n + 1)) :
    Option (TowerIntegralResult n) :=
  L.stage.run fuel (denseFracTowerCoefficientInput n derivative c)

/-- The lower stage's domain viewed at a coefficient-field fraction. -/
def LayeredTranscendentalLevel.coefficientDomain
    (L : LayeredTranscendentalLevel n) (derivative : DensePoly (DenseFracTower n))
    (c : DenseFracTower (n + 1)) : Prop :=
  L.stage.domain (denseFracTowerCoefficientInput n derivative c)

/-- Every accepted lower coefficient run has the common recursive-result certificate. -/
theorem LayeredTranscendentalLevel.runCoefficient_sound
    (L : LayeredTranscendentalLevel n) (derivative : DensePoly (DenseFracTower n))
    (fuel : ℕ) (c : DenseFracTower (n + 1)) (result : TowerIntegralResult n)
    (hdomain : L.coefficientDomain derivative c)
    (hrun : L.runCoefficient derivative fuel c = some result) :
    LayeredTranscendentalStage.Correct (denseFracTowerCoefficientInput n derivative c) result :=
  L.stage.sound fuel (denseFracTowerCoefficientInput n derivative c) result hdomain hrun

/-- A lower coefficient input satisfying its selected integrability predicate eventually succeeds. -/
theorem LayeredTranscendentalLevel.runCoefficient_complete
    (L : LayeredTranscendentalLevel n) (derivative : DensePoly (DenseFracTower n))
    (c : DenseFracTower (n + 1)) (hdomain : L.coefficientDomain derivative c)
    (hintegrable : L.Integrable (denseFracTowerCoefficientInput n derivative c)) :
    ∃ fuel result, L.runCoefficient derivative fuel c = some result :=
  L.stage.complete (denseFracTowerCoefficientInput n derivative c) hdomain hintegrable

/-- Export a selected lower level through the recursive tower-coefficient interface. -/
noncomputable def LayeredTranscendentalLevel.asTowerCoefficientStage
    (L : LayeredTranscendentalLevel n) (derivative : DensePoly (DenseFracTower n)) :
    TowerCoefficientStage n := by
  let integrable : DenseFracTower (n + 1) → Prop := fun c =>
    L.Integrable (denseFracTowerCoefficientInput n derivative c)
  refine { derivative := derivative, Integrable := integrable, stage := ?_ }
  refine
    { run := L.runCoefficient derivative
      domain := L.coefficientDomain derivative
      sound := ?_
      complete := ?_ }
  · intro fuel c result hdomain hrun
    exact L.runCoefficient_sound derivative fuel c result hdomain hrun
  · intro c hdomain hintegrable
    exact L.runCoefficient_complete derivative c hdomain hintegrable

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
