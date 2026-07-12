import DeepWiki.SymbolicIntegration.Engine.LrtGuarded
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementary
import DeepWiki.SymbolicIntegration.Engine.Tower.Stage

/-! # Algebraic coefficient-log language

Records ordinary lower-field logarithms and root-free algebraic-residue LRT families without coercing either
one into the other. This is the syntax and genuine-log layer for heterogeneous transcendental recursion. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- A lower-coefficient logarithmic contribution: either an ordinary logarithm or a root-free LRT family. -/
inductive AlgebraicCoefficientLog (β : Type u) [CField β] where
  /-- An ordinary constant-coefficient logarithm in `DenseFrac β`. -/
  | ordinary (coefficient argument : DenseFrac β) : AlgebraicCoefficientLog β
  /-- A root-free LRT family `Σ_{R(c)=0} c log S(c,t)` over the lower variable. -/
  | lrt (residue : DensePoly β) (argument : List (DensePoly β)) : AlgebraicCoefficientLog β

/-- An elementary coefficient antiderivative with a rational part and heterogeneous logarithmic evidence. -/
structure AlgebraicCoefficientIntegralResult (β : Type u) [CField β] where
  /-- Rational lower-field antiderivative part. -/
  rational : DenseFrac β
  /-- Ordinary and algebraic-residue logarithmic contributions. -/
  logs : List (AlgebraicCoefficientLog β)

variable {β : Type u} [CField β] [CFieldSpec.{u,u} β] [CDiffField β]

/-- Embed an ordinary recursive coefficient result into the heterogeneous log language. -/
def AlgebraicCoefficientIntegralResult.ofOrdinary (res : CoefficientIntegralResult (DenseFrac β)) :
    AlgebraicCoefficientIntegralResult β where
  rational := res.rational
  logs := res.logs.map fun cv => .ordinary cv.1 cv.2

/-- Embed a root-free lower LRT result into the heterogeneous coefficient log language. -/
def AlgebraicCoefficientIntegralResult.ofLrt (res : LrtResult β) :
    AlgebraicCoefficientIntegralResult β where
  rational := CField.div (CFrac.ofPoly res.rational.1) (CFrac.ofPoly res.rational.2)
  logs := res.logs.map fun RS => .lrt RS.1 RS.2

/-- The genuine-log condition for one heterogeneous coefficient log contribution. -/
def AlgebraicCoefficientLog.IsGenuine : AlgebraicCoefficientLog β → Prop
  | .ordinary coefficient argument =>
      CFieldSpec.toK (CDiffField.cderiv coefficient) = 0 ∧ CFieldSpec.toK argument ≠ 0
  | .lrt residue _ =>
      CPolyEngine.cisZero (CPolyEngine.mapDeriv (CPolyEngine.cmonic residue)) = true

/-- Every heterogeneous logarithmic contribution in a result is genuine. -/
def AlgebraicCoefficientIntegralResult.LogsGenuine (res : AlgebraicCoefficientIntegralResult β) : Prop :=
  ∀ log ∈ res.logs, log.IsGenuine

/-- The derivative contribution of one heterogeneous coefficient log in an algebraically closed extension. -/
noncomputable def AlgebraicCoefficientLog.denote {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly β) : AlgebraicCoefficientLog β → RatFunc E
  | .ordinary coefficient argument =>
      ratFuncBaseChange E
        (CFieldSpec.toK coefficient *
          (CFieldSpec.toK (CDiffField.cderiv argument) / CFieldSpec.toK argument))
  | .lrt residue argument => logResidueTermLrt (E := E) Dt (residue, argument)

/-- The derivative contribution of a heterogeneous coefficient-log list. -/
noncomputable def algebraicCoefficientLogSum {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly β) (logs : List (AlgebraicCoefficientLog β)) : RatFunc E :=
  (logs.map (AlgebraicCoefficientLog.denote (E := E) Dt)).sum

/-- A heterogeneous coefficient result differentiates to its input after base change to every algebraically
closed differential extension. -/
def IsAlgebraicCoefficientIntegralResult [CDiffFieldSpec β] (c : DenseFrac β)
    (res : AlgebraicCoefficientIntegralResult β) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    [DifferentialAlgebra (CFieldSpec.K β) E] [IsAlgClosed E],
    ratFuncBaseChange E (CFieldSpec.toK (CDiffField.cderiv res.rational)) +
        algebraicCoefficientLogSum (E := E) ([CCommRing.one] : DensePoly β) res.logs =
      ratFuncBaseChange E (CFieldSpec.toK c)

/-- A lower fraction possesses a heterogeneous algebraic coefficient antiderivative. -/
def IsAlgebraicCoefficientElementarilyIntegrable [CDiffFieldSpec β] (c : DenseFrac β) : Prop :=
  ∃ res : AlgebraicCoefficientIntegralResult β, IsAlgebraicCoefficientIntegralResult c res

/-- The common integration-stage specialization for heterogeneous coefficient antiderivatives. -/
abbrev AlgebraicCoefficientStage [CDiffFieldSpec β] :=
  IntegrationStage (DenseFrac β) (AlgebraicCoefficientIntegralResult β)
    IsCoefficientElementarilyIntegrable IsAlgebraicCoefficientIntegralResult

/-- The algebraic coefficient-log interpretation of an embedded LRT result is exactly its LRT residue sum. -/
theorem algebraicCoefficientLogSum_ofLrt {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly β) (res : LrtResult β) :
    algebraicCoefficientLogSum (E := E) Dt (AlgebraicCoefficientIntegralResult.ofLrt res).logs =
      logResidueSumLrt (E := E) Dt res.logs := by
  simp only [AlgebraicCoefficientIntegralResult.ofLrt, algebraicCoefficientLogSum, List.map_map]
  exact (logResidueSumLrtG_eq_sum Dt res.logs).symm

/-- The algebraic coefficient-log interpretation of an ordinary recursive result is its base-changed
coefficient logarithmic sum. -/
theorem algebraicCoefficientLogSum_ofOrdinary {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly β) (res : CoefficientIntegralResult (DenseFrac β)) :
    algebraicCoefficientLogSum (E := E) Dt (AlgebraicCoefficientIntegralResult.ofOrdinary res).logs =
      ratFuncBaseChange E (coefficientLogSum res.logs) := by
  rcases res with ⟨rational, logs⟩
  induction logs with
  | nil =>
    simp [AlgebraicCoefficientIntegralResult.ofOrdinary, algebraicCoefficientLogSum,
      coefficientLogSum]
  | cons log logs ih =>
    simp [AlgebraicCoefficientIntegralResult.ofOrdinary, algebraicCoefficientLogSum,
      coefficientLogSum] at ih ⊢
    simpa [AlgebraicCoefficientLog.denote] using
      congrArg (ratFuncBaseChange E
        (CFieldSpec.toK log.1 *
          (CFieldSpec.toK (CDiffField.cderiv log.2) / CFieldSpec.toK log.2)) + ·) ih

/-- An ordinary recursive coefficient certificate embeds into the heterogeneous coefficient-log semantics. -/
theorem isAlgebraicCoefficientIntegralResult_ofOrdinary [CDiffFieldSpec β]
    (c : DenseFrac β) (res : CoefficientIntegralResult (DenseFrac β))
    (hres : IsCoefficientIntegralResult c res) :
    IsAlgebraicCoefficientIntegralResult c (AlgebraicCoefficientIntegralResult.ofOrdinary res) := by
  intro E _ _ _ _ _ _
  have hbase := congrArg (ratFuncBaseChange E) hres.1
  rw [map_add, ← algebraicCoefficientLogSum_ofOrdinary] at hbase
  exact hbase

/-- An ordinary recursive coefficient integrator is a common stage after embedding its log language. -/
noncomputable def CRecursiveElementaryIntegrator.asAlgebraicCoefficientStage
    [CDiffFieldSpec β] (C : CRecursiveElementaryIntegrator (DenseFrac β))
    (domain : RecursiveElementaryDomain (α := DenseFrac β))
    [LawfulCRecursiveElementaryIntegrator C]
    [CompleteCRecursiveElementaryIntegrator C domain] : AlgebraicCoefficientStage (β := β) where
  run fuel c := (C.integrate fuel c).map AlgebraicCoefficientIntegralResult.ofOrdinary
  domain := domain
  sound fuel c output _hdomain hrun := by
    obtain ⟨ordinary, hordinary, rfl⟩ := Option.map_eq_some_iff.mp hrun
    exact isAlgebraicCoefficientIntegralResult_ofOrdinary c ordinary
      (LawfulCRecursiveElementaryIntegrator.sound fuel c ordinary hordinary)
  complete c hdomain hintegrable := by
    obtain ⟨fuel, ordinary, hrun⟩ := CompleteCRecursiveElementaryIntegrator.complete
      (C := C) (domain := domain) c hdomain hintegrable
    exact ⟨fuel, AlgebraicCoefficientIntegralResult.ofOrdinary ordinary, by simp [hrun]⟩

/-- A genuine root-free LRT identity embeds into the heterogeneous coefficient-log semantics. -/
theorem isAlgebraicCoefficientIntegralResult_ofLrt [CDiffFieldSpec β]
    [CFieldDomain β DensePoly] [Algebra ℚ (CFieldSpec.K β)]
    (c : DenseFrac β) (res : LrtResult β)
    (hres : IsIntegralResultLrt ([CCommRing.one] : DensePoly β)
      (CFrac.num c) (CFrac.den c) res) :
    IsAlgebraicCoefficientIntegralResult c (AlgebraicCoefficientIntegralResult.ofLrt res) := by
  intro E _ _ _ _ _ _
  rw [algebraicCoefficientLogSum_ofLrt]
  have hrational :
      ratFuncBaseChange E
          (CFieldSpec.toK
            (CDiffField.cderiv (AlgebraicCoefficientIntegralResult.ofLrt res).rational)) =
        towerDerivExt ([CCommRing.one] : DensePoly β)
          (amGExt (E := E) (CPoly.toPoly res.rational.1) /
            amGExt (E := E) (CPoly.toPoly res.rational.2)) := by
    rw [AlgebraicCoefficientIntegralResult.ofLrt, toK_cderiv_denseFrac]
    simp only [CFieldSpec.toK_div, CFrac.toK_ofPoly]
    simpa only [towerFractionFieldDerivP, towerFractionFieldDeriv, toPoly_list_eq] using
      (ratFuncBaseChange_towerFractionFieldDerivG (E := E)
        ([CCommRing.one] : DensePoly β) (CPoly.toPoly res.rational.1)
          (CPoly.toPoly res.rational.2))
  have hinput :
      ratFuncBaseChange E (CFieldSpec.toK c) =
        amGExt (E := E) (CPoly.toPoly (CFrac.num c)) /
          amGExt (E := E) (CPoly.toPoly (CFrac.den c)) := by
    rw [toK_denseFrac_eq_fieldFrac, ratFuncBaseChange_amG_div]
  rw [hrational, hinput]
  simpa only [toPoly_list_eq] using hres E

/-- The ordinary embedding preserves the genuine-log certificate of a coefficient result. -/
theorem AlgebraicCoefficientIntegralResult.logsGenuine_ofOrdinary
    (c : DenseFrac β) (res : CoefficientIntegralResult (DenseFrac β))
    (hres : IsCoefficientIntegralResult c res) :
    (AlgebraicCoefficientIntegralResult.ofOrdinary res).LogsGenuine := by
  intro log hlog
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlog
  exact ⟨hres.2.1 source hsource, hres.2.2 source hsource⟩

/-- The LRT embedding preserves root-free residue constancy. -/
theorem AlgebraicCoefficientIntegralResult.logsGenuine_ofLrt (res : LrtResult β)
    (hres : AllResiduesConstantLrt res) :
    (AlgebraicCoefficientIntegralResult.ofLrt res).LogsGenuine := by
  intro log hlog
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlog
  exact (List.all_eq_true.mp hres) source hsource

end DeepWiki.SymbolicIntegration
