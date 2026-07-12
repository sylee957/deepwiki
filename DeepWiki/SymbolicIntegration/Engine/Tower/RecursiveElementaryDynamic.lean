import DeepWiki.SymbolicIntegration.Engine.RecursiveCoefficient
import DeepWiki.SymbolicIntegration.Engine.Tower.Stage

/-! # Explicit-derivation recursive elementary coefficient stages

Recursive coefficient integration is a stage in its own right. This interface avoids the implicit
`CDiffField` instance by carrying the selected computable and semantic derivatives explicitly, then
exports accepted results through the common output-remainder contract.
-/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- A recursive elementary coefficient integrator selected for one explicit computable derivation. -/
structure CRecursiveElementaryIntegratorWith (α : Type u) [CField α]
    (derivation : CFieldDerivation α) where
  /-- Integrate a coefficient to a rational part plus lower-field logarithms, if possible. -/
  integrate : ℕ → α → Option (CoefficientIntegralResult α)

/-- The logarithmic derivative sum selected by an explicit coefficient derivation. -/
def coefficientLogSumWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (logs : List (α × α)) : CFieldSpec.K α :=
  (logs.map fun cv => CFieldSpec.toK cv.1 *
    (CFieldSpec.toK (derivation.cderiv cv.2) / CFieldSpec.toK cv.2)).sum

/-- A recursive elementary result is sound for the selected explicit coefficient differential. -/
def IsCoefficientIntegralResultWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (c : α) (res : CoefficientIntegralResult α) : Prop :=
  @Differential.deriv _ _ diffK (CFieldSpec.toK res.rational) +
      coefficientLogSumWith derivation res.logs = CFieldSpec.toK c ∧
    (∀ cv ∈ res.logs, @Differential.deriv _ _ diffK (CFieldSpec.toK cv.1) = 0) ∧
    (∀ cv ∈ res.logs, CFieldSpec.toK cv.2 ≠ 0)

/-- A coefficient admits an elementary antiderivative for an explicit derivative when it has a witness. -/
def IsCoefficientElementarilyIntegrableWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α)) (c : α) : Prop :=
  ∃ res : CoefficientIntegralResult α, IsCoefficientIntegralResultWith derivation diffK c res

/-- Soundness law for an explicit recursive elementary coefficient integrator. -/
class LawfulCRecursiveElementaryIntegratorWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (C : CRecursiveElementaryIntegratorWith α derivation) : Prop where
  /-- Every accepted result is an elementary antiderivative under the selected differential. -/
  sound : ∀ fuel c res, C.integrate fuel c = some res →
    IsCoefficientIntegralResultWith derivation diffK c res

/-- Semantic input domain for explicit recursive elementary coefficient integration. -/
abbrev RecursiveElementaryDomainWith (α : Type u) := α → Prop

/-- Relative completeness law for an explicit recursive elementary coefficient integrator. -/
class CompleteCRecursiveElementaryIntegratorWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (C : CRecursiveElementaryIntegratorWith α derivation)
    (domain : RecursiveElementaryDomainWith α)
    [LawfulCRecursiveElementaryIntegratorWith derivation diffK C] : Prop where
  /-- Every in-domain coefficient with an elementary witness is eventually accepted. -/
  complete : ∀ c, domain c → IsCoefficientElementarilyIntegrableWith derivation diffK c →
    ∃ fuel res, C.integrate fuel c = some res

/-- Export an explicit recursive elementary coefficient solver as a common remainder stage. -/
noncomputable def CRecursiveElementaryIntegratorWith.asRemainderIntegrationStage
    {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (C : CRecursiveElementaryIntegratorWith α derivation)
    (domain : RecursiveElementaryDomainWith α)
    [LawfulCRecursiveElementaryIntegratorWith derivation diffK C]
    [CompleteCRecursiveElementaryIntegratorWith derivation diffK C domain] :
    RemainderIntegrationStage α (CoefficientIntegralResult α) Unit
      (IsCoefficientElementarilyIntegrableWith derivation diffK)
      (fun c result _ => IsCoefficientIntegralResultWith derivation diffK c result) :=
  { stage :=
      { run := fun fuel c => (C.integrate fuel c).map fun result => ⟨result, ()⟩
        domain := domain
        sound := by
          intro fuel c result _ hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact LawfulCRecursiveElementaryIntegratorWith.sound fuel c out hout
        complete := by
          intro c hdomain hintegrable
          obtain ⟨fuel, result, hrun⟩ :=
            CompleteCRecursiveElementaryIntegratorWith.complete
              (C := C) (domain := domain) c hdomain hintegrable
          exact ⟨fuel, ⟨result, ()⟩, by simp [hrun]⟩ } }

/-! ### Compatibility adapter for legacy coefficient recursion -/

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]
  [CDiffField α] [CDiffFieldSpec.{u,v} α]

/-- The legacy recursive elementary solver viewed through its explicit coefficient derivation. -/
@[reducible] noncomputable def CRecursiveElementaryIntegrator.asWith
    (C : CRecursiveElementaryIntegrator α) :
    CRecursiveElementaryIntegratorWith α (CFieldDerivation.ofCDiffField α) where
  integrate := C.integrate

omit [CDiffFieldSpec α] in
/-- The explicit and legacy coefficient logarithmic sums agree in the compatibility context. -/
theorem coefficientLogSumWith_ofCDiffField (logs : List (α × α)) :
    coefficientLogSumWith (CFieldDerivation.ofCDiffField α) logs = coefficientLogSum logs := by
  simp only [coefficientLogSumWith, CFieldDerivation.ofCDiffField, coefficientLogSum]

/-- The legacy elementary coefficient certificate is the explicit certificate in the compatibility context. -/
theorem isCoefficientIntegralResultWith_ofCDiffField_iff (c : α) (res : CoefficientIntegralResult α) :
    IsCoefficientIntegralResultWith (CFieldDerivation.ofCDiffField α) CDiffFieldSpec.diffK c res ↔
      IsCoefficientIntegralResult c res := by
  unfold IsCoefficientIntegralResultWith IsCoefficientIntegralResult
  rw [coefficientLogSumWith_ofCDiffField]
  simp only [CDiffFieldSpec.toK_cderiv]

/-- Promote a lawful legacy coefficient solver to the explicit-differential contract. -/
@[reducible] noncomputable def LawfulCRecursiveElementaryIntegratorWith.ofLegacy
    (C : CRecursiveElementaryIntegrator α) [LawfulCRecursiveElementaryIntegrator C] :
    LawfulCRecursiveElementaryIntegratorWith (CFieldDerivation.ofCDiffField α)
      CDiffFieldSpec.diffK C.asWith where
  sound fuel c res hrun :=
    (isCoefficientIntegralResultWith_ofCDiffField_iff c res).mpr
      (LawfulCRecursiveElementaryIntegrator.sound fuel c res hrun)

/-- Promote a complete legacy coefficient solver to the explicit-differential contract. -/
@[reducible] noncomputable def CompleteCRecursiveElementaryIntegratorWith.ofLegacy
    (C : CRecursiveElementaryIntegrator α) (domain : RecursiveElementaryDomain (α := α))
    [LawfulCRecursiveElementaryIntegrator C] [CompleteCRecursiveElementaryIntegrator C domain] :
    @CompleteCRecursiveElementaryIntegratorWith α _ _
      (CFieldDerivation.ofCDiffField α) CDiffFieldSpec.diffK C.asWith domain
      (@LawfulCRecursiveElementaryIntegratorWith.ofLegacy α _ _ _ _ C _) := by
  letI : LawfulCRecursiveElementaryIntegratorWith (CFieldDerivation.ofCDiffField α)
      CDiffFieldSpec.diffK C.asWith := LawfulCRecursiveElementaryIntegratorWith.ofLegacy C
  refine ⟨?_⟩
  intro c hdomain hintegrable
  obtain ⟨witness, hwitness⟩ := hintegrable
  obtain ⟨fuel, result, hrun⟩ := CompleteCRecursiveElementaryIntegrator.complete
    (C := C) (domain := domain) c hdomain
      ⟨witness, (isCoefficientIntegralResultWith_ofCDiffField_iff c witness).mp hwitness⟩
  exact ⟨fuel, result, hrun⟩

end DeepWiki.SymbolicIntegration
