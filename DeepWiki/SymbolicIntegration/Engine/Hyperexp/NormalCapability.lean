import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalSemantic
import DeepWiki.SymbolicIntegration.Engine.NormalReduction

/-! # Checked hyperexponential normal-reduction capability

The residual-feedback normal solver becomes a sound `CNormalReduction` after its result passes the
representation-independent identity and denominator checks.
-/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u v

namespace DensePoly

variable {α : Type u} [CField α] [CDiffField α] [CRischField α]
  [CPolyGcd DensePoly α] [CPolySquarefree DensePoly α]
  [CPolyResultant DensePoly] [CResidueSource DensePoly α]

/-- Raw residual-feedback normal reduction before the representation-independent certificate check. -/
def hyperexpResidualNormalReduction : CNormalReduction DensePoly α where
  reduce Dt a d :=
    let red := cIntegrateReduced Dt a d
      (CResidueSource.candidates (cResidueResultantTower Dt a d))
    cCorrectHyperexpNormal (cExpEta Dt) red

end DensePoly

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α]
  [CDiffFieldSpec.{u,v} α] [CRischField α] [Algebra ℚ (CFieldSpec.K α)]
  [CPolyGcd DensePoly α] [CPolySquarefree DensePoly α]
  [CPolyResultant DensePoly] [CResidueSource DensePoly α]

/-- Residual-feedback hyperexponential normal reduction with generic certificate validation. -/
def hyperexpCheckedNormalReduction : CNormalReduction DensePoly α where
  reduce := checkedNormalReduction (DensePoly.hyperexpResidualNormalReduction (α := α)) |>.reduce

/-- The checked hyperexponential normal solver is sound on every accepted input. -/
abbrev hyperexpCheckedNormalDomain : NormalReductionDomain DensePoly α :=
  checkedNormalReductionDomain

/-- Semantic completeness domain for residual-feedback normal reduction: the deterministic reduced
candidate has the required residual identity and its scalar residual RDE is solvable. -/
def hyperexpResidualNormalCompleteDomain : NormalReductionDomain DensePoly α := fun Dt a d =>
  HyperexpResidualCorrectionDomain Dt (DensePoly.cExpEta Dt) a d
    (DensePoly.cIntegrateReduced Dt a d
      (CResidueSource.candidates (DensePoly.cResidueResultantTower Dt a d)))

/-- The checked residual-feedback normal operation satisfies the normal-reduction soundness contract. -/
instance instLawfulCNormalReductionHyperexpChecked :
    LawfulCNormalReduction (hyperexpCheckedNormalReduction (α := α))
      (hyperexpCheckedNormalDomain (α := α)) := by
  unfold hyperexpCheckedNormalReduction hyperexpCheckedNormalDomain
  infer_instance

/-- The checked hyperexponential normal stage is lawful on its semantic residual-correction domain. -/
instance instLawfulCNormalReductionHyperexpSemantic :
    LawfulCNormalReduction (hyperexpCheckedNormalReduction (α := α))
      (hyperexpResidualNormalCompleteDomain (α := α)) := by
  unfold hyperexpCheckedNormalReduction
  infer_instance

/-- Field-RDE completeness makes semantic residual-feedback normal inputs executable. -/
theorem completeCNormalReductionHyperexpSemantic [CRischFieldSpec α]
    (hfield : CRischFieldComplete α) :
    CompleteCNormalReduction (hyperexpCheckedNormalReduction (α := α))
      (hyperexpResidualNormalCompleteDomain (α := α)) where
  relative_complete Dt a d hdomain hd _ := by
    let red := DensePoly.cIntegrateReduced Dt a d
      (CResidueSource.candidates (DensePoly.cResidueResultantTower Dt a d))
    obtain ⟨out, hraw, hcert⟩ := cCorrectHyperexpNormal_exists_of_domain hfield Dt
      (DensePoly.cExpEta Dt) a d red hdomain
    have hcheck := normalReductionCheck_of_certified Dt a d out hd hcert
    refine ⟨out, ?_, hcert⟩
    simp [hyperexpCheckedNormalReduction, DensePoly.hyperexpResidualNormalReduction,
      checkedNormalReduction, red, hraw, hcheck]

end DeepWiki.SymbolicIntegration
