import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalCore
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

/-- Raw residual-feedback integration of a hyperexponential normal fraction. -/
def hyperexpNormalReduction : CNormalReduction DensePoly α where
  reduce Dt a d :=
    cIntegrateHyperexpNormal Dt a d
      (CResidueSource.candidates (cResidueResultantTower Dt a d))

end DensePoly

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α]
  [CDiffFieldSpec.{u,v} α] [CRischField α] [Algebra ℚ (CFieldSpec.K α)]
  [CPolyGcd DensePoly α] [CPolySquarefree DensePoly α]
  [CPolyResultant DensePoly] [CResidueSource DensePoly α]

/-- Residual-feedback hyperexponential normal reduction with generic certificate validation. -/
def hyperexpCheckedNormalReduction : CNormalReduction DensePoly α where
  reduce := checkedNormalReduction (DensePoly.hyperexpNormalReduction (α := α)) |>.reduce

/-- The checked hyperexponential normal solver is sound on every accepted input. -/
abbrev hyperexpCheckedNormalDomain : NormalReductionDomain DensePoly α :=
  checkedNormalReductionDomain

/-- The checked residual-feedback normal operation satisfies the normal-reduction soundness contract. -/
instance instLawfulCNormalReductionHyperexpChecked :
    LawfulCNormalReduction (hyperexpCheckedNormalReduction (α := α))
      (hyperexpCheckedNormalDomain (α := α)) := by
  unfold hyperexpCheckedNormalReduction hyperexpCheckedNormalDomain
  infer_instance

/-- The checked hyperexponential normal stage is lawful on its explicit raw-acceptance domain. -/
instance instLawfulCNormalReductionHyperexpCheckedAcceptance :
    LawfulCNormalReduction (hyperexpCheckedNormalReduction (α := α))
      (checkedNormalReductionAcceptanceDomain
        (DensePoly.hyperexpNormalReduction (α := α))) := by
  unfold hyperexpCheckedNormalReduction
  infer_instance

/-- The checked hyperexponential normal stage is complete on its explicit raw-acceptance domain. -/
instance instCompleteCNormalReductionHyperexpChecked :
    CompleteCNormalReduction (hyperexpCheckedNormalReduction (α := α))
      (checkedNormalReductionAcceptanceDomain
        (DensePoly.hyperexpNormalReduction (α := α))) := by
  unfold hyperexpCheckedNormalReduction
  infer_instance

end DeepWiki.SymbolicIntegration
