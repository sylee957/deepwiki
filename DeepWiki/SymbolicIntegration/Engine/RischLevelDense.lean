import DeepWiki.SymbolicIntegration.Engine.RischLevel
import DeepWiki.SymbolicIntegration.Engine.ResidueLogPartDense
import DeepWiki.SymbolicIntegration.Engine.CanonicalReconstructionCharZero
import DeepWiki.SymbolicIntegration.Engine.Hermite.ReductionDenseLawful

/-! # Dense realization of the compositional Risch level

The legacy drivers accept an explicit list of residue candidates.  This module adapts that list to
the representation-neutral `CResidueSource` capability and runs the generic one-level pipeline;
its normal branch therefore exposes logs only after the checked dense residue realization accepts
them. -/

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CPolyGcd DensePoly α]
  [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]

/-- Run the generic one-level Risch pipeline using the caller's explicit dense residue candidates. -/
def cIntegrateCaseChecked (C : CMonomialCase DensePoly α) (cands : List α)
    (Dt a d : DensePoly α) : Option (IntegralResult α) :=
  let _ : CResidueSource DensePoly α := { candidates := fun _ => cands }
  (oneLevelRisch C).integrate Dt a d

/-- Run the polynomial-aware generic Risch pipeline with an explicit reduction budget. -/
def cIntegrateCaseCheckedWithPolynomial (kind : PolynomialReductionKind) (fuel : ℕ)
    (C : CMonomialCase DensePoly α) (cands : List α)
    (Dt a d : DensePoly α) : Option (IntegralResult α) :=
  let _ : CResidueSource DensePoly α := { candidates := fun _ => cands }
  (oneLevelRischWithPolynomial (towerPolynomialReduction (P := DensePoly) (α := α)) kind fuel C).integrate
    Dt a d

end DensePoly

open Polynomial

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
  [CFracGcdCoreWf α]
  [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))]
  [CPolyGcd DensePoly α]
  [CPolySplitFactor DensePoly α] [LawfulCPolySplitFactor DensePoly α]
  [CPolyResultant DensePoly]

/-- A successful checked dense one-level run satisfies the representation-neutral integral specification. -/
theorem DensePoly.cIntegrateCaseChecked_sound (C : CMonomialCase DensePoly α)
    [LawfulCMonomialCase C] (cands : List α) (Dt a d : DensePoly α) (res : IntegralResult α)
    (hd : CPoly.toPoly d ≠ 0) (hdegree : (CPoly.toPoly Dt).natDegree ≤ 1)
    (hrun : DensePoly.cIntegrateCaseChecked C cands Dt a d = some res) :
    IsIntegralResultP Dt a d res := by
  letI : CResidueSource DensePoly α := { candidates := fun _ => cands }
  change assembleOneLevel C Dt a d = some res at hrun
  exact assembleOneLevel_sound C Dt a d res hd hdegree hrun

end DeepWiki.SymbolicIntegration
