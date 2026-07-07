import DeepWiki.SymbolicIntegration.Computable.LrtCompleteness
import DeepWiki.SymbolicIntegration.Computable.ResidueConstantBridge

/-! # The primitive LRT integrator as a decision procedure (soundness + completeness)

The root-free residue guard characterizes genuine algebraic-residue elementary integrability in the
primitive case: `IsElementaryIntegrableGenuineLrtG Dt a d ↔ cResidueConstantGuardG Dt a d = true`.
-/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- The primitive LRT guard characterizes genuine elementary integrability. -/
theorem primitiveLrtDecides [LrtLiouvilleFrontier α] (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hsuff : cResidueConstantGuardG Dt a d = true → IsElementaryIntegrableGenuineLrtG Dt a d) :
    IsElementaryIntegrableGenuineLrtG Dt a d ↔ cResidueConstantGuardG Dt a d = true :=
  ⟨LrtLiouvilleFrontier.descendGenuineLrt Dt a d hd0, hsuff⟩

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- A passing primitive LRT guard gives a genuine antiderivative from soundness and residue constancy. -/
theorem isElementaryIntegrableGenuineLrt_of_guard (Dt a d : CPolyG α)
    (hsound : IsIntegralResultLrtG Dt a d (cIntegrateReducedLrtG Dt a d))
    (hbridge : cResidueConstantGuardG Dt a d = true →
      allResiduesConstantLrtG (cIntegrateReducedLrtG Dt a d) = true)
    (hguard : cResidueConstantGuardG Dt a d = true) :
    IsElementaryIntegrableGenuineLrtG Dt a d :=
  ⟨cIntegrateReducedLrtG Dt a d, hsound, hbridge hguard⟩

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- A passing primitive LRT guard gives a genuine antiderivative with residue constancy discharged. -/
theorem isElementaryIntegrableGenuineLrt_of_guard_of_setup [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hR0 : toPolyG (cResidueResultantTowerGWf Dt (cHermiteReduceTowerGWf Dt a d).2.1
      (cHermiteReduceTowerGWf Dt a d).2.2) ≠ 0)
    (hsound : IsIntegralResultLrtG Dt a d (cIntegrateReducedLrtG Dt a d))
    (hguard : cResidueConstantGuardG Dt a d = true) :
    IsElementaryIntegrableGenuineLrtG Dt a d :=
  isElementaryIntegrableGenuineLrt_of_guard Dt a d hsound
    (allResiduesConstantLrtG_of_guard hgcd Dt a d hR0) hguard

/-- The fully assembled primitive LRT guard criterion for genuine elementary integrability. -/
theorem primitiveLrtDecides_of_setup [CharZero (CFieldSpec.K α)] [LrtLiouvilleFrontier α]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hR0 : toPolyG (cResidueResultantTowerGWf Dt (cHermiteReduceTowerGWf Dt a d).2.1
      (cHermiteReduceTowerGWf Dt a d).2.2) ≠ 0)
    (hsound : IsIntegralResultLrtG Dt a d (cIntegrateReducedLrtG Dt a d)) :
    IsElementaryIntegrableGenuineLrtG Dt a d ↔ cResidueConstantGuardG Dt a d = true :=
  primitiveLrtDecides Dt a d hd0
    (isElementaryIntegrableGenuineLrt_of_guard_of_setup hgcd Dt a d hR0 hsound)

end DeepWiki.SymbolicIntegration
