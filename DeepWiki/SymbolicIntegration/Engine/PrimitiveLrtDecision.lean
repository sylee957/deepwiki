import DeepWiki.SymbolicIntegration.Engine.LrtCompleteness
import DeepWiki.SymbolicIntegration.Engine.ResidueConstantBridge

/-! # The primitive LRT integrator as a decision procedure (soundness + completeness)

The root-free residue guard characterizes genuine algebraic-residue elementary integrability in the
primitive case: `IsElementaryIntegrableGenuineLrt Dt a d ↔ cResidueConstantGuard Dt a d = true`.
-/

namespace DeepWiki.SymbolicIntegration

open DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-! ### Algorithm-selected decision API -/

section Selected

variable [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
  [Algebra ℚ (CFieldSpec.K α)]

/-- The primitive LRT guard characterizes genuine elementary integrability. -/
theorem primitiveLrtDecides [LrtLiouvilleFrontier α] (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hsuff : cResidueConstantGuard Dt a d = true → IsElementaryIntegrableGenuineLrt Dt a d) :
    IsElementaryIntegrableGenuineLrt Dt a d ↔ cResidueConstantGuard Dt a d = true :=
  ⟨LrtLiouvilleFrontier.descendGenuineLrt Dt a d hd0, hsuff⟩

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- A passing primitive LRT guard gives a genuine antiderivative from soundness and residue constancy. -/
theorem isElementaryIntegrableGenuineLrt_of_guard (Dt a d : DensePoly α)
    (hsound : IsIntegralResultLrt Dt a d (cIntegrateReducedLrt Dt a d))
    (hbridge : cResidueConstantGuard Dt a d = true →
      allResiduesConstantLrt (cIntegrateReducedLrt Dt a d) = true)
    (hguard : cResidueConstantGuard Dt a d = true) :
    IsElementaryIntegrableGenuineLrt Dt a d :=
  ⟨cIntegrateReducedLrt Dt a d, hsound, hbridge hguard⟩

end Selected

/-! ### Concrete correction-proof boundary -/

section Concrete

variable [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- A passing primitive LRT guard gives a genuine antiderivative with residue constancy discharged. -/
theorem isElementaryIntegrableGenuineLrt_of_guard_of_setup [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hR0 : toPoly (cResidueResultantTower Dt (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2) ≠ 0)
    (hsound : IsIntegralResultLrt Dt a d (cIntegrateReducedLrt Dt a d))
    (hguard : cResidueConstantGuard Dt a d = true) :
    IsElementaryIntegrableGenuineLrt Dt a d :=
  isElementaryIntegrableGenuineLrt_of_guard Dt a d hsound
    (allResiduesConstantLrtG_of_guard hgcd Dt a d hR0) hguard

/-- The fully assembled primitive LRT guard criterion for genuine elementary integrability. -/
theorem primitiveLrtDecides_of_setup [CharZero (CFieldSpec.K α)] [LrtLiouvilleFrontier α]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hR0 : toPoly (cResidueResultantTower Dt (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2) ≠ 0)
    (hsound : IsIntegralResultLrt Dt a d (cIntegrateReducedLrt Dt a d)) :
    IsElementaryIntegrableGenuineLrt Dt a d ↔ cResidueConstantGuard Dt a d = true :=
  primitiveLrtDecides Dt a d hd0
    (isElementaryIntegrableGenuineLrt_of_guard_of_setup hgcd Dt a d hR0 hsound)

end Concrete

end DeepWiki.SymbolicIntegration
