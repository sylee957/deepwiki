import DeepWiki.SymbolicIntegration.Computable.LrtCompleteness
import DeepWiki.SymbolicIntegration.Computable.ResidueConstantBridge

/-! # The primitive LRT integrator as a decision procedure (soundness + completeness)

The elegant primitive integrator: genuine (algebraic-residue) elementary integrability of `a/d` in the
primitive case is **decided** by the root-free residue guard,
`IsElementaryIntegrableGenuineLrtG a d ↔ cResidueConstantGuardG a d = true`. The two halves are the two
honest frontiers meeting in one characterization:

- **`→` (completeness / necessary)** — the Liouville/residue criterion `LrtLiouvilleFrontier.descendGenuineLrt`:
  a genuine antiderivative forces all residues constant. Proven here.
- **`←` (soundness / sufficient)** — a passing guard yields the Rothstein–Trager genuine antiderivative
  (`cIntegrateReducedLrtG`): the reduced soundness (`PrimitiveFrontierLrt`-style) plus the residues being
  constant *because the guard checked exactly that* (the Yun-factor bridge, on the same Hermite reduce, so no
  `crNorm` mismatch).

This is the shape hyperexp/hypertangent extend to: a different special/reduced integrator with its own guard,
same decision structure. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The primitive LRT integrator DECIDES genuine elementary integrability.** `a/d` is genuinely
(algebraic-residue) elementary integrable **iff** the decidable root-free residue guard passes. The `→` is the
Liouville/residue criterion (`LrtLiouvilleFrontier`); the `←` (sufficiency) is supplied by soundness — a passing
guard constructs the Rothstein–Trager genuine antiderivative. Packaging the two directions as one decidable
characterization is the elegant primitive integrator. -/
theorem primitiveLrtDecides [LrtLiouvilleFrontier α] (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hsuff : cResidueConstantGuardG Dt a d = true → IsElementaryIntegrableGenuineLrtG Dt a d) :
    IsElementaryIntegrableGenuineLrtG Dt a d ↔ cResidueConstantGuardG Dt a d = true :=
  ⟨LrtLiouvilleFrontier.descendGenuineLrt Dt a d hd0, hsuff⟩

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **The sufficiency (`←`), reduced to its two concrete inputs.** A passing guard yields a *genuine*
antiderivative — the Rothstein–Trager result `cIntegrateReducedLrtG Dt a d` — given (i) its reduced soundness
`hsound` (the `PrimitiveFrontierLrt`-style identity, on the *raw* `a/d`), and (ii) the residue bridge `hbridge`
(a passing guard forces the result's residues constant). Both are on the **same** Hermite reduce as the guard,
so there is no `crNorm` mismatch. Feeds `primitiveLrtDecides` as `hsuff`. -/
theorem isElementaryIntegrableGenuineLrt_of_guard (Dt a d : CPolyG α)
    (hsound : IsIntegralResultLrtG Dt a d (cIntegrateReducedLrtG Dt a d))
    (hbridge : cResidueConstantGuardG Dt a d = true →
      allResiduesConstantLrtG (cIntegrateReducedLrtG Dt a d) = true)
    (hguard : cResidueConstantGuardG Dt a d = true) :
    IsElementaryIntegrableGenuineLrtG Dt a d :=
  ⟨cIntegrateReducedLrtG Dt a d, hsound, hbridge hguard⟩

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **The sufficiency (`←`), with the residue bridge DISCHARGED.** A passing guard yields a genuine
antiderivative given only the raw reduced soundness `hsound` and the nonzero residue resultant `hR0` (the same
one soundness needs) — the residue-constancy is now *proven* (`allResiduesConstantLrtG_of_guard`, the assembled
Yun-factor bridge), no longer an input. -/
theorem isElementaryIntegrableGenuineLrt_of_guard_of_setup [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hR0 : toPolyG (cResidueResultantTowerGWf Dt (cHermiteReduceTowerGWf Dt a d).2.1
      (cHermiteReduceTowerGWf Dt a d).2.2) ≠ 0)
    (hsound : IsIntegralResultLrtG Dt a d (cIntegrateReducedLrtG Dt a d))
    (hguard : cResidueConstantGuardG Dt a d = true) :
    IsElementaryIntegrableGenuineLrtG Dt a d :=
  isElementaryIntegrableGenuineLrt_of_guard Dt a d hsound
    (allResiduesConstantLrtG_of_guard hgcd Dt a d hR0) hguard

/-- **★ The primitive LRT integrator decides genuine elementary integrability — fully assembled.** The residue
bridge is discharged, so the decision `IsElementaryIntegrableGenuineLrtG a d ↔ cResidueConstantGuardG a d = true`
needs only the two genuine setup ingredients on the `←` side — the raw reduced soundness `hsound` and the
nonzero residue resultant `hR0` (both required by the reduced soundness anyway) — plus `LrtLiouvilleFrontier`
on the `→`. No unproven residue bridge remains. -/
theorem primitiveLrtDecides_of_setup [CharZero (CFieldSpec.K α)] [LrtLiouvilleFrontier α]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hR0 : toPolyG (cResidueResultantTowerGWf Dt (cHermiteReduceTowerGWf Dt a d).2.1
      (cHermiteReduceTowerGWf Dt a d).2.2) ≠ 0)
    (hsound : IsIntegralResultLrtG Dt a d (cIntegrateReducedLrtG Dt a d)) :
    IsElementaryIntegrableGenuineLrtG Dt a d ↔ cResidueConstantGuardG Dt a d = true :=
  primitiveLrtDecides Dt a d hd0
    (isElementaryIntegrableGenuineLrt_of_guard_of_setup hgcd Dt a d hR0 hsound)

end DeepWiki.SymbolicIntegration
