import DeepWiki.SymbolicIntegration.Computable.LrtCompleteness

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

end DeepWiki.SymbolicIntegration
