import DeepWiki.SymbolicIntegration.Engine.LrtGuarded

/-! # LRT completeness — the decidable non-integrability certificate (root-free)

The completeness half of the primitive LRT tower. The residue-constancy guard `cResidueConstantGuard` is
**necessary** for genuine (broad) elementary integrability: `cIntegrateReducedLrt`'s log part
`Σ c·D(Sᵢ)/Sᵢ` differentiates back to `a/d` only when every residue `c` is a constant, and the residues are
the roots of the Rothstein–Trager residue resultant `R`, all constant iff `D(monic R) = 0` (root-free,
decidable). `LrtLiouvilleFrontier` holds the Liouville/residue **descent** (genuine-integrable ⟹ guard passes)
as a frontier field — the primitive-case residue criterion (Bronstein Thm 5.6.1), whose abstract keystone is
done in-project (`LiouvilleLog.isLiouville_logExtension_uncond` + the residue criterion). The derived
`not_isElementaryIntegrableGenuineLrt` is a decidable non-integrability certificate — the algebraic-residue
analogue of `LiouvilleFrontier` / `not_isElementaryIntegrableGenuine`, with **no rational-residue restriction**. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **The LRT completeness frontier (Liouville criterion), as a class.** `descendGenuineLrt`: genuine (broad)
elementary integrability implies the residues are constants (`cResidueConstantGuard = true`, root-free
decidable). This implication is the primitive-case residue criterion (Bronstein Thm 5.6.1); its abstract math
is done in-project (`isLiouville_logExtension_uncond`, the transcendental log Liouville keystone; the residue
criterion), so this field is the computable→abstract bridge for the algebraic (LRT) residues, not a missing
theorem. The completeness analogue of the reduced-soundness frontier `PrimitiveFrontierLrt`. -/
class LrtLiouvilleFrontier (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [Algebra ℚ (CFieldSpec.K α)] where
  /-- Genuine (broad) elementary integrability ⟹ the residue-constancy guard passes. -/
  descendGenuineLrt : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 →
    IsElementaryIntegrableGenuineLrt Dt a d → cResidueConstantGuard Dt a d = true

/-- **Derived completeness — a decidable non-integrability certificate (root-free).** If the integrability
guard *fails* (`cResidueConstantGuard = false`: some residue is non-constant), then `a/d` is **not** genuinely
(broadly) elementary integrable. Non-vacuous, and with **no rational-residue restriction** (unlike the rational
`not_isElementaryIntegrableGenuine`) — modulo the Liouville frontier `descendGenuineLrt`. -/
theorem not_isElementaryIntegrableGenuineLrt [LrtLiouvilleFrontier α] (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0) (hguard : cResidueConstantGuard Dt a d = false) :
    ¬ IsElementaryIntegrableGenuineLrt Dt a d := by
  intro h
  rw [LrtLiouvilleFrontier.descendGenuineLrt Dt a d hd0 h] at hguard
  simp at hguard

end DeepWiki.SymbolicIntegration
