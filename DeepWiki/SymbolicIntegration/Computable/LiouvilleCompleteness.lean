import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitive
import DeepWiki.SymbolicIntegration.Computable.LrtGuarded

/-! # Structured completeness for the primitive case — the Liouville frontier

`LawfulRischLevel` is soundness-only (its `sound` is genuine; completeness is decoupled here so soundness
resolution never depends on the completeness frontier). This file provides the completeness, against the
well-posed target `IsElementaryIntegrableGenuineG` (genuine, residue-constant integrability): the necessary
condition is the
decidable root-free integrability guard `cResidueConstantGuardG` (residues constant ⟺ monic `D(R) = 0`), and the
descent — genuine integrability ⟹ residues constant — is the primitive-case Liouville/residue criterion
(Bronstein Thm 5.6.1), held as a frontier class field (the completeness analogue of `PrimitiveFrontier.hreduced`).

**Status of the descent** (not a Mathlib gap): the transcendental **log** Liouville keystone is *already proven
in-project* — `LiouvilleLog.isLiouville_logExtension_uncond` (`IsLiouville F F(log u)` from the necessary
`NondegenerateLog u`), axiom-clean — as is the rational residue criterion
(`ratFunc_logarithmFree_iff_residues_zero`). So `descendGenuine` is not research-grade: it is the
computable→abstract **bridge** (relate `cResidueResultantTowerGWf`'s roots to the abstract residues via the
soundness-side `roots_rtResultantGen`/`toPolyG_cResidueResultantTowerGWf_map`, and `IsElementaryIntegrableGenuineG`
to the abstract Liouville form via `logResidueSumG = Σ (toK cᵢ)·logDeriv(amG vᵢ)`), plus the residue-matching
core (for a reduced `a/d`, the rational part cannot carry a simple-pole residue, so all residues are the
constant log coefficients). That bridge is large but project-internal, not a missing theorem. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The primitive completeness frontier (Liouville criterion), as a class.** `descendGenuine` states the
necessary condition for *genuine* elementary integrability of the reduced normal part: the residues are
constants, i.e. the monic residue resultant has constant coefficients (`cResidueConstantGuardG`, root-free,
decidable). This implication — genuine integrability ⟹ residues constant — is the primitive-case residue
criterion (Bronstein Thm 5.6.1). Its abstract math is done in-project (`isLiouville_logExtension_uncond`, the
transcendental log Liouville keystone; `ratFunc_logarithmFree_iff_residues_zero`, the residue criterion); this
field is the computable→abstract bridge to those results (see the module docstring), not a missing theorem. -/
class LiouvilleFrontier (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] where
  descendGenuine : ∀ (Dt a d : CPolyG α), toPolyG d ≠ 0 →
    IsElementaryIntegrableGenuineG Dt a d → cResidueConstantGuardG Dt a d = true

/-- **Derived completeness — a decidable non-integrability certificate.** If the root-free integrability guard
*fails* (`cResidueConstantGuardG = false`: some residue is non-constant), then `a/d` is **not** genuinely
elementary integrable. Non-vacuous (unlike the trivial `LawfulRischLevel` completeness contract), modulo the
Liouville frontier `descendGenuine`. -/
theorem not_isElementaryIntegrableGenuine [LiouvilleFrontier α] (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hguard : cResidueConstantGuardG Dt a d = false) : ¬ IsElementaryIntegrableGenuineG Dt a d := by
  intro h
  rw [LiouvilleFrontier.descendGenuine Dt a d hd0 h] at hguard
  simp at hguard

end DeepWiki.SymbolicIntegration
