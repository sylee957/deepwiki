import DeepWiki.SymbolicIntegration.Computable.GenuineSoundness
import DeepWiki.SymbolicIntegration.Computable.LrtGuarded

/-! # Structured completeness for the primitive case — the Liouville frontier

The `LawfulRischLevel` completeness contract is trivial in the primitive instance (`SpecElem = NrmElem = True`),
so `not_isElementaryIntegrable` is vacuous. This file makes it **meaningful**, against the well-posed target
`IsElementaryIntegrableGenuineG` (genuine, residue-constant integrability): the necessary condition is the
decidable root-free integrability guard `cResidueConstantGuardG` (residues constant ⟺ `D(R) = 0`), and the
descent — genuine integrability ⟹ residues constant — is the transcendental **Liouville theorem** for the
primitive case, held as a frontier class field (the completeness analogue of `PrimitiveFrontier.hreduced`).
Mathlib has only the algebraic Liouville case, so the descent is a genuine frontier; everything else is
derived. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The primitive completeness frontier (Liouville criterion), as a class.** `descendGenuine` states the
necessary condition for *genuine* elementary integrability of the reduced normal part: the residues are
constants, i.e. the residue resultant has constant coefficients (`cResidueConstantGuardG`, root-free,
decidable). This implication — genuine integrability ⟹ residues constant — is exactly the transcendental
Liouville theorem (Bronstein Thm 5.6.1); Mathlib has only the algebraic case, so it is a genuine frontier. -/
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
