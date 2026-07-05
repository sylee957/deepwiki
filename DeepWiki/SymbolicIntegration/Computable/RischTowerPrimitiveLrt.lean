import DeepWiki.SymbolicIntegration.Computable.LrtSoundness
import DeepWiki.SymbolicIntegration.Computable.CanonicalReconstructionCharZero

/-! # The LRT (root-free) primitive reduced frontier — the algebraic-residue analogue of `PrimitiveFrontier`

The rational reduced frontier (`PrimitiveFrontier.hreduced`) demands `IsIntegralResultG`: the Liouville form
with **rational** residue coefficients `cᵢ ∈ K` and log arguments in `K[t]`. That obligation forces the
reduced denominator to split over `K`; when the residues are algebraic it is simply false, so no general
instance of `PrimitiveFrontier` exists. The root-free Lazard–Rioboo–Trager integrator `cIntegrateReducedLrtG`
avoids root-finding, and its soundness `IsIntegralResultLrtG` is the *algebraic-residue* analogue: over every
algebraically-closed differential extension `E`, the `E`-derivative of the rational part plus the symbolic
algebraic-residue log sum equals `a/d`.

This file packages that as the parallel frontier `PrimitiveFrontierLrt` (single field `hreducedLrt`) with the
broad (algebraic-residue) elementary-integrability target `IsElementaryIntegrableLrtG`, and the reductions
tying them to the assembled soundness `isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **Broad (algebraic-residue) elementary integrability.** `a/d` has an antiderivative in the extended
Liouville form `⟦rational⟧ + Σᵢ Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))` — an `LrtResultG`, whose residue coefficients
`c` may be **algebraic** over the constants. The root-free analogue of `IsElementaryIntegrableG`, which
restricts the coefficients to `K`. -/
def IsElementaryIntegrableLrtG (Dt a d : CPolyG α) : Prop :=
  ∃ res : LrtResultG α, IsIntegralResultLrtG Dt a d res

omit [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The LRT soundness→completeness bridge.** Any `IsIntegralResultLrtG` witness makes `a/d`
elementary-integrable in the broad (algebraic-residue) sense — verbatim, the LRT analogue of
`IsElementaryIntegrableG.of_isIntegralResult`. -/
theorem IsElementaryIntegrableLrtG.of_isIntegralResultLrt {Dt a d : CPolyG α} {res : LrtResultG α}
    (h : IsIntegralResultLrtG Dt a d res) : IsElementaryIntegrableLrtG Dt a d :=
  ⟨res, h⟩

/-- **The LRT primitive reduced frontier, as a class.** The root-free analogue of `PrimitiveFrontier`: the
single field `hreducedLrt` asserts the reduced normal part `cₙ/dₙ` integrates correctly *with algebraic
residues* — `IsIntegralResultLrtG` for the symbolic integrator `cIntegrateReducedLrtG`. Discharged (modulo the
genuine Bronstein side conditions) by `isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup`; unlike the
rational `hreduced`, there is **no** rational-residue restriction. -/
class PrimitiveFrontierLrt (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    [Fact (GcdFFCorrect (α := α))] where
  /-- Reduced-part soundness with algebraic residues: `cₙ/dₙ` integrates to `cIntegrateReducedLrtG …`, whose
  log part carries symbolic algebraic residues. The `d ≠ 0` precondition is supplied by the integrator guard;
  the normalized-denominator nonvanishing is *proven* downstream (Hermite denominator ≠ 0 from `dₙ ≠ 0`). -/
  hreducedLrt : ∀ (Dt a d : CPolyG α), toPolyG d ≠ 0 →
    IsIntegralResultLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d))

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **`hreducedLrt` from a universal reduced soundness.** If `cIntegrateReducedLrtG` is sound on *every*
reduced input `(a', d')` with `d' ≠ 0` (which `isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup` supplies
per input, modulo the genuine side conditions), then the frontier field `hreducedLrt` holds — specialize to
the canonical normalized parts `(cₙ, dₙ)`, whose denominator is nonzero (`crNormDen_ne_zero_of_charZero`). -/
theorem hreducedLrt_of_reducedSoundLrt [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (hRed : ∀ (Dt a' d' : CPolyG α), toPolyG d' ≠ 0 →
      IsIntegralResultLrtG Dt a' d' (cIntegrateReducedLrtG Dt a' d'))
    (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0) :
    IsIntegralResultLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)) :=
  hRed Dt (crNormNum Dt a d) (crNormDen Dt a d) (crNormDen_ne_zero_of_charZero hgcd Dt a d hd0)

/-- **The frontier certifies broad elementary integrability of the reduced normal part.** From a
`PrimitiveFrontierLrt` instance, the canonical normal part `cₙ/dₙ` is elementary-integrable in the
algebraic-residue sense — the LRT analogue of the reduced-part payoff of `PrimitiveFrontier`. -/
theorem isElementaryIntegrableLrtG_crNorm_of_frontier [CharZero (CFieldSpec.K α)]
    [Fact (GcdFFCorrect (α := α))] [PrimitiveFrontierLrt α] (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0) :
    IsElementaryIntegrableLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d) :=
  ⟨_, PrimitiveFrontierLrt.hreducedLrt Dt a d hd0⟩

end DeepWiki.SymbolicIntegration
