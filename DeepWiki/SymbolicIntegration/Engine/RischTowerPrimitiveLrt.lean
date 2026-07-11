import DeepWiki.SymbolicIntegration.Engine.LrtSoundness
import DeepWiki.SymbolicIntegration.Engine.LrtResidueResultantDischarge
import DeepWiki.SymbolicIntegration.Engine.CanonicalReconstructionCharZero

/-! # The LRT (root-free) primitive reduced frontier — the algebraic-residue analogue of `PrimitiveFrontier`

The rational reduced frontier (`PrimitiveFrontier.hreduced`) demands `IsIntegralResult`: the Liouville form
with **rational** residue coefficients `cᵢ ∈ K` and log arguments in `K[t]`. That obligation forces the
reduced denominator to split over `K`; when the residues are algebraic it is simply false, so no general
instance of `PrimitiveFrontier` exists. The root-free Lazard–Rioboo–Trager integrator `cIntegrateReducedLrt`
avoids root-finding, and its soundness `IsIntegralResultLrt` is the *algebraic-residue* analogue: over every
algebraically-closed differential extension `E`, the `E`-derivative of the rational part plus the symbolic
algebraic-residue log sum equals `a/d`.

This file packages that as the parallel frontier `PrimitiveFrontierLrt` (single field `hreducedLrt`) with the
broad (algebraic-residue) elementary-integrability target `IsElementaryIntegrableLrt`, and the reductions
tying them to the assembled soundness `isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup`.

**Closing `hreducedLrt`.** `hreducedLrt_of_genuineAll` closes the frontier down to the bundled genuine data
`LrtReducedGenuineData` (Rothstein–Trager residue-data + the primitive-case `Dt` constant + the three
per-extension nondegeneracy conditions `hB`/`hnorm`/`hilt`): given that data for every reduced input, the LRT
primitive reduced soundness is a *theorem*, so `PrimitiveFrontierLrt` is `⟨hreducedLrt_of_genuineAll hgcd data⟩`.
Those conditions are Bronstein's necessary hypotheses (a properly-built tower satisfies them, but they are not
provable from the computable data alone), so this is the honest closure — the residual is exactly the genuine
integrability conditions, not an opaque soundness obligation. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac Polynomial
open scoped Differential

universe u v

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec α]

/-- **Broad (algebraic-residue) elementary integrability.** `a/d` has an antiderivative in the extended
Liouville form `⟦rational⟧ + Σᵢ Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))` — an `LrtResult`, whose residue coefficients
`c` may be **algebraic** over the constants. The root-free analogue of `IsElementaryIntegrable`, which
restricts the coefficients to `K`. -/
def IsElementaryIntegrableLrt (Dt a d : DensePoly α) : Prop :=
  ∃ res : LrtResult α, IsIntegralResultLrt Dt a d res

/-- **The LRT soundness→completeness bridge.** Any `IsIntegralResultLrt` witness makes `a/d`
elementary-integrable in the broad (algebraic-residue) sense — verbatim, the LRT analogue of
`IsElementaryIntegrable.of_isIntegralResult`. -/
theorem IsElementaryIntegrableLrt.of_isIntegralResultLrt {Dt a d : DensePoly α} {res : LrtResult α}
    (h : IsIntegralResultLrt Dt a d res) : IsElementaryIntegrableLrt Dt a d :=
  ⟨res, h⟩

/-- **The proper reduced LRT result contract.** This certifies the selected
`cIntegrateReducedLrt` output for every proper input, together with the nonzero stored rational denominator.
It is the semantic boundary between a concrete reduced-integrator realization and consumers that only compose
its result. -/
class LrtReducedProperFrontier (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] : Prop where
  /-- A proper reduced input has the selected root-free LRT antiderivative. -/
  sound : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
    (toPoly a).degree < (toPoly d).degree →
    IsIntegralResultLrt Dt a d (cIntegrateReducedLrt Dt a d)
  /-- The selected reduced LRT result stores a nonzero rational denominator. -/
  rational_den_nonzero : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
    toPoly (cIntegrateReducedLrt Dt a d).rational.2 ≠ 0

/-- **The LRT primitive normalized frontier, as a class.** The root-free analogue of
`PrimitiveFrontier`: it certifies the canonical normal input supplied to the LRT assembler. The more general
`LrtReducedProperFrontier` result contract derives this frontier without exposing a concrete Wf realization. -/
class PrimitiveFrontierLrt (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] : Prop where
  /-- Reduced-part soundness with algebraic residues: `cₙ/dₙ` integrates to `cIntegrateReducedLrt …`, whose
  log part carries symbolic algebraic residues. -/
  hreducedLrt : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
    IsIntegralResultLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d))
  /-- The rational denominator stored by the selected reduced LRT output is nonzero. -/
  hreducedDenNonzero : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
    toPoly (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)).rational.2 ≠ 0

/-- A proper reduced-result contract supplies the primitive normalized LRT frontier. -/
instance (priority := low) instPrimitiveFrontierLrtOfReduced [CPolyGcd DensePoly α]
    [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    [CPolySubresultant DensePoly] [LawfulCPolyGcd.{u, v} DensePoly α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] [LawfulCPolySplitFactor DensePoly α]
    [LrtReducedProperFrontier α] :
    PrimitiveFrontierLrt α where
  hreducedLrt := fun Dt a d hd0 hDt0 =>
    LrtReducedProperFrontier.sound Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (crNormDen_ne_zero_of_lawfulSplit Dt a d hd0) hDt0
      (crNormNum_degree_lt_crNormDen_of_lawfulSplit Dt a d hd0)
  hreducedDenNonzero := fun Dt a d hd0 hDt0 =>
    LrtReducedProperFrontier.rational_den_nonzero Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (crNormDen_ne_zero_of_lawfulSplit Dt a d hd0) hDt0

/-- **★ `hreducedLrt` closed from the genuine data.** Threading the assembled `of_genuine` soundness through
the canonical normalized input: if the genuine Rothstein–Trager residue-data + tower-nondegeneracy conditions
(`LrtReducedGenuineData`) hold for every reduced input, then the LRT primitive reduced frontier `hreducedLrt`
holds. This closes the frontier down to those necessary conditions, with no rational-residue restriction or
opaque soundness field. -/
theorem hreducedLrt_of_genuineAll [CFracGcdCoreWf α] [LawfulCPolyGcd.{u,v} DensePoly α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (hgen : ∀ (Dt a' d' : DensePoly α), toPoly d' ≠ 0 → LrtReducedGenuineData Dt a' d')
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hDt0 : (toPoly Dt).natDegree = 0) :
    IsIntegralResultLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)) := by
  letI : Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) := ⟨hgcd⟩
  -- apply `_of_genuine` directly at the canonical normal part, whose properness `deg crNormNum < deg crNormDen`
  -- (`crNormNum_degree_lt_crNormDen`) supplies the `haProper` input
  exact isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine hgcd Dt (crNormNum Dt a d) (crNormDen Dt a d)
    (crNormDen_ne_zero_of_charZero Dt a d hd0) hDt0
    (crNormNum_degree_lt_crNormDen Dt a d hd0)
    (hgen Dt (crNormNum Dt a d) (crNormDen Dt a d) (crNormDen_ne_zero_of_charZero Dt a d hd0))

/-- The concrete well-founded reduced-integrator proof supplies the representation-independent proper-result
contract. This is a provider boundary: consumers use `LrtReducedProperFrontier`, not the Wf gcd realization. -/
theorem lrtReducedProperFrontier_of_genuineAll [CFracGcdCoreWf α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (hgen : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → LrtReducedGenuineData Dt a d)
    (hden : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
      toPoly (cIntegrateReducedLrt Dt a d).rational.2 ≠ 0) :
    LrtReducedProperFrontier α where
  sound Dt a d hd0 hDt0 hproper :=
    isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine hgcd Dt a d hd0 hDt0 hproper
      (hgen Dt a d hd0)
  rational_den_nonzero := hden

-- The closure genuinely constructs the frontier: given the genuine data for every reduced input, a
-- `PrimitiveFrontierLrt` instance follows (hence the whole assembled root-free LRT solver).
example [CFracGcdCoreWf α] [LawfulCPolyGcd.{u,v} DensePoly α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))]
    (hgen : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → LrtReducedGenuineData Dt a d)
    (hden : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
      toPoly (cIntegrateReducedLrt Dt a d).rational.2 ≠ 0) :
    PrimitiveFrontierLrt α := by
  letI : LrtReducedProperFrontier α :=
    lrtReducedProperFrontier_of_genuineAll
      (Fact.out (p := CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))) hgen hden
  infer_instance

/-- **The frontier certifies broad elementary integrability of the reduced normal part.** From a
`PrimitiveFrontierLrt` instance, the canonical normal part `cₙ/dₙ` is elementary-integrable in the
algebraic-residue sense — the LRT analogue of the reduced-part payoff of `PrimitiveFrontier`. -/
theorem isElementaryIntegrableLrtG_crNorm_of_frontier [CharZero (CFieldSpec.K α)]
    [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [Algebra ℚ (CFieldSpec.K α)] [PrimitiveFrontierLrt α]
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hDt0 : (toPoly Dt).natDegree = 0) :
    IsElementaryIntegrableLrt Dt (crNormNum Dt a d) (crNormDen Dt a d) :=
  ⟨_, PrimitiveFrontierLrt.hreducedLrt Dt a d hd0 hDt0⟩

end DeepWiki.SymbolicIntegration
