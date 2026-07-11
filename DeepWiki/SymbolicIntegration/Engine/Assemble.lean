import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.IntegrationSpec
import DeepWiki.SymbolicIntegration.Engine.NormalReduction

/-! # The abstract one-level Risch assembler (Stage-1)

The abstract soundness *core* of the one-level Risch integrator, proven purely over stage-result data —
**no concrete algorithm** (`canonicalRepresentationFast`, `cIntegrateReduced`, `cHermiteReduceTower`, …)
appears in this file. Dense canonical-split accessors and their reconstruction theorem live in
`IntegratorAssembly.lean`, which imports this file. See `docs/risch-two-stage-discipline.md`. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- The Prop-free per-monomial-case operations of one-level Risch integration over a polynomial
representation `P`: integrate the polynomial/special part and post-process the normal result. -/
structure CMonomialCase (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate the special/polynomial part `fₚ + b/dₛ` to a fraction `(snum, sden)`, or fail. -/
  integrateSpecial : P α → P α → P α → P α → Option (P α × P α)
  /-- Post-process a reduced normal result (identity for primitive; residual subtraction for hyperexponential). -/
  postprocessNormal : P α → IntegralResult α P → Option (IntegralResult α P)

/-- Representation-neutral output of canonical rational-function decomposition. -/
structure CanonicalRepresentationResult (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] where
  /-- Polynomial part. -/
  polynomial : P α
  /-- Numerator of the special-denominator part. -/
  specialNum : P α
  /-- Special denominator. -/
  specialDen : P α
  /-- Numerator of the normal-denominator part. -/
  normalNum : P α
  /-- Normal denominator. -/
  normalDen : P α

/-- Prop-free canonical-representation stage over a polynomial representation. -/
class CCanonicalRepresentation (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Decompose `a/d` into polynomial, special-denominator, and normal-denominator parts. -/
  compute : P α → P α → P α → CanonicalRepresentationResult P α

/-- Combine fractions `snum/sden + gnum/gden` in any polynomial representation. -/
def combineRationalParts {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (snum sden gnum gden : P α) : P α × P α :=
  (CPolyEngine.add (CPolyEngine.mul snum gden) (CPolyEngine.mul gnum sden),
    CPolyEngine.mul sden gden)

/-- Combine a special-part fraction with a corrected normal result in any polynomial representation. -/
def combineSN {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (snum sden : P α) (nrm : IntegralResult α P) : IntegralResult α P :=
  ⟨combineRationalParts snum sden nrm.rational.1 nrm.rational.2, nrm.logs⟩

/-! ### Representation-independent recombination -/

open CFrac Polynomial
open scoped Differential

/-- The tower fraction-field element represented by a polynomial numerator and denominator. -/
noncomputable abbrev fieldFracP {P : Type u → Type u} [CPoly P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (num den : P α) :
    RatFunc (CFieldSpec.K α) :=
  am α (CPoly.toPoly num) / am α (CPoly.toPoly den)

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Denotation-level contract for a `CMonomialCase`: successful special integration has the expected
derivative, while normal post-processing preserves certified integration results and nonzero denominators. -/
class LawfulCMonomialCase (C : CMonomialCase P α) : Prop where
  /-- A successful special integration has derivative `fₚ + b/dₛ`. -/
  special_sound : ∀ (Dt fp b ds snum sden : P α),
    C.integrateSpecial Dt fp b ds = some (snum, sden) →
      CPoly.toPoly sden ≠ 0 ∧
        towerFractionFieldDerivP Dt (fieldFracP snum sden)
          = fieldFracP fp CPoly.one + fieldFracP b ds
  /-- Normal-result post-processing preserves its integral-result certificate. -/
  postprocessNormal_sound : ∀ (Dt cn dn : P α) (before after : IntegralResult α P),
    IsIntegralResultP Dt cn dn before → C.postprocessNormal Dt before = some after →
      IsIntegralResultP Dt cn dn after
  /-- Normal-result post-processing preserves a nonzero rational denominator. -/
  postprocessNormal_den_nonzero : ∀ (Dt : P α) (before after : IntegralResult α P),
    CPoly.toPoly before.rational.2 ≠ 0 → C.postprocessNormal Dt before = some after →
      CPoly.toPoly after.rational.2 ≠ 0

/-- Semantic domain on which a monomial special solver is required to be complete. -/
abbrev MonomialSpecialDomain (P : Type u → Type u) (α : Type u) := P α → P α → P α → P α → Prop

/-- Relative completeness contract for a monomial-case special solver on a selected domain. -/
class CompleteCMonomialCase (C : CMonomialCase P α)
    (specialDomain : MonomialSpecialDomain P α) : Prop where
  /-- Every domain-admissible special antiderivative lies in the executable solver's domain. -/
  special_complete : ∀ (Dt fp b ds snum sden : P α),
    specialDomain Dt fp b ds →
    CPoly.toPoly sden ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP snum sden)
      = fieldFracP fp CPoly.one + fieldFracP b ds →
      ∃ out, C.integrateSpecial Dt fp b ds = some out
  /-- Every certified genuine normal result lies in the normal postprocessor's domain. -/
  postprocess_complete : ∀ (Dt cn dn : P α) (before : IntegralResult α P),
    CertifiedNormalResult Dt cn dn before →
      ∃ after, C.postprocessNormal Dt before = some after

/-- Denotation-level contract for canonical representation. -/
class LawfulCCanonicalRepresentation [CCanonicalRepresentation P α] : Prop where
  /-- Canonical decomposition reconstructs the input fraction. -/
  reconstruction : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    let out := CCanonicalRepresentation.compute Dt a d
    fieldFracP out.polynomial CPoly.one
        + fieldFracP out.specialNum out.specialDen
        + fieldFracP out.normalNum out.normalDen
      = fieldFracP a d
  /-- A nonzero input denominator produces a nonzero special denominator. -/
  specialDen_nonzero : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    CPoly.toPoly (CCanonicalRepresentation.compute Dt a d).specialDen ≠ 0
  /-- A nonzero input denominator produces a nonzero normal denominator. -/
  normalDen_nonzero : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    CPoly.toPoly (CCanonicalRepresentation.compute Dt a d).normalDen ≠ 0
  /-- The canonical normal fraction is proper. -/
  normal_proper : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    (CPoly.toPoly (CCanonicalRepresentation.compute Dt a d).normalNum).degree <
      (CPoly.toPoly (CCanonicalRepresentation.compute Dt a d).normalDen).degree
  /-- The canonical normal denominator is differential normal-squarefree. -/
  normal_isNormalSqfree : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly (CCanonicalRepresentation.compute Dt a d).normalDen)

/-- The selected canonical decomposition for `Dt`, `a`, and `d`. -/
abbrev canonicalResult [CCanonicalRepresentation P α] (Dt a d : P α) :
    CanonicalRepresentationResult P α :=
  CCanonicalRepresentation.compute Dt a d

/-- **Representation-independent assembler recombination.** A special fraction whose derivative is
`specialVal`, a normal result for `cn/dn`, and their reconstruction of `a/d` combine into an integral result.
This is the common soundness square consumed by every concrete one-level assembler. -/
theorem combineSN_isIntegralResultP (Dt a d cn dn snum sden : P α) (nrm : IntegralResult α P)
    (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : CPoly.toPoly sden ≠ 0) (hgden : CPoly.toPoly nrm.rational.2 ≠ 0)
    (hSpecField : towerFractionFieldDerivP Dt (fieldFracP snum sden) = specialVal)
    (hNrmField : IsIntegralResultP Dt cn dn nrm)
    (hrecon : specialVal + fieldFracP cn dn = fieldFracP a d) :
    IsIntegralResultP Dt a d (combineSN snum sden nrm) := by
  simp only [IsIntegralResultP] at hNrmField ⊢
  show towerFractionFieldDerivP Dt
      (am α (CPoly.toPoly (CPolyEngine.add (CPolyEngine.mul snum nrm.rational.2)
        (CPolyEngine.mul nrm.rational.1 sden))) /
        am α (CPoly.toPoly (CPolyEngine.mul sden nrm.rational.2)))
      + logResidueSumP Dt nrm.logs = _
  have hAsden : am α (CPoly.toPoly sden) ≠ 0 := am_ne_zero hsden
  have hAgden : am α (CPoly.toPoly nrm.rational.2) ≠ 0 := am_ne_zero hgden
  have hcombine : am α (CPoly.toPoly (CPolyEngine.add (CPolyEngine.mul snum nrm.rational.2)
        (CPolyEngine.mul nrm.rational.1 sden))) /
        am α (CPoly.toPoly (CPolyEngine.mul sden nrm.rational.2))
      = am α (CPoly.toPoly snum) / am α (CPoly.toPoly sden)
        + am α (CPoly.toPoly nrm.rational.1) / am α (CPoly.toPoly nrm.rational.2) := by
    rw [LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_mul,
      LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul]
    simp only [map_add, map_mul]
    field_simp
  rw [hcombine, map_add]
  rw [hSpecField, add_assoc, hNrmField]
  simpa only [fieldFracP] using hrecon

/-- **Generic one-level Risch assembly soundness.** A lawful canonical decomposition, a lawful monomial-case
special integration, and a certified normal result compose to an integral result of the original input. No
concrete polynomial representation or reduction implementation occurs in this theorem. -/
theorem assembleOneLevelP_sound (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [LawfulCMonomialCase C] [LawfulCCanonicalRepresentation (P := P) (α := α)]
    (Dt a d : P α) (before nrm : IntegralResult α P) (snum sden : P α)
    (hd : CPoly.toPoly d ≠ 0) (hbefore : IsIntegralResultP Dt
      (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen before)
    (hbeforeDen : CPoly.toPoly before.rational.2 ≠ 0)
    (hspecial : C.integrateSpecial Dt (canonicalResult Dt a d).polynomial
      (canonicalResult Dt a d).specialNum (canonicalResult Dt a d).specialDen = some (snum, sden))
    (hpost : C.postprocessNormal Dt before = some nrm) :
    IsIntegralResultP Dt a d (combineSN snum sden nrm) := by
  obtain ⟨hsden, hspecialField⟩ := LawfulCMonomialCase.special_sound (C := C) Dt
    (canonicalResult Dt a d).polynomial (canonicalResult Dt a d).specialNum
    (canonicalResult Dt a d).specialDen snum sden hspecial
  have hnrm := LawfulCMonomialCase.postprocessNormal_sound (C := C) Dt
    (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen before nrm hbefore hpost
  have hnrmDen := LawfulCMonomialCase.postprocessNormal_den_nonzero (C := C) Dt before nrm hbeforeDen hpost
  have hcanonical := LawfulCCanonicalRepresentation.reconstruction Dt a d hd
  refine combineSN_isIntegralResultP Dt a d (canonicalResult Dt a d).normalNum
    (canonicalResult Dt a d).normalDen snum sden nrm
    (fieldFracP (canonicalResult Dt a d).polynomial CPoly.one +
      fieldFracP (canonicalResult Dt a d).specialNum (canonicalResult Dt a d).specialDen)
    hsden hnrmDen hspecialField hnrm ?_
  simpa only [add_assoc] using hcanonical

end DeepWiki.SymbolicIntegration
