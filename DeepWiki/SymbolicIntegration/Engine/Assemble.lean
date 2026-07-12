import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.IntegrationSpec
import DeepWiki.SymbolicIntegration.Engine.NormalReduction
import DeepWiki.SymbolicIntegration.Engine.Tower.Stage

/-! # The abstract one-level Risch assembler (Stage-1)

The abstract soundness *core* of the one-level Risch integrator, proven purely over stage-result data —
**no concrete algorithm** (`canonicalRepresentationFast`, `cIntegrateReduced`, `cHermiteReduceTower`, …)
appears in this file. Dense canonical-split accessors and their reconstruction theorem live in
`CanonicalRepresentationDense.lean`, which imports this file. See `docs/risch-two-stage-discipline.md`. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- The Prop-free per-monomial-case operations of one-level Risch integration over a polynomial
representation `P`: integrate the polynomial/special part and post-process the normal result. -/
structure CMonomialCase (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate the special/polynomial part `fₚ + b/dₛ` to a rational-plus-log result, or fail. -/
  integrateSpecial : ℕ → P α → P α → P α → P α → Option (IntegralResult α P)
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

/-- Add two represented integral results, combining rational fractions and concatenating logarithms. -/
def combineIntegralResults {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (left right : IntegralResult α P) : IntegralResult α P :=
  ⟨combineRationalParts left.rational.1 left.rational.2 right.rational.1 right.rational.2,
    left.logs ++ right.logs⟩

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

/-- A semantic certificate for one monomial-special integration result. -/
def IsMonomialSpecialResult (Dt fp b ds : P α) (res : IntegralResult α P) : Prop :=
  CPoly.toPoly res.rational.2 ≠ 0 ∧
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
    (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0) ∧
    towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2) +
      logResidueSumP Dt res.logs = fieldFracP fp CPoly.one + fieldFracP b ds

/-- Denotation-level contract for a `CMonomialCase`: successful special integration has the expected
derivative, while normal post-processing preserves certified integration results and nonzero denominators. -/
class LawfulCMonomialCase (C : CMonomialCase P α) : Prop where
  /-- A successful special integration has derivative `fₚ + b/dₛ`. -/
  special_sound : ∀ (fuel : ℕ) (Dt fp b ds : P α) (res : IntegralResult α P),
    C.integrateSpecial fuel Dt fp b ds = some res →
      CPoly.toPoly res.rational.2 ≠ 0 ∧
        towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2)
            + logResidueSumP Dt res.logs =
          fieldFracP fp CPoly.one + fieldFracP b ds
  /-- Normal-result post-processing preserves its integral-result certificate. -/
  postprocessNormal_sound : ∀ (Dt cn dn : P α) (before after : IntegralResult α P),
    IsIntegralResultP Dt cn dn before → C.postprocessNormal Dt before = some after →
      IsIntegralResultP Dt cn dn after
  /-- Normal-result post-processing preserves a nonzero rational denominator. -/
  postprocessNormal_den_nonzero : ∀ (Dt : P α) (before after : IntegralResult α P),
    CPoly.toPoly before.rational.2 ≠ 0 → C.postprocessNormal Dt before = some after →
      CPoly.toPoly after.rational.2 ≠ 0

/-- A lawful monomial case whose special and postprocessed logarithms are genuine elementary terms. -/
class LawfulGenuineCMonomialCase (C : CMonomialCase P α)
    [LawfulCMonomialCase C] : Prop where
  /-- Every successful special result has constant logarithmic coefficients. -/
  special_coefficients_constant : ∀ (fuel : ℕ) (Dt fp b ds : P α)
      (res : IntegralResult α P),
    C.integrateSpecial fuel Dt fp b ds = some res →
      ∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0
  /-- Every successful special result has nonzero logarithm arguments. -/
  special_arguments_nonzero : ∀ (fuel : ℕ) (Dt fp b ds : P α)
      (res : IntegralResult α P),
    C.integrateSpecial fuel Dt fp b ds = some res →
      ∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0
  /-- Normal postprocessing preserves constant logarithmic coefficients. -/
  postprocessNormal_coefficients_constant : ∀ (Dt : P α)
      (before after : IntegralResult α P),
    (∀ cv ∈ before.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) →
    C.postprocessNormal Dt before = some after →
      ∀ cv ∈ after.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0
  /-- Normal postprocessing preserves nonzero logarithm arguments. -/
  postprocessNormal_arguments_nonzero : ∀ (Dt : P α)
      (before after : IntegralResult α P),
    (∀ cv ∈ before.logs, CPoly.toPoly cv.2 ≠ 0) →
    C.postprocessNormal Dt before = some after →
      ∀ cv ∈ after.logs, CPoly.toPoly cv.2 ≠ 0

omit [LawfulCPolyEngine P] in
/-- A lawful genuine special-stage run yields the common semantic result certificate. -/
theorem isMonomialSpecialResult_of_run (C : CMonomialCase P α)
    [LawfulCMonomialCase C] [LawfulGenuineCMonomialCase C]
    (fuel : ℕ) (Dt fp b ds : P α) (res : IntegralResult α P)
    (hrun : C.integrateSpecial fuel Dt fp b ds = some res) :
    IsMonomialSpecialResult Dt fp b ds res := by
  obtain ⟨hden, hidentity⟩ := LawfulCMonomialCase.special_sound fuel Dt fp b ds res hrun
  refine ⟨hden, ?_, ?_, hidentity⟩
  · exact LawfulGenuineCMonomialCase.special_coefficients_constant fuel Dt fp b ds res hrun
  · exact LawfulGenuineCMonomialCase.special_arguments_nonzero fuel Dt fp b ds res hrun

/-- Semantic domain on which a monomial special solver is required to be complete. -/
abbrev MonomialSpecialDomain (P : Type u → Type u) (α : Type u) := P α → P α → P α → P α → Prop

/-- Relative completeness contract for a monomial-case special solver on a selected domain. -/
class CompleteCMonomialCase (C : CMonomialCase P α)
    (specialDomain : MonomialSpecialDomain P α) : Prop where
  /-- Every domain-admissible special antiderivative lies in the executable solver's domain. -/
  special_complete : ∀ (Dt fp b ds : P α) (res : IntegralResult α P),
    specialDomain Dt fp b ds →
    CPoly.toPoly res.rational.2 ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2)
        + logResidueSumP Dt res.logs = fieldFracP fp CPoly.one + fieldFracP b ds →
      ∃ fuel out, C.integrateSpecial fuel Dt fp b ds = some out
  /-- Every certified genuine normal result lies in the normal postprocessor's domain. -/
  postprocess_complete : ∀ (Dt cn dn : P α) (before : IntegralResult α P),
    CertifiedNormalResult Dt cn dn before →
      ∃ after, C.postprocessNormal Dt before = some after

/-- The input supplied to a monomial-special remainder stage. -/
structure MonomialSpecialInput (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] [CFieldSpec α] where
  /-- The selected monomial derivative. -/
  derivative : P α
  /-- Polynomial contribution from polynomial reduction. -/
  polynomial : P α
  /-- Special-fraction numerator. -/
  specialNum : P α
  /-- Special-fraction denominator. -/
  specialDen : P α
  /-- The represented special denominator denotes a nonzero polynomial. -/
  specialDen_nonzero : CPoly.toPoly specialDen ≠ 0

/-- The representation-neutral completion stage exported by a certified monomial special solver. -/
noncomputable def CMonomialCase.asRemainderIntegrationStage
    (C : CMonomialCase P α) (domain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase C] [LawfulGenuineCMonomialCase C]
    [CompleteCMonomialCase C domain] :
    RemainderIntegrationStage (MonomialSpecialInput P α) (IntegralResult α P) Unit
      (fun input => ∃ result,
        IsMonomialSpecialResult input.derivative input.polynomial input.specialNum input.specialDen result)
      (fun input result _ =>
        IsMonomialSpecialResult input.derivative input.polynomial input.specialNum input.specialDen result) :=
  { stage :=
      { run := fun fuel input =>
          (C.integrateSpecial fuel input.derivative input.polynomial input.specialNum input.specialDen).map
            fun result => ⟨result, ()⟩
        domain := fun input => domain input.derivative input.polynomial input.specialNum input.specialDen
        sound := by
          intro fuel input result hdomain hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact isMonomialSpecialResult_of_run C fuel input.derivative input.polynomial
            input.specialNum input.specialDen out hout
        complete := by
          intro input hdomain hintegrable
          obtain ⟨result, hresult⟩ := hintegrable
          obtain ⟨hden, _hconstants, _hargs, hidentity⟩ := hresult
          obtain ⟨fuel, out, hrun⟩ := CompleteCMonomialCase.special_complete (C := C)
            input.derivative input.polynomial input.specialNum input.specialDen result hdomain
              hden hidentity
          exact ⟨fuel, ⟨out, ()⟩, by simp [hrun]⟩ } }

/-- A certified normal result packaged for the monomial-specific normal postprocessor. -/
structure NormalPostprocessInput (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] [CFieldSpec α] where
  /-- Original normal-reduction input. -/
  source : NormalReductionInput P α
  /-- Certified output of normal/Hermite reduction. -/
  normalResult : IntegralResult α P

/-- A normal-reduction result is handed off to normal postprocessing without changing its source fraction. -/
def IsNormalPostprocessHandoff (input : NormalReductionInput P α) (_ : Unit)
    (next : NormalPostprocessInput P α) : Prop :=
  CertifiedNormalResult input.derivative input.numerator input.denominator next.normalResult ∧
    next.source.derivative = input.derivative ∧ next.source.numerator = input.numerator ∧
      next.source.denominator = input.denominator

/-- Export normal/Hermite reduction with its certified result as the postprocessor's typed input. -/
noncomputable def CNormalReduction.asPostprocessHandoffStage
    (N : CNormalReduction P α) (domain : NormalReductionDomain P α)
    [LawfulCNormalReduction N domain] [LawfulGenuineCNormalReduction N domain]
    [CompleteCNormalReduction N domain] :
    RemainderIntegrationStage (NormalReductionInput P α) Unit (NormalPostprocessInput P α)
      (fun input => IsNormalPartIntegrable input.derivative input.numerator input.denominator)
      IsNormalPostprocessHandoff :=
  { stage :=
      { run := fun _ input =>
          (N.reduce input.derivative input.numerator input.denominator).map fun out =>
            ⟨(), ⟨input, out⟩⟩
        domain := fun input => domain input.derivative input.numerator input.denominator
        sound := by
          intro fuel input result hdomain hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          refine ⟨?_, rfl, rfl, rfl⟩
          exact ⟨LawfulCNormalReduction.sound input.derivative input.numerator input.denominator out
              hdomain input.denominator_nonzero hout,
            LawfulCNormalReduction.rationalDen_nonzero input.derivative input.numerator
              input.denominator out hdomain input.denominator_nonzero hout,
            LawfulGenuineCNormalReduction.coefficients_constant input.derivative input.numerator
              input.denominator out hdomain input.denominator_nonzero hout,
            LawfulGenuineCNormalReduction.arguments_nonzero input.derivative input.numerator
              input.denominator out hdomain input.denominator_nonzero hout⟩
        complete := by
          intro input hdomain hintegrable
          obtain ⟨out, hrun, _⟩ := CompleteCNormalReduction.relative_complete (N := N)
            input.derivative input.numerator input.denominator hdomain input.denominator_nonzero hintegrable
          exact ⟨0, ⟨(), ⟨input, out⟩⟩, by simp [hrun]⟩ } }

/-- Post-process a typed certified normal result as a remainder stage. -/
noncomputable def CMonomialCase.asNormalPostprocessRemainderStage
    (C : CMonomialCase P α) (specialDomain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase C] [LawfulGenuineCMonomialCase C]
    [CompleteCMonomialCase C specialDomain] :
    RemainderIntegrationStage (NormalPostprocessInput P α) (IntegralResult α P) Unit
      (fun _ => True)
      (fun input result _ =>
        CertifiedNormalResult input.source.derivative input.source.numerator input.source.denominator result) :=
  { stage :=
      { run := fun _ input =>
          (C.postprocessNormal input.source.derivative input.normalResult).map fun result => ⟨result, ()⟩
        domain := fun input =>
          CertifiedNormalResult input.source.derivative input.source.numerator input.source.denominator
            input.normalResult
        sound := by
          intro _ input result hcertified hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          refine ⟨LawfulCMonomialCase.postprocessNormal_sound input.source.derivative
              input.source.numerator input.source.denominator input.normalResult out hcertified.integral
              hout,
            LawfulCMonomialCase.postprocessNormal_den_nonzero input.source.derivative
              input.normalResult out hcertified.rationalDen_nonzero hout,
            LawfulGenuineCMonomialCase.postprocessNormal_coefficients_constant input.source.derivative
              input.normalResult out hcertified.coefficients_constant hout,
            LawfulGenuineCMonomialCase.postprocessNormal_arguments_nonzero input.source.derivative
              input.normalResult out hcertified.arguments_nonzero hout⟩
        complete := by
          intro input hcertified _
          obtain ⟨out, hout⟩ := CompleteCMonomialCase.postprocess_complete (C := C) specialDomain
            input.source.derivative input.source.numerator input.source.denominator input.normalResult
              hcertified
          exact ⟨0, ⟨out, ()⟩, by simp [hout]⟩ } }

/-- Compose normal/Hermite reduction and monomial-specific normal postprocessing. -/
noncomputable def CNormalReduction.asPostprocessedRemainderStage
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] [LawfulGenuineCNormalReduction N normalDomain]
    [CompleteCNormalReduction N normalDomain]
    (C : CMonomialCase P α) (specialDomain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase C] [LawfulGenuineCMonomialCase C]
    [CompleteCMonomialCase C specialDomain] :
    RemainderIntegrationStage (NormalReductionInput P α) (IntegralResult α P) Unit
      (fun input => IsNormalPartIntegrable input.derivative input.numerator input.denominator)
      (fun input result _ =>
        CertifiedNormalResult input.derivative input.numerator input.denominator result) := by
  let normal := N.asPostprocessHandoffStage normalDomain
  let postprocess := C.asNormalPostprocessRemainderStage specialDomain
  let composed :
      RemainderIntegrationStage (NormalReductionInput P α) (Unit × IntegralResult α P) Unit
        (fun input => IsNormalPartIntegrable input.derivative input.numerator input.denominator)
        (fun input output _ =>
          CertifiedNormalResult input.derivative input.numerator input.denominator output.2) :=
    normal.compose postprocess
    (fun input => normalDomain input.derivative input.numerator input.denominator)
    (fun input => IsNormalPartIntegrable input.derivative input.numerator input.denominator)
    (by
      intro input hdomain
      exact hdomain)
    (by
      intro input _ next _ hhandoff
      rcases hhandoff with ⟨hcertified, hderivative, hnum, hden⟩
      change CertifiedNormalResult next.source.derivative next.source.numerator
        next.source.denominator next.normalResult
      simpa [hderivative, hnum, hden] using hcertified)
    (by
      intro input hintegrable
      exact ⟨hintegrable, fun _ _ _ => True.intro⟩)
    (by
      intro input _ next result _ hhandoff hpostprocess
      rcases hhandoff with ⟨_, hderivative, hnum, hden⟩
      simpa [hderivative, hnum, hden] using hpostprocess)
  exact composed.mapOutput Prod.snd (by
    intro input _ _ hcorrect
    exact hcorrect)

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

omit [LawfulCPolyEngine P] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Logarithmic denotations turn list concatenation into addition. -/
theorem logResidueSumP_append (Dt : P α) (left right : List (α × P α)) :
    logResidueSumP Dt (left ++ right) = logResidueSumP Dt left + logResidueSumP Dt right := by
  simp only [logResidueSumP, List.map_append, List.sum_append]

/-- Adding a rational antiderivative to an integral result adds their denotational values. -/
theorem combineSN_value (Dt snum sden : P α) (nrm : IntegralResult α P)
    (rationalVal normalVal : RatFunc (CFieldSpec.K α))
    (hsden : CPoly.toPoly sden ≠ 0) (hnrmDen : CPoly.toPoly nrm.rational.2 ≠ 0)
    (hrational : towerFractionFieldDerivP Dt (fieldFracP snum sden) = rationalVal)
    (hnormal : towerFractionFieldDerivP Dt (fieldFracP nrm.rational.1 nrm.rational.2) +
      logResidueSumP Dt nrm.logs = normalVal) :
    towerFractionFieldDerivP Dt
        (fieldFracP (combineSN snum sden nrm).rational.1 (combineSN snum sden nrm).rational.2) +
      logResidueSumP Dt (combineSN snum sden nrm).logs = rationalVal + normalVal := by
  have hAsden : am α (CPoly.toPoly sden) ≠ 0 := am_ne_zero hsden
  have hAnrmDen : am α (CPoly.toPoly nrm.rational.2) ≠ 0 := am_ne_zero hnrmDen
  have hcombine : fieldFracP
      (CPolyEngine.add (CPolyEngine.mul snum nrm.rational.2)
        (CPolyEngine.mul nrm.rational.1 sden))
      (CPolyEngine.mul sden nrm.rational.2) =
      fieldFracP snum sden + fieldFracP nrm.rational.1 nrm.rational.2 := by
    simp only [fieldFracP, LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_mul,
      map_add, map_mul]
    field_simp
  simp only [combineSN, combineRationalParts]
  rw [hcombine, map_add, hrational]
  linear_combination hnormal

/-- Two certified partial results add to a certified result for the reconstructed input fraction. -/
theorem combineIntegralResults_isIntegralResultP (Dt a d cn dn : P α)
    (left right : IntegralResult α P) (leftVal : RatFunc (CFieldSpec.K α))
    (hleftDen : CPoly.toPoly left.rational.2 ≠ 0)
    (hrightDen : CPoly.toPoly right.rational.2 ≠ 0)
    (hleft : towerFractionFieldDerivP Dt (fieldFracP left.rational.1 left.rational.2)
        + logResidueSumP Dt left.logs = leftVal)
    (hright : IsIntegralResultP Dt cn dn right)
    (hrecon : leftVal + fieldFracP cn dn = fieldFracP a d) :
    IsIntegralResultP Dt a d (combineIntegralResults left right) := by
  have hAleft : am α (CPoly.toPoly left.rational.2) ≠ 0 := am_ne_zero hleftDen
  have hAright : am α (CPoly.toPoly right.rational.2) ≠ 0 := am_ne_zero hrightDen
  have hcombine : fieldFracP
      (CPolyEngine.add (CPolyEngine.mul left.rational.1 right.rational.2)
        (CPolyEngine.mul right.rational.1 left.rational.2))
      (CPolyEngine.mul left.rational.2 right.rational.2) =
      fieldFracP left.rational.1 left.rational.2 +
        fieldFracP right.rational.1 right.rational.2 := by
    simp only [fieldFracP, LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_mul,
      map_add, map_mul]
    field_simp
  change towerFractionFieldDerivP Dt
      (fieldFracP
        (CPolyEngine.add (CPolyEngine.mul left.rational.1 right.rational.2)
          (CPolyEngine.mul right.rational.1 left.rational.2))
        (CPolyEngine.mul left.rational.2 right.rational.2)) +
      logResidueSumP Dt (left.logs ++ right.logs) = fieldFracP a d
  rw [hcombine, map_add, logResidueSumP_append]
  simp only [IsIntegralResultP] at hright
  calc
    (towerFractionFieldDerivP Dt (fieldFracP left.rational.1 left.rational.2) +
          towerFractionFieldDerivP Dt (fieldFracP right.rational.1 right.rational.2)) +
        (logResidueSumP Dt left.logs + logResidueSumP Dt right.logs) =
        (towerFractionFieldDerivP Dt (fieldFracP left.rational.1 left.rational.2) +
          logResidueSumP Dt left.logs) +
          (towerFractionFieldDerivP Dt (fieldFracP right.rational.1 right.rational.2) +
            logResidueSumP Dt right.logs) := by ring
    _ = leftVal + fieldFracP cn dn := by rw [hleft, hright]
    _ = fieldFracP a d := hrecon

end DeepWiki.SymbolicIntegration
