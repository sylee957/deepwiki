import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.IntegrationSpec

/-! # The abstract one-level Risch assembler (Stage-1)

The abstract soundness *core* of the one-level Risch integrator, proven purely over stage-result data —
**no concrete algorithm** (`cIntegrateCase`, `canonicalRepresentationFast`, `cIntegrateReduced`,
`cHermiteReduceTower`, …) appears in this file. The concrete assembler (the `cIntegrateCase` def, the
per-case `CMonomialCase` realizers, the reduced-stage realizations, and the end-to-end one-shots) lives in
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

/-- Special/normal rational-part combination executes on sparse polynomial results. -/
example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let nrm : IntegralResult ℚ CPoly.SparsePoly := ⟨(ofList [2], ofList [1]), []⟩
    CPoly.coeff (combineSN (ofList [3]) (ofList [1]) nrm).rational.1 0 = 5 := by
  native_decide

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
derivative, normal post-processing preserves certified integration results and nonzero denominators, and every
valid special antiderivative is found. -/
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
  /-- Relative completeness for special-part integration. -/
  special_complete : ∀ (Dt fp b ds snum sden : P α),
    CPoly.toPoly sden ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP snum sden)
      = fieldFracP fp CPoly.one + fieldFracP b ds →
      ∃ out, C.integrateSpecial Dt fp b ds = some out

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

namespace DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- The tower fraction-field element `⟦num/den⟧ = am(toPoly num) / am(toPoly den)`. -/
noncomputable abbrev fieldFrac (num den : DensePoly α) : RatFunc (CFieldSpec.K α) :=
  am α (toPoly num) / am α (toPoly den)

/-- **The abstract assembler soundness core (no concrete algorithm).** Purely from the abstract stage
results — a special-part fraction `snum/sden` differentiating to `specialVal`, a normal-part result `nrm`
that is an antiderivative of `cn/dn` (`hNrmField`), and the canonical reconstruction `specialVal + ⟦cn/dn⟧ =
⟦a/d⟧` (`hrecon`) — the combined result `combineSN snum sden nrm` is an antiderivative of `a/d`. This is the
soundness proven *against the interface data*; the concrete assembler (`IntegratorAssembly.lean`) is a
wrapper that supplies these from `canonicalRepresentationFast` / the reduced stage. -/
theorem combineSN_isIntegralResult (Dt a d cn dn snum sden : DensePoly α) (nrm : IntegralResult α)
    (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : toPoly sden ≠ 0) (hgden : toPoly nrm.rational.2 ≠ 0)
    (hSpecField : towerFractionFieldDeriv Dt (fieldFrac snum sden) = specialVal)
    (hNrmField : IsIntegralResult Dt cn dn nrm)
    (hrecon : specialVal + fieldFrac cn dn = fieldFrac a d) :
    IsIntegralResult Dt a d (combineSN snum sden nrm) := by
  have hgeneric := combineSN_isIntegralResultP (P := DensePoly) Dt a d cn dn snum sden nrm specialVal
    (by simpa only [toPoly_list_eq] using hsden)
    (by simpa only [toPoly_list_eq] using hgden)
    (by simpa only [fieldFracP, fieldFrac, towerFractionFieldDerivP,
      towerFractionFieldDeriv, toPoly_list_eq] using hSpecField)
    (by simpa only [IsIntegralResultP, IsIntegralResult, towerFractionFieldDerivP,
      towerFractionFieldDeriv, logResidueSumP, logResidueSum, toPoly_list_eq] using hNrmField)
    (by simpa only [fieldFracP, fieldFrac, toPoly_list_eq] using hrecon)
  simpa only [IsIntegralResultP, IsIntegralResult, towerFractionFieldDerivP,
    towerFractionFieldDeriv, logResidueSumP, logResidueSum, toPoly_list_eq] using hgeneric

/-! ## Elementary-integrability targets

Two existentials. `IsElementaryIntegrable` is the **formal** target — `∃` an `IntegralResult` satisfying the
formal log-derivative identity `IsIntegralResult`; it is too weak to be a completeness target (it holds
whenever the poles are rational over `K`, regardless of residue-constancy). `IsElementaryIntegrableGenuine`
is the **well-posed** target — the same but with all residues constant (`IsGenuineIntegralResult`), so its
negation is a meaningful non-integrability statement. The assembled solver's `sound` produces the genuine one;
the decidable completeness certificate lives in `LrtLiouvilleFrontier` (`LrtCompleteness.lean`). -/

/-- **`a/d` is formally elementary integrable over the tower**: there is an `IntegralResult` satisfying the
formal identity `IsIntegralResult`. Too weak to complete against (residues need not be constant); the genuine
target is `IsElementaryIntegrableGenuine`. -/
def IsElementaryIntegrable (Dt a d : DensePoly α) : Prop :=
  ∃ res : IntegralResult α, IsIntegralResult Dt a d res

/-- **The soundness→completeness bridge.** Any `IsIntegralResult` witness makes `a/d` elementary
integrable. So every concrete solver's soundness realization is, verbatim, a constructive-completeness
witness for `IsElementaryIntegrable`. -/
theorem IsElementaryIntegrable.of_isIntegralResult {Dt a d : DensePoly α} {res : IntegralResult α}
    (h : IsIntegralResult Dt a d res) : IsElementaryIntegrable Dt a d :=
  ⟨res, h⟩

/-- **Genuine elementary integrability**: an antiderivative in the Liouville form with **constant** residue
coefficients (`IsGenuineIntegralResult`). The well-posed completeness target: unlike `IsElementaryIntegrable`
(the formal ∃, which holds whenever the poles are rational over `K` regardless of residue-constancy), this
requires the residues to be genuine constants, so `¬IsElementaryIntegrableGenuine` is a meaningful
non-integrability statement. -/
def IsElementaryIntegrableGenuine (Dt a d : DensePoly α) : Prop :=
  ∃ res : IntegralResult α, IsGenuineIntegralResult Dt a d res

/-- Any genuine witness makes `a/d` genuinely elementary integrable. -/
theorem IsElementaryIntegrableGenuine.of_isGenuineIntegralResult {Dt a d : DensePoly α}
    {res : IntegralResult α} (h : IsGenuineIntegralResult Dt a d res) :
    IsElementaryIntegrableGenuine Dt a d :=
  ⟨res, h⟩

/-- Genuine integrability implies the formal `IsElementaryIntegrable` (drop the residue-constancy). -/
theorem IsElementaryIntegrableGenuine.toIsElementaryIntegrable {Dt a d : DensePoly α}
    (h : IsElementaryIntegrableGenuine Dt a d) : IsElementaryIntegrable Dt a d :=
  let ⟨res, hres⟩ := h; ⟨res, hres.1⟩

end DensePoly

end DeepWiki.SymbolicIntegration
