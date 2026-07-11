import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.IntegrationSpec

/-! # The abstract one-level Risch assembler (Stage-1)

The abstract soundness *core* of the one-level Risch integrator, proven purely over stage-result data —
**no concrete algorithm** (`cIntegrateCase`, `canonicalRepresentationFast`, `cIntegrateReduced`,
`cHermiteReduceTower`, …) appears in this file. The concrete assembler (the `cIntegrateCase` def, the
per-case `MonomialCase` instances, the reduced-stage realizations, and the end-to-end one-shots) lives in
`IntegratorAssembly.lean`, which imports this file. See `docs/risch-two-stage-discipline.md`. -/

namespace DeepWiki.SymbolicIntegration

universe u

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α]

/-- The per-monomial-case hooks of one-level Risch integration: `integrateSpecial Dt fp b ds` handles the
polynomial/special part as a fraction, `reducedCorrect Dt` post-processes the reduced normal part. -/
structure MonomialCase (α : Type*) [CField α] [CDiffField α] where
  /-- Integrate the special/polynomial part `fₚ + b/dₛ` to a fraction `(snum, sden)`, or `none`. -/
  integrateSpecial : DensePoly α → DensePoly α → DensePoly α → DensePoly α → Option (DensePoly α × DensePoly α)
  /-- Post-process the reduced normal result (identity for primitive; residual subtraction for hyperexp). -/
  reducedCorrect : DensePoly α → IntegralResult α → Option (IntegralResult α)

end DensePoly

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

open DensePoly CFrac Polynomial
open scoped Differential

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
  simp only [IsIntegralResult] at hNrmField ⊢
  show towerFractionFieldDeriv Dt
      (am α (toPoly (cadd (cmul snum nrm.rational.2) (cmul nrm.rational.1 sden)))
        / am α (toPoly (cmul sden nrm.rational.2))) + logResidueSum Dt nrm.logs = _
  have hAsden : am α (toPoly sden) ≠ 0 := am_ne_zero hsden
  have hAgden : am α (toPoly nrm.rational.2) ≠ 0 := am_ne_zero hgden
  have hcombine : am α (toPoly (cadd (cmul snum nrm.rational.2) (cmul nrm.rational.1 sden)))
        / am α (toPoly (cmul sden nrm.rational.2))
      = am α (toPoly snum) / am α (toPoly sden)
        + am α (toPoly nrm.rational.1) / am α (toPoly nrm.rational.2) := by
    -- front-load transport (denotation + `am` homomorphism) to a pure fraction-field goal, then math
    simp only [denote, map_add, map_mul]
    field_simp
  rw [hcombine, map_add]
  simp only [fieldFrac] at hSpecField
  rw [hSpecField, add_assoc, hNrmField]
  simpa only [fieldFrac] using hrecon

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

end DeepWiki.SymbolicIntegration
