import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Computable.IntegrationSpec

/-! # The abstract one-level Risch assembler (Stage-1)

The abstract soundness *core* of the one-level Risch integrator, proven purely over stage-result data —
**no concrete algorithm** (`cIntegrateCase`, `canonicalRepresentationFastGWf`, `cIntegrateReducedGWf`,
`cHermiteReduceTowerGWf`, …) appears in this file. The concrete assembler (the `cIntegrateCase` def, the
per-case `MonomialCase` instances, the reduced-stage realizations, and the end-to-end one-shots) lives in
`IntegratorAssembly.lean`, which imports this file. See `docs/risch-two-stage-discipline.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- The per-monomial-case hooks of one-level Risch integration: `integrateSpecial Dt fp b ds` handles the
polynomial/special part as a fraction, `reducedCorrect Dt` post-processes the reduced normal part. -/
structure MonomialCase (α : Type*) [CField α] [CDiffField α] where
  /-- Integrate the special/polynomial part `fₚ + b/dₛ` to a fraction `(snum, sden)`, or `none`. -/
  integrateSpecial : CPolyG α → CPolyG α → CPolyG α → CPolyG α → Option (CPolyG α × CPolyG α)
  /-- Post-process the reduced normal result (identity for primitive; residual subtraction for hyperexp). -/
  reducedCorrect : CPolyG α → IntegralResultG α → Option (IntegralResultG α)

/-- Combine a special-part fraction `snum/sden` with the corrected normal result `nrm = gnum/gden + logs`:
`(snum·gden + gnum·sden)/(sden·gden) + logs`. -/
def combineSN (snum sden : CPolyG α) (nrm : IntegralResultG α) : IntegralResultG α :=
  let gnum := nrm.rational.1
  let gden := nrm.rational.2
  ⟨(caddG (cmulG snum gden) (cmulG gnum sden), cmulG sden gden), nrm.logs⟩

end CPolyG

open CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- The tower fraction-field element `⟦num/den⟧ = amG(toPolyG num) / amG(toPolyG den)`. -/
noncomputable abbrev fieldFrac (num den : CPolyG α) : RatFunc (CFieldSpec.K α) :=
  amG α (toPolyG num) / amG α (toPolyG den)

/-- **The abstract assembler soundness core (no concrete algorithm).** Purely from the abstract stage
results — a special-part fraction `snum/sden` differentiating to `specialVal`, a normal-part result `nrm`
that is an antiderivative of `cn/dn` (`hNrmField`), and the canonical reconstruction `specialVal + ⟦cn/dn⟧ =
⟦a/d⟧` (`hrecon`) — the combined result `combineSN snum sden nrm` is an antiderivative of `a/d`. This is the
soundness proven *against the interface data*; the concrete assembler (`IntegratorAssembly.lean`) is a
wrapper that supplies these from `canonicalRepresentationFastGWf` / the reduced stage. -/
theorem combineSN_isIntegralResult (Dt a d cn dn snum sden : CPolyG α) (nrm : IntegralResultG α)
    (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : toPolyG sden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hSpecField : towerFractionFieldDerivG Dt (fieldFrac snum sden) = specialVal)
    (hNrmField : IsIntegralResultG Dt cn dn nrm)
    (hrecon : specialVal + fieldFrac cn dn = fieldFrac a d) :
    IsIntegralResultG Dt a d (combineSN snum sden nrm) := by
  simp only [IsIntegralResultG] at hNrmField ⊢
  show towerFractionFieldDerivG Dt
      (amG α (toPolyG (caddG (cmulG snum nrm.rational.2) (cmulG nrm.rational.1 sden)))
        / amG α (toPolyG (cmulG sden nrm.rational.2))) + logResidueSumG Dt nrm.logs = _
  have hAsden : amG α (toPolyG sden) ≠ 0 := amG_toPolyG_ne_zero hsden
  have hAgden : amG α (toPolyG nrm.rational.2) ≠ 0 := amG_toPolyG_ne_zero hgden
  have hcombine : amG α (toPolyG (caddG (cmulG snum nrm.rational.2) (cmulG nrm.rational.1 sden)))
        / amG α (toPolyG (cmulG sden nrm.rational.2))
      = amG α (toPolyG snum) / amG α (toPolyG sden)
        + amG α (toPolyG nrm.rational.1) / amG α (toPolyG nrm.rational.2) := by
    rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, map_add, map_mul, map_mul, map_mul]
    field_simp
  rw [hcombine, map_add]
  simp only [fieldFrac] at hSpecField
  rw [hSpecField, add_assoc, hNrmField]
  simpa only [fieldFrac] using hrecon

/-! ## Abstract completeness (Stage-1)

The completeness *target*, parallel to soundness. At one Risch level, "`a/d` has an elementary integral over
the tower" is exactly "there is an `IntegralResultG`" — a rational part plus `Σ cᵢ·log vᵢ` with constant
`cᵢ`, which is the Liouville form. So `IsElementaryIntegrableG` is defined by that existential, and the
constructive direction is a corollary of the soundness core. The frontier direction (the algorithm's
failure certifies non-elementarity) is stated abstractly via a *descent* law — the Liouville / residue-
criterion / RDE-completeness content — taken as the interface contract, exactly as `hSpecField`/`hNrmField`
were for soundness. No concrete algorithm. -/

/-- **`a/d` is elementary integrable over the tower**: there is an antiderivative in the Liouville form
`⟦rational⟧ + Σ cᵢ·log vᵢ` (an `IntegralResultG`). The completeness target. -/
def IsElementaryIntegrableG (Dt a d : CPolyG α) : Prop :=
  ∃ res : IntegralResultG α, IsIntegralResultG Dt a d res

/-- **The soundness→completeness bridge.** Any `IsIntegralResultG` witness makes `a/d` elementary
integrable. So every concrete solver's soundness realization is, verbatim, a constructive-completeness
witness for `IsElementaryIntegrableG`. -/
theorem IsElementaryIntegrableG.of_isIntegralResult {Dt a d : CPolyG α} {res : IntegralResultG α}
    (h : IsIntegralResultG Dt a d res) : IsElementaryIntegrableG Dt a d :=
  ⟨res, h⟩

/-- **Genuine elementary integrability**: an antiderivative in the Liouville form with **constant** residue
coefficients (`IsGenuineIntegralResultG`). The well-posed completeness target: unlike `IsElementaryIntegrableG`
(the formal ∃, which holds whenever the poles are rational over `K` regardless of residue-constancy), this
requires the residues to be genuine constants, so `¬IsElementaryIntegrableGenuineG` is a meaningful
non-integrability statement. -/
def IsElementaryIntegrableGenuineG (Dt a d : CPolyG α) : Prop :=
  ∃ res : IntegralResultG α, IsGenuineIntegralResultG Dt a d res

/-- Any genuine witness makes `a/d` genuinely elementary integrable. -/
theorem IsElementaryIntegrableGenuineG.of_isGenuineIntegralResult {Dt a d : CPolyG α}
    {res : IntegralResultG α} (h : IsGenuineIntegralResultG Dt a d res) :
    IsElementaryIntegrableGenuineG Dt a d :=
  ⟨res, h⟩

/-- Genuine integrability implies the formal `IsElementaryIntegrableG` (drop the residue-constancy). -/
theorem IsElementaryIntegrableGenuineG.toIsElementaryIntegrableG {Dt a d : CPolyG α}
    (h : IsElementaryIntegrableGenuineG Dt a d) : IsElementaryIntegrableG Dt a d :=
  let ⟨res, hres⟩ := h; ⟨res, hres.1⟩

/-- **Constructive completeness (soundness core, restated).** If the stages certify a special fraction
and a normal-part result reconstructing `a/d`, then `a/d` is elementary integrable. The easy direction —
a corollary of `combineSN_isIntegralResult`. -/
theorem isElementaryIntegrableG_of_stages (Dt a d cn dn snum sden : CPolyG α)
    (nrm : IntegralResultG α) (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : toPolyG sden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hSpecField : towerFractionFieldDerivG Dt (fieldFrac snum sden) = specialVal)
    (hNrmField : IsIntegralResultG Dt cn dn nrm)
    (hrecon : specialVal + fieldFrac cn dn = fieldFrac a d) :
    IsElementaryIntegrableG Dt a d :=
  ⟨combineSN snum sden nrm,
    combineSN_isIntegralResult Dt a d cn dn snum sden nrm specialVal hsden hgden hSpecField hNrmField
      hrecon⟩

/-- **Abstract assembler completeness (the frontier direction).** If elementary-integrability of `a/d`
descends to both a special-part and a normal-part obligation (`hDescend` — the Liouville / canonical-split
content), then a certified non-elementary obstruction in either part (`hobstruct`) makes `a/d` non-elementary.
The dual of `isElementaryIntegrableG_of_stages`: the deep `hDescend` law is the completeness frontier
(residue criterion, RDE completeness, Liouville descent), the interface contract. -/
theorem not_isElementaryIntegrableG_of_obstruction (Dt a d : CPolyG α) {SpecElem NrmElem : Prop}
    (hDescend : IsElementaryIntegrableG Dt a d → SpecElem ∧ NrmElem)
    (hobstruct : ¬ SpecElem ∨ ¬ NrmElem) :
    ¬ IsElementaryIntegrableG Dt a d :=
  fun h => hobstruct.elim (fun hns => hns (hDescend h).1) (fun hnn => hnn (hDescend h).2)

end DeepWiki.SymbolicIntegration
