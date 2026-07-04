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

end DeepWiki.SymbolicIntegration
