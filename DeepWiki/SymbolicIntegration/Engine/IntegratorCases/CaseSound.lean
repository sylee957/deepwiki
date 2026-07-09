import DeepWiki.SymbolicIntegration.Engine.IntegratorCases.ReducedSound

/-! # Case-level soundness for concrete one-level Risch cases

Primitive and hyperexponential case soundness corollaries assembled from the
generic case assembler and reduced-stage soundness.
-/

namespace DeepWiki.SymbolicIntegration

open Compute
open CPolyG
open QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The hyperexp case, as a corollary of the generic soundness** (not the driver): the special value is
the polynomial part `⟦fpPart⟧`, `integrateSpecial`/`reducedCorrect` are the Laurent/normal solves. -/
theorem cIntegrateCase_hyperexp_sound (Dt a d : CPolyG α)
    (cands : List α) (res : IntegralResultG α) (lnum lden : CPolyG α) (nrm : IntegralResultG α)
    (fpPart : CPolyG α) (hlden : toPolyG lden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hLaur : cIntegrateHyperexpLaurentG (cExpEtaG Dt) (crPoly Dt a d)
        (cHyperexpSpecialNegG (crSpecNum Dt a d) (crSpecDen Dt a d)) = some (lnum, lden))
    (hNrm : cIntegrateHyperexpNormalG Dt (crNormNum Dt a d) (crNormDen Dt a d) cands = some nrm)
    (hsome : cIntegrateCase hyperexpCase Dt a d cands = some res)
    (hLaurField : towerFractionFieldDerivG Dt (fieldFrac lnum lden) = amG α (toPolyG fpPart))
    (hNrmField : IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm)
    (hrecon : amG α (toPolyG fpPart) + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d) :
    IsIntegralResultG Dt a d res :=
  cIntegrateCase_sound hyperexpCase Dt a d cands res lnum lden nrm (amG α (toPolyG fpPart))
    hlden hgden hLaur hNrm hsome hLaurField hNrmField hrecon

/-- **The primitive case, as a corollary of the generic soundness.** The special part is the polynomial
`qₚ` (as `qₚ/1`) from the `b = 0` RDE; the reduced part needs no correction, so `nrm` is `redNorm`. -/
theorem cIntegrateCase_primitive_sound (Dt a d : CPolyG α) (cands : List α) (res : IntegralResultG α)
    (qp : CPolyG α) (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : toPolyG ([CField.one] : CPolyG α) ≠ 0)
    (hgden : toPolyG (redNorm Dt a d cands).rational.2 ≠ 0)
    (hb : cisZeroG (crSpecNum Dt a d) = true)
    (hqp : cPolyRischDEG Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase Dt a d cands = some res)
    (hSpecField : towerFractionFieldDerivG Dt (fieldFrac qp [CField.one]) = specialVal)
    (hNrmField : IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) (redNorm Dt a d cands))
    (hrecon : specialVal + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d) :
    IsIntegralResultG Dt a d res := by
  have hSpec : primitiveCase.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d)
      = some (qp, [CField.one]) := by
    simp only [primitiveCase, hb, if_true, hqp]
  exact cIntegrateCase_sound primitiveCase Dt a d cands res qp [CField.one] (redNorm Dt a d cands)
    specialVal hsden hgden hSpec rfl hsome hSpecField hNrmField hrecon

/-- **Primitive case with the special-part identity discharged** (canonical primitive `Dt = 1`, `fₚ ≠ 0`):
`hSpecField` is no longer a hypothesis — it follows from `cPolyRischDEG_nil_field_identity` (the engine's
own poly-RDE soundness), leaving only the shared reduced identity (`hNrmField`) and reconstruction
(`hrecon`). One step closer to unconditional. -/
theorem cIntegrateCase_primitive_sound_polyRDE [CharZero (CFieldSpec.K α)]
    (a d : CPolyG α) (cands : List α) (res : IntegralResultG α) (qp : CPolyG α)
    (hgden : toPolyG (redNorm ([CField.one] : CPolyG α) a d cands).rational.2 ≠ 0)
    (hb : cisZeroG (crSpecNum ([CField.one] : CPolyG α) a d) = true)
    (hfp : cisZeroG (crPoly ([CField.one] : CPolyG α) a d) = false)
    (hconst : Differential.mapCoeffs (toPolyG (crPoly ([CField.one] : CPolyG α) a d)) = 0)
    (hqp : cPolyRischDEG ([CField.one] : CPolyG α) [] (crPoly ([CField.one] : CPolyG α) a d)
        ((cdegG (crPoly ([CField.one] : CPolyG α) a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase ([CField.one] : CPolyG α) a d cands = some res)
    (hNrmField : IsIntegralResultG ([CField.one] : CPolyG α) (crNormNum ([CField.one] : CPolyG α) a d)
        (crNormDen ([CField.one] : CPolyG α) a d) (redNorm ([CField.one] : CPolyG α) a d cands))
    (hrecon : fieldFrac (crPoly ([CField.one] : CPolyG α) a d) [CField.one]
          + fieldFrac (crNormNum ([CField.one] : CPolyG α) a d) (crNormDen ([CField.one] : CPolyG α) a d)
        = fieldFrac a d) :
    IsIntegralResultG ([CField.one] : CPolyG α) a d res := by
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    simp only [denote]
    simp
  exact cIntegrateCase_primitive_sound ([CField.one] : CPolyG α) a d cands res qp
    (fieldFrac (crPoly ([CField.one] : CPolyG α) a d) [CField.one])
    (by rw [hone]; exact one_ne_zero) hgden hb hqp hsome
    (cPolyRischDEG_nil_field_identity (crPoly ([CField.one] : CPolyG α) a d) qp _ hfp (le_refl _)
      hqp hconst)
    hNrmField hrecon

/-- **Primitive case with BOTH `hSpecField` and `hrecon` discharged** (canonical primitive `Dt = 1`,
`fₚ ≠ 0`, special part `b = 0`): the special-part identity comes from the poly-RDE soundness and the
reconstruction from `canonicalReconstruction` (the `b = 0` special term vanishes). The only remaining
inputs are the shared reduced identity (`hNrmField`) and the `cSplitFactorFastG` split-correctness facts
(`hsplit`, coprimality) — the engine's split frontier. -/
theorem cIntegrateCase_primitive_sound_full [CharZero (CFieldSpec.K α)]
    (a d : CPolyG α) (cands : List α) (res : IntegralResultG α) (qp : CPolyG α)
    (hgden : toPolyG (redNorm ([CField.one] : CPolyG α) a d cands).rational.2 ≠ 0)
    (hb : cisZeroG (crSpecNum ([CField.one] : CPolyG α) a d) = true)
    (hfp : cisZeroG (crPoly ([CField.one] : CPolyG α) a d) = false)
    (hconst : Differential.mapCoeffs (toPolyG (crPoly ([CField.one] : CPolyG α) a d)) = 0)
    (hqp : cPolyRischDEG ([CField.one] : CPolyG α) [] (crPoly ([CField.one] : CPolyG α) a d)
        ((cdegG (crPoly ([CField.one] : CPolyG α) a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase ([CField.one] : CPolyG α) a d cands = some res)
    (hNrmField : IsIntegralResultG ([CField.one] : CPolyG α) (crNormNum ([CField.one] : CPolyG α) a d)
        (crNormDen ([CField.one] : CPolyG α) a d) (redNorm ([CField.one] : CPolyG α) a d cands))
    (hd : toPolyG d ≠ 0)
    (hdn : toPolyG (crNormDen ([CField.one] : CPolyG α) a d) ≠ 0)
    (hds : toPolyG (crSpecDen ([CField.one] : CPolyG α) a d) ≠ 0)
    (hsplit : toPolyG d
      = toPolyG (crSpecDen ([CField.one] : CPolyG α) a d) * toPolyG (crNormDen ([CField.one] : CPolyG α) a d))
    (hgdeg : (toPolyG (cgcdWf (crNormDen ([CField.one] : CPolyG α) a d)
        (crSpecDen ([CField.one] : CPolyG α) a d)).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (crNormDen ([CField.one] : CPolyG α) a d)
        (crSpecDen ([CField.one] : CPolyG α) a d)).1 ≠ 0) :
    IsIntegralResultG ([CField.one] : CPolyG α) a d res := by
  have hspec0 : fieldFrac (crSpecNum ([CField.one] : CPolyG α) a d)
      (crSpecDen ([CField.one] : CPolyG α) a d) = 0 := by
    simp only [fieldFrac, (cisZeroG_iff (crSpecNum ([CField.one] : CPolyG α) a d)).mp hb, map_zero,
      zero_div]
  have hrecon : fieldFrac (crPoly ([CField.one] : CPolyG α) a d) [CField.one]
        + fieldFrac (crNormNum ([CField.one] : CPolyG α) a d) (crNormDen ([CField.one] : CPolyG α) a d)
      = fieldFrac a d := by
    have h := canonicalReconstruction ([CField.one] : CPolyG α) a d hd hdn hds hsplit hgdeg hgne
    rw [hspec0, add_zero] at h
    exact h
  exact cIntegrateCase_primitive_sound_polyRDE a d cands res qp hgden hb hfp hconst hqp hsome hNrmField
    hrecon

end DeepWiki.SymbolicIntegration
