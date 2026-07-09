import DeepWiki.SymbolicIntegration.Engine.IntegratorCases.ReducedSound

/-! # Case-level soundness for concrete one-level Risch cases

Primitive and hyperexponential case soundness corollaries assembled from the
generic case assembler and reduced-stage soundness.
-/

namespace DeepWiki.SymbolicIntegration

open CPoly
open QFunNZ Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The hyperexp case, as a corollary of the generic soundness** (not the driver): the special value is
the polynomial part `⟦fpPart⟧`, `integrateSpecial`/`reducedCorrect` are the Laurent/normal solves. -/
theorem cIntegrateCase_hyperexp_sound (Dt a d : CPoly α)
    (cands : List α) (res : IntegralResult α) (lnum lden : CPoly α) (nrm : IntegralResult α)
    (fpPart : CPoly α) (hlden : toPoly lden ≠ 0) (hgden : toPoly nrm.rational.2 ≠ 0)
    (hLaur : cIntegrateHyperexpLaurent (cExpEta Dt) (crPoly Dt a d)
        (cHyperexpSpecialNeg (crSpecNum Dt a d) (crSpecDen Dt a d)) = some (lnum, lden))
    (hNrm : cIntegrateHyperexpNormal Dt (crNormNum Dt a d) (crNormDen Dt a d) cands = some nrm)
    (hsome : cIntegrateCase hyperexpCase Dt a d cands = some res)
    (hLaurField : towerFractionFieldDeriv Dt (fieldFrac lnum lden) = am α (toPoly fpPart))
    (hNrmField : IsIntegralResult Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm)
    (hrecon : am α (toPoly fpPart) + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d) :
    IsIntegralResult Dt a d res :=
  cIntegrateCase_sound hyperexpCase Dt a d cands res lnum lden nrm (am α (toPoly fpPart))
    hlden hgden hLaur hNrm hsome hLaurField hNrmField hrecon

/-- **The primitive case, as a corollary of the generic soundness.** The special part is the polynomial
`qₚ` (as `qₚ/1`) from the `b = 0` RDE; the reduced part needs no correction, so `nrm` is `redNorm`. -/
theorem cIntegrateCase_primitive_sound (Dt a d : CPoly α) (cands : List α) (res : IntegralResult α)
    (qp : CPoly α) (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : toPoly ([CField.one] : CPoly α) ≠ 0)
    (hgden : toPoly (redNorm Dt a d cands).rational.2 ≠ 0)
    (hb : cisZero (crSpecNum Dt a d) = true)
    (hqp : cPolyRischDE Dt [] (crPoly Dt a d) ((cdeg (crPoly Dt a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase Dt a d cands = some res)
    (hSpecField : towerFractionFieldDeriv Dt (fieldFrac qp [CField.one]) = specialVal)
    (hNrmField : IsIntegralResult Dt (crNormNum Dt a d) (crNormDen Dt a d) (redNorm Dt a d cands))
    (hrecon : specialVal + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d) :
    IsIntegralResult Dt a d res := by
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
    (a d : CPoly α) (cands : List α) (res : IntegralResult α) (qp : CPoly α)
    (hgden : toPoly (redNorm ([CField.one] : CPoly α) a d cands).rational.2 ≠ 0)
    (hb : cisZero (crSpecNum ([CField.one] : CPoly α) a d) = true)
    (hfp : cisZero (crPoly ([CField.one] : CPoly α) a d) = false)
    (hconst : Differential.mapCoeffs (toPoly (crPoly ([CField.one] : CPoly α) a d)) = 0)
    (hqp : cPolyRischDE ([CField.one] : CPoly α) [] (crPoly ([CField.one] : CPoly α) a d)
        ((cdeg (crPoly ([CField.one] : CPoly α) a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase ([CField.one] : CPoly α) a d cands = some res)
    (hNrmField : IsIntegralResult ([CField.one] : CPoly α) (crNormNum ([CField.one] : CPoly α) a d)
        (crNormDen ([CField.one] : CPoly α) a d) (redNorm ([CField.one] : CPoly α) a d cands))
    (hrecon : fieldFrac (crPoly ([CField.one] : CPoly α) a d) [CField.one]
          + fieldFrac (crNormNum ([CField.one] : CPoly α) a d) (crNormDen ([CField.one] : CPoly α) a d)
        = fieldFrac a d) :
    IsIntegralResult ([CField.one] : CPoly α) a d res := by
  have hone : toPoly ([CField.one] : CPoly α) = 1 := by
    simp only [denote]
    simp
  exact cIntegrateCase_primitive_sound ([CField.one] : CPoly α) a d cands res qp
    (fieldFrac (crPoly ([CField.one] : CPoly α) a d) [CField.one])
    (by rw [hone]; exact one_ne_zero) hgden hb hqp hsome
    (cPolyRischDEG_nil_field_identity (crPoly ([CField.one] : CPoly α) a d) qp _ hfp (le_refl _)
      hqp hconst)
    hNrmField hrecon

/-- **Primitive case with BOTH `hSpecField` and `hrecon` discharged** (canonical primitive `Dt = 1`,
`fₚ ≠ 0`, special part `b = 0`): the special-part identity comes from the poly-RDE soundness and the
reconstruction from `canonicalReconstruction` (the `b = 0` special term vanishes). The only remaining
inputs are the shared reduced identity (`hNrmField`) and the `cSplitFactorFast` split-correctness facts
(`hsplit`, coprimality) — the engine's split frontier. -/
theorem cIntegrateCase_primitive_sound_full [CharZero (CFieldSpec.K α)]
    (a d : CPoly α) (cands : List α) (res : IntegralResult α) (qp : CPoly α)
    (hgden : toPoly (redNorm ([CField.one] : CPoly α) a d cands).rational.2 ≠ 0)
    (hb : cisZero (crSpecNum ([CField.one] : CPoly α) a d) = true)
    (hfp : cisZero (crPoly ([CField.one] : CPoly α) a d) = false)
    (hconst : Differential.mapCoeffs (toPoly (crPoly ([CField.one] : CPoly α) a d)) = 0)
    (hqp : cPolyRischDE ([CField.one] : CPoly α) [] (crPoly ([CField.one] : CPoly α) a d)
        ((cdeg (crPoly ([CField.one] : CPoly α) a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase ([CField.one] : CPoly α) a d cands = some res)
    (hNrmField : IsIntegralResult ([CField.one] : CPoly α) (crNormNum ([CField.one] : CPoly α) a d)
        (crNormDen ([CField.one] : CPoly α) a d) (redNorm ([CField.one] : CPoly α) a d cands))
    (hd : toPoly d ≠ 0)
    (hdn : toPoly (crNormDen ([CField.one] : CPoly α) a d) ≠ 0)
    (hds : toPoly (crSpecDen ([CField.one] : CPoly α) a d) ≠ 0)
    (hsplit : toPoly d
      = toPoly (crSpecDen ([CField.one] : CPoly α) a d) * toPoly (crNormDen ([CField.one] : CPoly α) a d))
    (hgdeg : (toPoly (cgcdWf (crNormDen ([CField.one] : CPoly α) a d)
        (crSpecDen ([CField.one] : CPoly α) a d)).1).natDegree = 0)
    (hgne : toPoly (cgcdWf (crNormDen ([CField.one] : CPoly α) a d)
        (crSpecDen ([CField.one] : CPoly α) a d)).1 ≠ 0) :
    IsIntegralResult ([CField.one] : CPoly α) a d res := by
  have hspec0 : fieldFrac (crSpecNum ([CField.one] : CPoly α) a d)
      (crSpecDen ([CField.one] : CPoly α) a d) = 0 := by
    simp only [fieldFrac, (cisZeroG_iff (crSpecNum ([CField.one] : CPoly α) a d)).mp hb, map_zero,
      zero_div]
  have hrecon : fieldFrac (crPoly ([CField.one] : CPoly α) a d) [CField.one]
        + fieldFrac (crNormNum ([CField.one] : CPoly α) a d) (crNormDen ([CField.one] : CPoly α) a d)
      = fieldFrac a d := by
    have h := canonicalReconstruction ([CField.one] : CPoly α) a d hd hdn hds hsplit hgdeg hgne
    rw [hspec0, add_zero] at h
    exact h
  exact cIntegrateCase_primitive_sound_polyRDE a d cands res qp hgden hb hfp hconst hqp hsome hNrmField
    hrecon

end DeepWiki.SymbolicIntegration
