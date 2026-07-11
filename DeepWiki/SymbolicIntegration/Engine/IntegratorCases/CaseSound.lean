import DeepWiki.SymbolicIntegration.Engine.IntegratorCases.ReducedSound

/-! # Case-level soundness for concrete one-level Risch cases

Primitive and hyperexponential case soundness corollaries assembled from the
generic case assembler and reduced-stage soundness.
-/

namespace DeepWiki.SymbolicIntegration

open DensePoly
open CFrac Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
  [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **The hyperexp case, as a corollary of the generic soundness** (not the driver): the special value is
the polynomial part `⟦fpPart⟧`, `integrateSpecial`/`reducedCorrect` are the Laurent/normal solves. -/
theorem cIntegrateCase_hyperexp_sound (Dt a d : DensePoly α)
    (cands : List α) (res : IntegralResult α) (lnum lden : DensePoly α) (nrm : IntegralResult α)
    (fpPart : DensePoly α) (hlden : toPoly lden ≠ 0) (hgden : toPoly nrm.rational.2 ≠ 0)
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
theorem cIntegrateCase_primitive_sound (Dt a d : DensePoly α) (cands : List α) (res : IntegralResult α)
    (qp : DensePoly α) (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : toPoly ([CCommRing.one] : DensePoly α) ≠ 0)
    (hgden : toPoly (redNorm Dt a d cands).rational.2 ≠ 0)
    (hb : cisZero (crSpecNum Dt a d) = true)
    (hqp : cPolyRischDE Dt [] (crPoly Dt a d) ((cdeg (crPoly Dt a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase Dt a d cands = some res)
    (hSpecField : towerFractionFieldDeriv Dt (fieldFrac qp [CCommRing.one]) = specialVal)
    (hNrmField : IsIntegralResult Dt (crNormNum Dt a d) (crNormDen Dt a d) (redNorm Dt a d cands))
    (hrecon : specialVal + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d) :
    IsIntegralResult Dt a d res := by
  have hSpec : primitiveCase.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d)
      = some (qp, [CCommRing.one]) := by
    simp only [primitiveCase, hb, if_true, hqp]
  exact cIntegrateCase_sound primitiveCase Dt a d cands res qp [CCommRing.one] (redNorm Dt a d cands)
    specialVal hsden hgden hSpec rfl hsome hSpecField hNrmField hrecon

/-- **Primitive case with the special-part identity discharged** (canonical primitive `Dt = 1`, `fₚ ≠ 0`):
`hSpecField` is no longer a hypothesis — it follows from `cPolyRischDEG_nil_field_identity` (the engine's
own poly-RDE soundness), leaving only the shared reduced identity (`hNrmField`) and reconstruction
(`hrecon`). One step closer to unconditional. -/
theorem cIntegrateCase_primitive_sound_polyRDE [CharZero (CFieldSpec.K α)]
    (a d : DensePoly α) (cands : List α) (res : IntegralResult α) (qp : DensePoly α)
    (hgden : toPoly (redNorm ([CCommRing.one] : DensePoly α) a d cands).rational.2 ≠ 0)
    (hb : cisZero (crSpecNum ([CCommRing.one] : DensePoly α) a d) = true)
    (hfp : cisZero (crPoly ([CCommRing.one] : DensePoly α) a d) = false)
    (hconst : Differential.mapCoeffs (toPoly (crPoly ([CCommRing.one] : DensePoly α) a d)) = 0)
    (hqp : cPolyRischDE ([CCommRing.one] : DensePoly α) [] (crPoly ([CCommRing.one] : DensePoly α) a d)
        ((cdeg (crPoly ([CCommRing.one] : DensePoly α) a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase ([CCommRing.one] : DensePoly α) a d cands = some res)
    (hNrmField : IsIntegralResult ([CCommRing.one] : DensePoly α) (crNormNum ([CCommRing.one] : DensePoly α) a d)
        (crNormDen ([CCommRing.one] : DensePoly α) a d) (redNorm ([CCommRing.one] : DensePoly α) a d cands))
    (hrecon : fieldFrac (crPoly ([CCommRing.one] : DensePoly α) a d) [CCommRing.one]
          + fieldFrac (crNormNum ([CCommRing.one] : DensePoly α) a d) (crNormDen ([CCommRing.one] : DensePoly α) a d)
        = fieldFrac a d) :
    IsIntegralResult ([CCommRing.one] : DensePoly α) a d res := by
  have hone : toPoly ([CCommRing.one] : DensePoly α) = 1 := by
    simp only [denote]
    simp
  exact cIntegrateCase_primitive_sound ([CCommRing.one] : DensePoly α) a d cands res qp
    (fieldFrac (crPoly ([CCommRing.one] : DensePoly α) a d) [CCommRing.one])
    (by rw [hone]; exact one_ne_zero) hgden hb hqp hsome
    (cPolyRischDEG_nil_field_identity (crPoly ([CCommRing.one] : DensePoly α) a d) qp _ hfp (le_refl _)
      hqp hconst)
    hNrmField hrecon

/-- **Primitive case with BOTH `hSpecField` and `hrecon` discharged** (canonical primitive `Dt = 1`,
`fₚ ≠ 0`, special part `b = 0`): the special-part identity comes from the poly-RDE soundness and the
reconstruction from `canonicalReconstruction` (the `b = 0` special term vanishes). The only remaining
inputs are the shared reduced identity (`hNrmField`) and the `CPoly.splitFactor` split-correctness facts
(`hsplit`, coprimality) — the engine's split frontier. -/
theorem cIntegrateCase_primitive_sound_full [CharZero (CFieldSpec.K α)]
    (a d : DensePoly α) (cands : List α) (res : IntegralResult α) (qp : DensePoly α)
    (hgden : toPoly (redNorm ([CCommRing.one] : DensePoly α) a d cands).rational.2 ≠ 0)
    (hb : cisZero (crSpecNum ([CCommRing.one] : DensePoly α) a d) = true)
    (hfp : cisZero (crPoly ([CCommRing.one] : DensePoly α) a d) = false)
    (hconst : Differential.mapCoeffs (toPoly (crPoly ([CCommRing.one] : DensePoly α) a d)) = 0)
    (hqp : cPolyRischDE ([CCommRing.one] : DensePoly α) [] (crPoly ([CCommRing.one] : DensePoly α) a d)
        ((cdeg (crPoly ([CCommRing.one] : DensePoly α) a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase ([CCommRing.one] : DensePoly α) a d cands = some res)
    (hNrmField : IsIntegralResult ([CCommRing.one] : DensePoly α) (crNormNum ([CCommRing.one] : DensePoly α) a d)
        (crNormDen ([CCommRing.one] : DensePoly α) a d) (redNorm ([CCommRing.one] : DensePoly α) a d cands))
    (hd : toPoly d ≠ 0)
    (hdn : toPoly (crNormDen ([CCommRing.one] : DensePoly α) a d) ≠ 0)
    (hds : toPoly (crSpecDen ([CCommRing.one] : DensePoly α) a d) ≠ 0)
    (hsplit : toPoly d
      = toPoly (crSpecDen ([CCommRing.one] : DensePoly α) a d) * toPoly (crNormDen ([CCommRing.one] : DensePoly α) a d))
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (crNormDen ([CCommRing.one] : DensePoly α) a d)
        (crSpecDen ([CCommRing.one] : DensePoly α) a d)).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (crNormDen ([CCommRing.one] : DensePoly α) a d)
        (crSpecDen ([CCommRing.one] : DensePoly α) a d)).1 ≠ 0) :
    IsIntegralResult ([CCommRing.one] : DensePoly α) a d res := by
  have hspec0 : fieldFrac (crSpecNum ([CCommRing.one] : DensePoly α) a d)
      (crSpecDen ([CCommRing.one] : DensePoly α) a d) = 0 := by
    simp only [fieldFrac, (cisZeroG_iff (crSpecNum ([CCommRing.one] : DensePoly α) a d)).mp hb, map_zero,
      zero_div]
  have hrecon : fieldFrac (crPoly ([CCommRing.one] : DensePoly α) a d) [CCommRing.one]
        + fieldFrac (crNormNum ([CCommRing.one] : DensePoly α) a d) (crNormDen ([CCommRing.one] : DensePoly α) a d)
      = fieldFrac a d := by
    have h := canonicalReconstruction ([CCommRing.one] : DensePoly α) a d hd hdn hds hsplit hgdeg hgne
    rw [hspec0, add_zero] at h
    exact h
  exact cIntegrateCase_primitive_sound_polyRDE a d cands res qp hgden hb hfp hconst hqp hsome hNrmField
    hrecon

end DeepWiki.SymbolicIntegration
