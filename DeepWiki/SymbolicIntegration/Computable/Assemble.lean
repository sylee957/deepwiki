import DeepWiki.SymbolicIntegration.Computable.UnifiedFuelFree
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.NormalCore
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.Special
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.FullSoundness
import DeepWiki.SymbolicIntegration.Computable.CanonicalFieldIdentity
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.FuelFreeDiophantine
import DeepWiki.SymbolicIntegration.Computable.LogPartTowerSoundness
import DeepWiki.SymbolicIntegration.Computable.HermiteTowerStep
import DeepWiki.SymbolicIntegration.Computable.HermiteValuationTower
import DeepWiki.SymbolicIntegration.Computable.OneShotAssembly
import DeepWiki.SymbolicIntegration.Computable.HermiteReduction
import DeepWiki.SymbolicIntegration.Computable.ResidueLogPart

/-! # Assemblable one-level Risch integrator

One generic integrator `cIntegrateCase` parameterized by a `MonomialCase` record (the per-case hooks), with
the primitive and hyperexponential cases as values. `cIntegrateHyperexpFullGWf` is definitionally the
hyperexp case; the primitive case is validated to reproduce the antiderivative identity.
-/

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

variable [CFracGcdCoreWf α]

/-- The generic one-level Risch integrator, parameterized by a monomial case `C`: canonical-split, run the
case's special-part hook, correct the reduced normal part, and combine. -/
def cIntegrateCase (C : MonomialCase α) (Dt a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d
  match C.integrateSpecial Dt fp b ds with
  | none => none
  | some (snum, sden) =>
    match C.reducedCorrect Dt (cIntegrateReducedGWf Dt cn dn cands) with
    | none => none
    | some nrm => some (combineSN snum sden nrm)

variable [CRischField α]

/-- Primitive monomial case (`Dt ∈ α`): the special part is empty (`b = 0` required), the polynomial part
`fₚ` is integrated by the `b = 0` RDE `cPolyRischDEGWf` as `qₚ/1`; the reduced part needs no correction. -/
def primitiveCase : MonomialCase α where
  integrateSpecial Dt fp b _ds :=
    if cisZeroG b then
      match cPolyRischDEGWf Dt [] fp ((cdegG fp : ℤ) + 1) with
      | none => none
      | some qp => some (qp, [CField.one])
    else none
  reducedCorrect _Dt nrm := some nrm

/-- Hyperexponential monomial case (`Dt = η·t`): the special/Laurent part is integrated by
`cIntegrateHyperexpLaurentG`; the reduced correction subtracts `∫R` (the residual `η·∑ᵢ cᵢ`). -/
def hyperexpCase : MonomialCase α where
  integrateSpecial Dt fp b ds :=
    cIntegrateHyperexpLaurentG (cExpEtaG Dt) fp (cHyperexpSpecialNegG b ds)
  reducedCorrect Dt nrm :=
    let η := cExpEtaG Dt
    let R := cHyperexpResidualG η nrm.logs
    match CRischField.crischDESolve (CField.zero : α) R with
    | none => none
    | some intR =>
      let gnum := nrm.rational.1
      let gden := nrm.rational.2
      some ⟨(csubG gnum (cmulG [intR] gden), gden), nrm.logs⟩

/-- **Bridge (hyperexp): the hyperexponential driver is definitionally the hyperexp case.** -/
theorem cIntegrateHyperexpFullGWf_eq_case (Dt a d : CPolyG α) (cands : List α) :
    cIntegrateHyperexpFullGWf Dt a d cands = cIntegrateCase hyperexpCase Dt a d cands := rfl

end CPolyG

/-! ### Validation — one assembler reproduces the antiderivative identity on both cases (`native_decide`) -/

open CPolyG

/-- Primitive case: `∫ 1/t² = −1/t` over `ℚ(x)[t]` with `Dt = 1` — `cIntegrateCase primitiveCase` returns a
result satisfying `checkIdentityG`. -/
theorem cIntegrateCase_primitive_invSq :
    (match cIntegrateCase (primitiveCase) ([CField.one] : CPolyG Lvl1)
        [CField.one] [CField.zero, CField.zero, CField.one] [CField.zero] with
      | some res => checkIdentityG ([CField.one] : CPolyG Lvl1) res [CField.one]
          [CField.zero, CField.zero, CField.one]
      | none => false) = true := by native_decide

/-- Hyperexp case: `∫ 1/exp = −1/exp` — `cIntegrateCase hyperexpCase` reproduces the hyperexp driver's
result satisfying `checkIdentityG` (same integrand data as `hyperexpInv_landsSpecialPart`). -/
theorem cIntegrateCase_hyperexp_inv :
    (match cIntegrateCase hyperexpCase hyperexpDt hyperexpInvA hyperexpInvD hyperexpInvCands with
      | some res => checkIdentityG hyperexpDt res hyperexpInvA hyperexpInvD
      | none => false) = true := by native_decide

/-- Hyperexp case on the special+normal mix `∫(1/exp + 1/(exp−1))`: the assembler lands the full identity
(where the special-part-only driver overshoots). -/
theorem cIntegrateCase_hyperexp_specNorm :
    (match cIntegrateCase hyperexpCase hyperexpDt hyperexpSpecNormA hyperexpSpecNormD
        hyperexpSpecNormCands with
      | some res => checkIdentityG hyperexpDt res hyperexpSpecNormA hyperexpSpecNormD
      | none => false) = true := by native_decide

/-! ### Generic soundness — one proof, both cases (P2)

`cIntegrateCase_sound` proves the field identity for the generic assembler from the two abstract hook
field-identities (`hSpecField` for `integrateSpecial`, `hNrmField` for `reducedCorrect`) and the canonical
reconstruction. Signatures read through the helpers below: `IsIntegralResultG` (the antiderivative
predicate), `fieldFrac` (a `CPolyG` fraction as a tower field element), and the `cr*`/`redNorm`
canonical-split accessors. The concrete cases instantiate it. -/

open QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- The tower fraction-field element `⟦num/den⟧ = amG(toPolyG num) / amG(toPolyG den)`. -/
noncomputable abbrev fieldFrac (num den : CPolyG α) : RatFunc (CFieldSpec.K α) :=
  amG α (toPolyG num) / amG α (toPolyG den)

/-- Polynomial part `fₚ` of `canonicalRepresentationFastGWf Dt a d`. -/
abbrev crPoly (Dt a d : CPolyG α) : CPolyG α := (canonicalRepresentationFastGWf Dt a d).1
/-- Special-part numerator `b` of the canonical split. -/
abbrev crSpecNum (Dt a d : CPolyG α) : CPolyG α := (canonicalRepresentationFastGWf Dt a d).2.1.1
/-- Special-part denominator `dₛ` of the canonical split. -/
abbrev crSpecDen (Dt a d : CPolyG α) : CPolyG α := (canonicalRepresentationFastGWf Dt a d).2.1.2
/-- Normal-part numerator `cₙ` of the canonical split. -/
abbrev crNormNum (Dt a d : CPolyG α) : CPolyG α := (canonicalRepresentationFastGWf Dt a d).2.2.1
/-- Normal-part denominator `dₙ` of the canonical split. -/
abbrev crNormDen (Dt a d : CPolyG α) : CPolyG α := (canonicalRepresentationFastGWf Dt a d).2.2.2
/-- The reduced integral of the normal part `cₙ/dₙ`. -/
abbrev redNorm (Dt a d : CPolyG α) (cands : List α) : IntegralResultG α :=
  cIntegrateReducedGWf Dt (crNormNum Dt a d) (crNormDen Dt a d) cands

omit [CDiffFieldSpec α] [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **Canonical reconstruction, modulo split correctness.** Given the special/normal split is a genuine
factorization `d = dₛ·dₙ` with `dₛ, dₙ` coprime (their gcd a nonzero constant) and nonzero, the canonical
pieces recombine: `⟦fₚ⟧ + ⟦b/dₛ⟧ + ⟦cₙ/dₙ⟧ = ⟦a/d⟧`. Assembles `toPolyG_cdivmodWf` (division),
`toPolyG_cbezoutOneWf` + `toPolyG_cextendedEuclideanSplitWf` (Bézout split), and
`canonicalRepFast_field_identity`. The only remaining input is the `cSplitFactorFastGWf` correctness
(`hsplit`, coprimality) — the engine's split frontier. -/
theorem canonicalReconstruction (Dt a d : CPolyG α)
    (hd : toPolyG d ≠ 0)
    (hdn : toPolyG (crNormDen Dt a d) ≠ 0)
    (hds : toPolyG (crSpecDen Dt a d) ≠ 0)
    (hsplit : toPolyG d = toPolyG (crSpecDen Dt a d) * toPolyG (crNormDen Dt a d))
    (hgdeg : (toPolyG (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1 ≠ 0) :
    fieldFrac (crPoly Dt a d) [CField.one]
        + fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d)
        + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d)
      = fieldFrac a d := by
  set qr := cdivmodWf a d with hqr
  set sn := cSplitFactorFastGWf Dt d with hsn
  set uw := cbezoutOneWf sn.1 sn.2 with huw
  set bc := cextendedEuclideanSplitWf sn.1 sn.2 qr.2 uw.1 uw.2 with hbc
  have hcanon : canonicalRepresentationFastGWf Dt a d = (qr.1, (bc.1, sn.2), (bc.2, sn.1)) := by
    rw [canonicalRepresentationFastGWf, ← hqr, ← hsn, ← huw, ← hbc]
  simp only [crPoly, crSpecNum, crSpecDen, crNormNum, crNormDen, fieldFrac, hcanon] at hdn hds hsplit hgdeg hgne ⊢
  have hcnd : cnormG d ≠ [] := fun h => hd ((cisZeroG_iff d).mp (by simp [cisZeroG, h]))
  have hcns : cnormG sn.2 ≠ [] := fun h => hds ((cisZeroG_iff sn.2).mp (by simp [cisZeroG, h]))
  have hbez : toPolyG uw.1 * toPolyG sn.1 + toPolyG uw.2 * toPolyG sn.2 = 1 :=
    toPolyG_cbezoutOneWf sn.1 sn.2 hgdeg hgne
  have hadiv : toPolyG a = toPolyG qr.1 * toPolyG d + toPolyG qr.2 := toPolyG_cdivmodWf a d hcnd
  have hbcr : toPolyG bc.1 * toPolyG sn.1 + toPolyG bc.2 * toPolyG sn.2 = toPolyG qr.2 :=
    toPolyG_cextendedEuclideanSplitWf sn.1 sn.2 qr.2 uw.1 uw.2 hcns hbez
  have hone : amG α (toPolyG ([CField.one] : CPolyG α)) = 1 := by
    rw [show toPolyG ([CField.one] : CPolyG α) = (1 : (CFieldSpec.K α)[X]) from by
      rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]]
    exact map_one (amG α)
  rw [hone, div_one]
  exact canonicalRepFast_field_identity (toPolyG a) (toPolyG d) (toPolyG qr.1) (toPolyG qr.2)
    (toPolyG sn.1) (toPolyG sn.2) (toPolyG bc.1) (toPolyG bc.2) hd hdn hds hadiv hsplit hbcr

omit [CRischField α] in
/-- **The reduced normal part is an integral result**, modulo the reduced-stage frontier: from the Hermite
half (`hherm`) and the Rothstein–Trager residue match (`hmatch`), `cIntegrateReducedGWf Dt a d cands`
satisfies the antiderivative predicate. A restatement of
`field_identity_of_cIntegrateReducedGWf_of_residueMatch` as `IsIntegralResultG`; `hherm`/`hmatch` are the
`cHermiteReduceTowerGWf` / RT-residue `native_decide` frontier. It discharges `hNrmField`. -/
theorem cIntegrateReducedGWf_isIntegralResult (Dt a d : CPolyG α) (cands : List α)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG α (toPolyG (cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hmatch : ((cIntegrateReducedGWf Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
          / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)) :
    IsIntegralResultG Dt a d (cIntegrateReducedGWf Dt a d cands) := by
  simp only [IsIntegralResultG]
  exact field_identity_of_cIntegrateReducedGWf_of_residueMatch Dt a d cands hherm hmatch

omit [CRischField α] in
/-- **Reduced-part soundness, consuming the interfaces (Stage-1).** From `LawfulHermiteReduction` (the
cleared Hermite identity) and `LawfulResidueLogPart` (the RT residue match) — the two *abstract* stage
laws — the reduced normal part integrates correctly. This is the assembler consuming its interfaces: the
composition `Hermite ∘ ResidueLogPart = reduced-part soundness`, with no concrete algorithm re-derived. -/
theorem cIntegrateReducedGWf_isIntegralResult_of_lawful (Dt a d : CPolyG α) (cands : List α)
    (hherm : LawfulHermiteReduction Dt a d (CPolyG.cHermiteReduceTowerGWf Dt a d).1.1
      (CPolyG.cHermiteReduceTowerGWf Dt a d).1.2 (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
      (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2)
    (hres : LawfulResidueLogPart Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
      (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 (CPolyG.cIntegrateReducedGWf Dt a d cands).logs) :
    IsIntegralResultG Dt a d (CPolyG.cIntegrateReducedGWf Dt a d cands) :=
  cIntegrateReducedGWf_isIntegralResult Dt a d cands hherm.field_identity hres.residue_match

omit [CRischField α] in
/-- **Generic assembler soundness.** If `cIntegrateCase C` returns `res` with the special-part hook giving
`(snum, sden)` (differentiating to `specialVal`) and the corrected normal part `nrm` (satisfying the
antiderivative predicate `hNrmField`), and the parts reconstruct `a/d` (`hrecon`), then `res` is an
antiderivative of `a/d`. Proven once, from the hook field-identities. -/
theorem cIntegrateCase_sound (C : MonomialCase α) (Dt a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (snum sden : CPolyG α) (nrm : IntegralResultG α)
    (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : toPolyG sden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hSpec : C.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d)
      = some (snum, sden))
    (hCorr : C.reducedCorrect Dt (redNorm Dt a d cands) = some nrm)
    (hsome : cIntegrateCase C Dt a d cands = some res)
    (hSpecField : towerFractionFieldDerivG Dt (fieldFrac snum sden) = specialVal)
    (hNrmField : IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm)
    (hrecon : specialVal + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d) :
    IsIntegralResultG Dt a d res := by
  have hshape : res = combineSN snum sden nrm := by
    rw [cIntegrateCase] at hsome
    simp only [crPoly, crSpecNum, crSpecDen, redNorm, crNormNum, crNormDen] at hSpec hCorr
    rcases hcrep : canonicalRepresentationFastGWf Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
    rw [hcrep] at hsome hSpec hCorr
    simp only [hSpec, hCorr] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  simp only [IsIntegralResultG] at hNrmField ⊢
  rw [hshape]
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

/-- **The hyperexp case, as a corollary of the generic soundness** (not the driver): the special value is
the polynomial part `⟦fpPart⟧`, `integrateSpecial`/`reducedCorrect` are the Laurent/normal solves. -/
theorem cIntegrateCase_hyperexp_sound (Dt a d : CPolyG α)
    (cands : List α) (res : IntegralResultG α) (lnum lden : CPolyG α) (nrm : IntegralResultG α)
    (fpPart : CPolyG α) (hlden : toPolyG lden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hLaur : cIntegrateHyperexpLaurentG (cExpEtaG Dt) (crPoly Dt a d)
        (cHyperexpSpecialNegG (crSpecNum Dt a d) (crSpecDen Dt a d)) = some (lnum, lden))
    (hNrm : cIntegrateHyperexpNormalGWf Dt (crNormNum Dt a d) (crNormDen Dt a d) cands = some nrm)
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
    (hqp : cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) = some qp)
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
`hSpecField` is no longer a hypothesis — it follows from `cPolyRischDEGWf_nil_field_identity` (the engine's
own poly-RDE soundness), leaving only the shared reduced identity (`hNrmField`) and reconstruction
(`hrecon`). One step closer to unconditional. -/
theorem cIntegrateCase_primitive_sound_polyRDE [CharZero (CFieldSpec.K α)]
    (a d : CPolyG α) (cands : List α) (res : IntegralResultG α) (qp : CPolyG α)
    (hgden : toPolyG (redNorm ([CField.one] : CPolyG α) a d cands).rational.2 ≠ 0)
    (hb : cisZeroG (crSpecNum ([CField.one] : CPolyG α) a d) = true)
    (hfp : cisZeroG (crPoly ([CField.one] : CPolyG α) a d) = false)
    (hconst : Differential.mapCoeffs (toPolyG (crPoly ([CField.one] : CPolyG α) a d)) = 0)
    (hqp : cPolyRischDEGWf ([CField.one] : CPolyG α) [] (crPoly ([CField.one] : CPolyG α) a d)
        ((cdegG (crPoly ([CField.one] : CPolyG α) a d) : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase ([CField.one] : CPolyG α) a d cands = some res)
    (hNrmField : IsIntegralResultG ([CField.one] : CPolyG α) (crNormNum ([CField.one] : CPolyG α) a d)
        (crNormDen ([CField.one] : CPolyG α) a d) (redNorm ([CField.one] : CPolyG α) a d cands))
    (hrecon : fieldFrac (crPoly ([CField.one] : CPolyG α) a d) [CField.one]
          + fieldFrac (crNormNum ([CField.one] : CPolyG α) a d) (crNormDen ([CField.one] : CPolyG α) a d)
        = fieldFrac a d) :
    IsIntegralResultG ([CField.one] : CPolyG α) a d res := by
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  exact cIntegrateCase_primitive_sound ([CField.one] : CPolyG α) a d cands res qp
    (fieldFrac (crPoly ([CField.one] : CPolyG α) a d) [CField.one])
    (by rw [hone]; exact one_ne_zero) hgden hb hqp hsome
    (cPolyRischDEGWf_nil_field_identity (crPoly ([CField.one] : CPolyG α) a d) qp _ hfp (le_refl _)
      hqp hconst)
    hNrmField hrecon

/-- **Primitive case with BOTH `hSpecField` and `hrecon` discharged** (canonical primitive `Dt = 1`,
`fₚ ≠ 0`, special part `b = 0`): the special-part identity comes from the poly-RDE soundness and the
reconstruction from `canonicalReconstruction` (the `b = 0` special term vanishes). The only remaining
inputs are the shared reduced identity (`hNrmField`) and the `cSplitFactorFastGWf` split-correctness facts
(`hsplit`, coprimality) — the engine's split frontier. -/
theorem cIntegrateCase_primitive_sound_full [CharZero (CFieldSpec.K α)]
    (a d : CPolyG α) (cands : List α) (res : IntegralResultG α) (qp : CPolyG α)
    (hgden : toPolyG (redNorm ([CField.one] : CPolyG α) a d cands).rational.2 ≠ 0)
    (hb : cisZeroG (crSpecNum ([CField.one] : CPolyG α) a d) = true)
    (hfp : cisZeroG (crPoly ([CField.one] : CPolyG α) a d) = false)
    (hconst : Differential.mapCoeffs (toPolyG (crPoly ([CField.one] : CPolyG α) a d)) = 0)
    (hqp : cPolyRischDEGWf ([CField.one] : CPolyG α) [] (crPoly ([CField.one] : CPolyG α) a d)
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

/-! ### Reduced-part soundness with the Hermite `hherm` discharged

`hherm` in `field_identity_of_cIntegrateReducedGWf_of_residueMatch` is *definitionally* the whole-step
Hermite identity `hermiteTowerStep_field_identity` (since `(cIntegrateReducedGWf …).rational = H.1` for
`H = cHermiteReduceTowerGWf …`). So the reduced-part soundness reduces to the single **exact-division**
frontier plus the RT residue match — the Hermite half is now assembled, not assumed. -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

open QFunNZG in
/-- **Reduced-part soundness, Hermite half discharged.** Given the exact-division relation for the
`cHermiteReduceTowerGWf` output (`hexact`) and the RT residue match (`hmatch`), the reduced normal part
integrates correctly: `D(⟦reduced.rational⟧) + logResidueSum reduced.logs = ⟦a/d⟧`. The Hermite `hherm`
is discharged by `hermiteTowerStep_field_identity`. -/
theorem field_identity_of_cIntegrateReducedGWf_of_residueMatch_of_exact (Dt a d : CPolyG α)
    (cands : List α)
    (hd : amG α (toPolyG d) ≠ 0)
    (hgden : amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).1.2) ≠ 0)
    (hDstar : amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2) ≠ 0)
    (hexact : amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1)
          * amG α (toPolyG (CPolyG.cmulG d
              (CPolyG.cmulG (CPolyG.cHermiteReduceTowerGWf Dt a d).1.2
                (CPolyG.cHermiteReduceTowerGWf Dt a d).1.2)))
        = amG α (toPolyG (CPolyG.csubG
            (CPolyG.cmulG a (CPolyG.cmulG (CPolyG.cHermiteReduceTowerGWf Dt a d).1.2
              (CPolyG.cHermiteReduceTowerGWf Dt a d).1.2))
            (CPolyG.cmulG d (CPolyG.csubG
              (CPolyG.cmulG (CPolyG.cmonomialDeriv Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).1.1)
                (CPolyG.cHermiteReduceTowerGWf Dt a d).1.2)
              (CPolyG.cmulG (CPolyG.cHermiteReduceTowerGWf Dt a d).1.1
                (CPolyG.cmonomialDeriv Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).1.2))))))
          * amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2))
    (hmatch : ((CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1)
          / amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_cIntegrateReducedGWf_of_residueMatch Dt a d cands
    (hermiteTowerStep_field_identity Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).1.1
      (CPolyG.cHermiteReduceTowerGWf Dt a d).1.2 a d (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
      (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 hd hgden hDstar hexact)
    hmatch

open Classical in
/-- **Reduced-part soundness, Hermite half discharged from pole-cancellation.** Given the RT residue
match (`hmatch`) and the differential-normality side condition `hcopgcd`, the reduced normal part
integrates correctly. Here the whole-step Hermite identity `hherm` is discharged by the pole-cancellation
capstone `cHermiteReduceTowerGWf_field_identity` (its radical numerator matched to the def field `.2.1`
via `toPolyG_hNum'_eq_2_1`), so `hexact`/`hgden`/`hDstar` are no longer separate frontiers — only the
genuine Bronstein normality condition `hcopgcd` remains (besides `hmatch` and the ℚ-unconditional gcd
frontier `hgcd`). -/
theorem field_identity_of_cIntegrateReducedGWf_of_residueMatch_of_hcopgcd
    [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (cands : List α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (CPolyG.cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hmatch : ((CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1)
          / amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_cIntegrateReducedGWf_of_residueMatch Dt a d cands
    (by
      have hcap := cHermiteReduceTowerGWf_field_identity hgcd Dt a d hd0 hpp hcopgcd
      rwa [toPolyG_hNum'_eq_2_1 hgcd Dt a d hd0 hpp hcopgcd] at hcap)
    hmatch

open Classical in
/-- **Reduced part is an integral result, Hermite frontier discharged.** Same as
`cIntegrateReducedGWf_isIntegralResult` but with the whole-step Hermite identity `hherm` supplied by the
pole-cancellation capstone (`field_identity_of_cIntegrateReducedGWf_of_residueMatch_of_hcopgcd`), so the
only Hermite-side obligation is the genuine differential-normality side condition `hcopgcd` — not a
`native_decide`-only frontier. This is the `hNrmField` input of the primitive/hyperexp assemblers with the
Hermite half now abstract. -/
theorem cIntegrateReducedGWf_isIntegralResult_of_hcopgcd [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (cands : List α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (CPolyG.cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hmatch : ((cIntegrateReducedGWf Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
          / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)) :
    IsIntegralResultG Dt a d (cIntegrateReducedGWf Dt a d cands) := by
  simp only [IsIntegralResultG]
  exact field_identity_of_cIntegrateReducedGWf_of_residueMatch_of_hcopgcd
    hgcd Dt a d cands hd0 hpp hcopgcd hmatch

open Classical in
/-- **The maximally-discharged primitive reduced-case field identity.** Assembles the whole primitive
reduced case (`D⟦reduced.rational⟧ + logResidueSum reduced.logs = ⟦a/d⟧`) with `s :=` the roots of the
reduced denominator, discharging FOUR side conditions from this session's arcs:
- `hherm` (whole-step Hermite) ← the pole-cancellation capstone + `toPolyG_hNum'_eq_2_1`, needs `hcopgcd`;
- `hden` (`.2.2 = nodal s`) ← `toPolyG_cHermiteReduceTowerGWf_Dstar_eq_nodal`, needs `hsplit`;
- `hnorm` (normality) and `hDd` (resolvent derivative ≠ 0) ← constant roots (`hconst`) + `hw : w ≠ 0`.
The genuinely-remaining inputs are: `hA` (leftover properness, the "Large residual"), `hdist` (residue
distinctness, genuine), `hres`/`hcand`/`hgcdread` (residue-enumeration + engine gcd-compute). -/
theorem field_identity_of_cIntegrateReducedGWf_primitive_maximal [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (cands : List α)
    (w : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hDt : toPolyG Dt = Polynomial.C w) (hw : w ≠ 0)
    (hsplit : (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).Splits)
    (hconst : ∀ β ∈ (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset, β′ = 0)
    (hcopgcd : ∀ x ∈ (CPolyG.cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hA : (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).degree
      < (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset.card)
    (hres : CPolyG.cRationalResiduesGWf Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
        (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 cands
      = (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset.toList.map residueCand)
    (hdist : ∀ γ ∈ (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset,
      ∀ δ ∈ (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset, γ ≠ δ →
      (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal
              (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset id)).eval γ
        ≠ (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal
              (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset id)).eval δ)
    (hcand : ∀ β ∈ (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset,
      CFieldSpec.toK (residueCand β)
      = (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal
            (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset id)).eval β) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  set s := (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).roots.toFinset with hs
  have hden : toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id :=
    toPolyG_cHermiteReduceTowerGWf_Dstar_eq_nodal hgcd Dt a d hd0 hpp hsplit
  have hherm : towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
      + amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1)
        / amG α (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2)
      = amG α (toPolyG a) / amG α (toPolyG d) := by
    have hcap := cHermiteReduceTowerGWf_field_identity hgcd Dt a d hd0 hpp hcopgcd
    rwa [toPolyG_hNum'_eq_2_1 hgcd Dt a d hd0 hpp hcopgcd] at hcap
  have hnorm : ∀ β ∈ s, w ≠ β′ := primitive_monomial_norm_of_const_roots s w hw hconst
  have hDd : ∀ β ∈ s, (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β ≠ 0 := by
    intro β hβ
    rw [hDt]
    exact implicitDeriv_C_nodal_eval_ne_zero w hw s hconst β hβ
  have hgcdread : ∀ β ∈ s, Associated
      (toPolyG (CPolyG.cLogArgTowerGWf Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
          (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 (residueCand β)))
      (gcd (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2)
          (toPolyG (CPolyG.cAmcDdG Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
            (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 (residueCand β)))) := fun β _ =>
    hgcd (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2
      (CPolyG.cAmcDdG Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
        (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 (residueCand β))
  exact field_identity_of_cIntegrateReducedGWf_primitive_of_residueData Dt a d cands s w residueCand
    hDt hherm hden hA hnorm hres hDd hdist hcand hgcdread

/-- `Algebra ℚ (CFieldSpec.K (QFunNZG ℚ))` via `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- `CharZero (CFieldSpec.K (QFunNZG ℚ))` via `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`. -/
local instance : CharZero (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (CharZero (RatFunc ℚ))

open Classical in
/-- **The fuel-free primitive one-shot at `ℚ(x)(t)` with the Hermite `hherm` ALSO discharged.** Extends
`cIntegrateGFullWf_primitive_oneShot_inputProper_qfunNZG` (which already discharges `hA`) by discharging the
whole-step Hermite identity `hherm` from the pole-cancellation capstone (`cHermiteReduceTowerGWf_field_identity`
+ `toPolyG_hNum'_eq_2_1`, on the normal part `cn/dn`), so the Hermite frontier is gone: the remaining inputs
are the genuine differential-normality `hcopgcd`, the residue data (`hform`/`hnorm`/`hden`), input properness
`haProper`, and the engine-regularity connectors (`hv`/`hbk`/`hdvd`/`hresDen`) + the tower gcd frontier `hgcd`. -/
theorem cIntegrateGFullWf_primitive_oneShot_hcopgcd_qfunNZG (Dt : CPolyG (QFunNZG ℚ))
    (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ)) (res : IntegralResultG (QFunNZG ℚ))
    (s : Finset (CFieldSpec.K (QFunNZG ℚ))) (w : CFieldSpec.K (QFunNZG ℚ))
    (hgcd : GcdFFCorrect (α := QFunNZG ℚ))
    (hDt : toPolyG Dt = Polynomial.C w)
    (hb' : CPolyG.cisZeroG (canonicalRepresentationFastGWf Dt a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastGWf Dt a d).1 = true)
    (hsome : CPolyG.cIntegrateGFullWf Dt a d cands = some res)
    (hrecon : amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
          / amG (QFunNZG ℚ) (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2)
        = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d))
    (hdn0 : toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2 ≠ 0)
    (hpp : (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (CPolyG.cSqfreeYunFFGWf (canonicalRepresentationFastGWf Dt a d).2.2.2).zipIdx.filter
        (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (CPolyG.cgcdWf (CPolyG.cmulG
          (CPolyG.cdivWf (canonicalRepresentationFastGWf Dt a d).2.2.2 (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (CPolyG.cgcdWf (CPolyG.cmulG
          (CPolyG.cdivWf (canonicalRepresentationFastGWf Dt a d).2.2.2 (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hden : toPolyG (cHermiteReduceTowerGWf Dt
          (canonicalRepresentationFastGWf Dt a d).2.2.1
          (canonicalRepresentationFastGWf Dt a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (CPolyG.cIntegrateReducedGWf Dt
            (canonicalRepresentationFastGWf Dt a d).2.2.1
            (canonicalRepresentationFastGWf Dt a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerGWf Dt
                  (canonicalRepresentationFastGWf Dt a d).2.2.1
                  (canonicalRepresentationFastGWf Dt a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (haProper : (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1).degree
      < (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2).degree)
    (hv : ∀ p ∈ (CPolyG.cSqfreeYunFFGWf (canonicalRepresentationFastGWf Dt a d).2.2.2).zipIdx,
        ¬ (p.2 + 1 ≤ 1) → toPolyG p.1 ≠ 0)
    (hbk : ∀ p ∈ (CPolyG.cSqfreeYunFFGWf (canonicalRepresentationFastGWf Dt a d).2.2.2).zipIdx,
        ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : CPolyG (QFunNZG ℚ)),
        (toPolyG (cdiophantineGWf
            (CPolyG.cmulG (CPolyG.cdivWf (canonicalRepresentationFastGWf Dt a d).2.2.2
              (CPolyG.cpowG p.1 (p.2 + 1))) (CPolyG.cmonomialDeriv Dt p.1)) p.1 rhs).1).degree
          < (toPolyG p.1).degree)
    (g : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ))
    (hgeq : g = (CPolyG.cSqfreeYunFFGWf (canonicalRepresentationFastGWf Dt a d).2.2.2).zipIdx.foldl
      (fun (gAcc : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)) (vi, idx) =>
        let i := idx + 1
        if i ≤ 1 then gAcc
        else
          let Vi_pow := CPolyG.cpowG vi i
          let u := CPolyG.cdivWf (canonicalRepresentationFastGWf Dt a d).2.2.2 Vi_pow
          let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1)
            (canonicalRepresentationFastGWf Dt a d).2.2.1 ([CField.zero], [CField.one])).1
          (CPolyG.caddG (CPolyG.cmulG gAcc.1 gloc.2) (CPolyG.cmulG gloc.1 gAcc.2),
            CPolyG.cmulG gAcc.2 gloc.2))
      ([CField.zero], [CField.one]))
    (hdvd : toPolyG (CPolyG.cmulG (canonicalRepresentationFastGWf Dt a d).2.2.2
        (CPolyG.cmulG g.2 g.2))
      ∣ toPolyG (CPolyG.cmulG (CPolyG.csubG
          (CPolyG.cmulG (canonicalRepresentationFastGWf Dt a d).2.2.1 (CPolyG.cmulG g.2 g.2))
          (CPolyG.cmulG (canonicalRepresentationFastGWf Dt a d).2.2.2
            (CPolyG.csubG (CPolyG.cmulG (CPolyG.cmonomialDeriv Dt g.1) g.2)
              (CPolyG.cmulG g.1 (CPolyG.cmonomialDeriv Dt g.2)))))
        ((CPolyG.cSqfreeYunFFGWf (canonicalRepresentationFastGWf Dt a d).2.2.2).foldl
          (fun acc vi => CPolyG.cmulG acc vi) [CField.one])))
    (hresDen : cnormG (CPolyG.cmulG (canonicalRepresentationFastGWf Dt a d).2.2.2
        (CPolyG.cmulG g.2 g.2)) ≠ ([] : CPolyG (QFunNZG ℚ))) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG res.rational.1) / amG (QFunNZG ℚ) (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) := by
  have hherm := cHermiteReduceTowerGWf_field_identity hgcd Dt
    (canonicalRepresentationFastGWf Dt a d).2.2.1 (canonicalRepresentationFastGWf Dt a d).2.2.2
    hdn0 hpp hcopgcd
  rw [toPolyG_hNum'_eq_2_1 hgcd Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
    (canonicalRepresentationFastGWf Dt a d).2.2.2 hdn0 hpp hcopgcd] at hherm
  exact cIntegrateGFullWf_primitive_oneShot_inputProper_qfunNZG Dt a d cands res s w hDt hb' hfp
    hsome hrecon hherm hden hnorm hform haProper hv hbk g hgeq hdvd hresDen

end DeepWiki.SymbolicIntegration
