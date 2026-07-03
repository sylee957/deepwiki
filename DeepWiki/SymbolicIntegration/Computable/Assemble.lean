import DeepWiki.SymbolicIntegration.Computable.UnifiedFuelFree
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.NormalCore
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.Special
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.FullSoundness

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
reconstruction. The concrete cases instantiate it; the hyperexp corollary below shows it subsumes the
driver's own soundness. -/

open QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] in
/-- **Generic assembler soundness.** If `cIntegrateCase C` returns `res` with the special-part hook giving
`(snum, sden)` (whose fraction differentiates to `specialVal`) and the corrected normal part `nrm` (whose
rational-plus-logs field identity is `hNrmField`), and the two parts reconstruct `a/d` (`hrecon`), then
`D(res.rational) + logResidueSum res.logs = a/d`. Proven once, from the hook field-identities. -/
theorem cIntegrateCase_sound (C : MonomialCase α) (Dt a d : CPolyG α) (cands : List α)
    (res : IntegralResultG α) (snum sden : CPolyG α) (nrm : IntegralResultG α)
    (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : toPolyG sden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hSpec : C.integrateSpecial Dt (canonicalRepresentationFastGWf Dt a d).1
        (canonicalRepresentationFastGWf Dt a d).2.1.1
        (canonicalRepresentationFastGWf Dt a d).2.1.2 = some (snum, sden))
    (hCorr : C.reducedCorrect Dt (cIntegrateReducedGWf Dt
        (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands) = some nrm)
    (hsome : cIntegrateCase C Dt a d cands = some res)
    (hSpecField : towerFractionFieldDerivG Dt (amG α (toPolyG snum) / amG α (toPolyG sden)) = specialVal)
    (hNrmField : towerFractionFieldDerivG Dt
            (amG α (toPolyG nrm.rational.1) / amG α (toPolyG nrm.rational.2))
          + logResidueSumG Dt nrm.logs
        = amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
          / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2))
    (hrecon : specialVal + amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  have hshape : res = combineSN snum sden nrm := by
    rw [cIntegrateCase] at hsome
    rcases hcrep : canonicalRepresentationFastGWf Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
    rw [hcrep] at hsome hSpec hCorr
    simp only [hSpec, hCorr] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
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
  rw [hcombine, map_add, hSpecField, add_assoc, hNrmField]
  exact hrecon

/-- **The hyperexp case, as a corollary of the generic soundness** (not the driver): the special value is
the polynomial part `⟦fpPart⟧`, `integrateSpecial`/`reducedCorrect` are the Laurent/normal solves. -/
theorem cIntegrateCase_hyperexp_sound (Dt a d : CPolyG α)
    (cands : List α) (res : IntegralResultG α) (lnum lden : CPolyG α) (nrm : IntegralResultG α)
    (fpPart : CPolyG α) (hlden : toPolyG lden ≠ 0) (hgden : toPolyG nrm.rational.2 ≠ 0)
    (hLaur : cIntegrateHyperexpLaurentG (cExpEtaG Dt)
        (canonicalRepresentationFastGWf Dt a d).1
        (cHyperexpSpecialNegG (canonicalRepresentationFastGWf Dt a d).2.1.1
          (canonicalRepresentationFastGWf Dt a d).2.1.2)
      = some (lnum, lden))
    (hNrm : cIntegrateHyperexpNormalGWf Dt
        (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands = some nrm)
    (hsome : cIntegrateCase hyperexpCase Dt a d cands = some res)
    (hLaurField : towerFractionFieldDerivG Dt (amG α (toPolyG lnum) / amG α (toPolyG lden))
        = amG α (toPolyG fpPart))
    (hNrmField : towerFractionFieldDerivG Dt
            (amG α (toPolyG nrm.rational.1) / amG α (toPolyG nrm.rational.2))
          + logResidueSumG Dt nrm.logs
        = amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
          / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2))
    (hrecon : amG α (toPolyG fpPart)
          + amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  cIntegrateCase_sound hyperexpCase Dt a d cands res lnum lden nrm (amG α (toPolyG fpPart))
    hlden hgden hLaur hNrm hsome hLaurField hNrmField hrecon

/-- **The primitive case, as a corollary of the generic soundness.** The special part is the polynomial
`qₚ` (as `qₚ/1`) from the `b = 0` RDE; the reduced part needs no correction, so `nrm` is the reduced result
directly. -/
theorem cIntegrateCase_primitive_sound (Dt a d : CPolyG α) (cands : List α) (res : IntegralResultG α)
    (qp : CPolyG α) (specialVal : RatFunc (CFieldSpec.K α))
    (hsden : toPolyG ([CField.one] : CPolyG α) ≠ 0)
    (hgden : toPolyG (cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands).rational.2 ≠ 0)
    (hb : cisZeroG (canonicalRepresentationFastGWf Dt a d).2.1.1 = true)
    (hqp : cPolyRischDEGWf Dt [] (canonicalRepresentationFastGWf Dt a d).1
        ((cdegG (canonicalRepresentationFastGWf Dt a d).1 : ℤ) + 1) = some qp)
    (hsome : cIntegrateCase primitiveCase Dt a d cands = some res)
    (hSpecField : towerFractionFieldDerivG Dt
        (amG α (toPolyG qp) / amG α (toPolyG ([CField.one] : CPolyG α))) = specialVal)
    (hNrmField : towerFractionFieldDerivG Dt
            (amG α (toPolyG (cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
                (canonicalRepresentationFastGWf Dt a d).2.2.2 cands).rational.1)
              / amG α (toPolyG (cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
                (canonicalRepresentationFastGWf Dt a d).2.2.2 cands).rational.2))
          + logResidueSumG Dt (cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
              (canonicalRepresentationFastGWf Dt a d).2.2.2 cands).logs
        = amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
          / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2))
    (hrecon : specialVal + amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastGWf Dt a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  have hSpec : primitiveCase.integrateSpecial Dt (canonicalRepresentationFastGWf Dt a d).1
      (canonicalRepresentationFastGWf Dt a d).2.1.1
      (canonicalRepresentationFastGWf Dt a d).2.1.2 = some (qp, [CField.one]) := by
    simp only [primitiveCase, hb, if_true, hqp]
  exact cIntegrateCase_sound primitiveCase Dt a d cands res qp [CField.one]
    (cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
      (canonicalRepresentationFastGWf Dt a d).2.2.2 cands) specialVal hsden hgden hSpec rfl hsome
    hSpecField hNrmField hrecon

end DeepWiki.SymbolicIntegration
