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
import DeepWiki.SymbolicIntegration.Computable.HermiteReductionRealization
import DeepWiki.SymbolicIntegration.Computable.ResidueLogPart
import DeepWiki.SymbolicIntegration.Computable.Assemble

/-! # The concrete one-level Risch assembler (realization of the abstract `Assemble`)

The concrete generic integrator `cIntegrateCase` (parameterized by a `MonomialCase` record), the primitive
and hyperexponential case instances, the canonical-split accessors, and the reduced-stage realizations —
everything that names a concrete algorithm. The abstract soundness core (`combineSN_isIntegralResult`),
`MonomialCase`, `combineSN`, and `fieldFrac` live in `Assemble.lean`; this file realizes them. See
`docs/risch-two-stage-discipline.md`.
-/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

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

open Classical in
omit [CRischField α] in
/-- **Primitive reduced-part soundness, assembled from the two realizations through the interfaces.** The
end-to-end payoff of the two-stage discipline: `cHermiteReduceTowerGWf_lawfulHermiteReduction` (Stage 2) and
`cIntegrateReducedGWf_lawfulResidueLogPart` (Stage 2) fed through `cIntegrateReducedGWf_isIntegralResult_of_lawful`
(Stage 1) — the reduced normal part integrates correctly with NO concrete algorithm re-derived in the
composition, only the two realization theorems and the abstract law. -/
theorem cIntegrateReducedGWf_primitive_isIntegralResult_via_interfaces [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (w : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (CPolyG.cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).degree
      < (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).degree)
    (hDt : toPolyG Dt = Polynomial.C w)
    (hden : toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hres : CPolyG.cRationalResiduesGWf Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
        (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPolyG (CPolyG.cLogArgTowerGWf Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
          (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 (residueCand β)))
      (gcd (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2)
          (toPolyG (CPolyG.cAmcDdG Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
            (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 (residueCand β))))) :
    IsIntegralResultG Dt a d (CPolyG.cIntegrateReducedGWf Dt a d cands) :=
  cIntegrateReducedGWf_isIntegralResult_of_lawful Dt a d cands
    (cHermiteReduceTowerGWf_lawfulHermiteReduction hgcd Dt a d hd0 hpp hcopgcd hproper)
    (cIntegrateReducedGWf_lawfulResidueLogPart Dt a d cands s w residueCand hDt hden hA hnorm hres
      hDd hdist hcand hgcdread)

open Classical in
omit [CRischField α] in
/-- **Hyperexp reduced-part soundness, assembled from the two realizations through the interfaces.** The
hyperexponential analogue of `…primitive_isIntegralResult_via_interfaces` — same Stage-1 composition, with
the hyperexp `ResidueLogPart` realization (integrability witness `hsum : ∑ c = 0`). -/
theorem cIntegrateReducedGWf_hyperexp_isIntegralResult_via_interfaces [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (cands : List α) (s : Finset (CFieldSpec.K α))
    (b : CFieldSpec.K α) (residueCand : CFieldSpec.K α → α)
    (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (CPolyG.cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (CPolyG.cgcdWf (CPolyG.cmulG (CPolyG.cdivWf d (CPolyG.cpowG x.1 (x.2 + 1)))
          (CPolyG.cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).degree
      < (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2).degree)
    (hb : b ≠ 0) (hDt : toPolyG Dt = Polynomial.C b * X)
    (hden : toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (Polynomial.C b * X).eval β ≠ β′)
    (hsum : ∑ β ∈ s, (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β = 0)
    (hres : CPolyG.cRationalResiduesGWf Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
        (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 cands = s.toList.map residueCand)
    (hDd : ∀ β ∈ s,
      (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β ≠ 0)
    (hdist : ∀ γ ∈ s, ∀ δ ∈ s, γ ≠ δ →
      (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval γ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval γ
        ≠ (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval δ
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval δ)
    (hcand : ∀ β ∈ s, CFieldSpec.toK (residueCand β)
      = (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1).eval β
        / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β)
    (hgcdread : ∀ β ∈ s, Associated
      (toPolyG (CPolyG.cLogArgTowerGWf Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
          (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 (residueCand β)))
      (gcd (toPolyG (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2)
          (toPolyG (CPolyG.cAmcDdG Dt (CPolyG.cHermiteReduceTowerGWf Dt a d).2.1
            (CPolyG.cHermiteReduceTowerGWf Dt a d).2.2 (residueCand β))))) :
    IsIntegralResultG Dt a d (CPolyG.cIntegrateReducedGWf Dt a d cands) :=
  cIntegrateReducedGWf_isIntegralResult_of_lawful Dt a d cands
    (cHermiteReduceTowerGWf_lawfulHermiteReduction hgcd Dt a d hd0 hpp hcopgcd hproper)
    (cIntegrateReducedGWf_lawfulResidueLogPart_hyperexp Dt a d cands s b residueCand hb hDt hden hA
      hnorm hsum hres hDd hdist hcand hgcdread)

omit [CRischField α] in
/-- **Generic assembler soundness.** If `cIntegrateCase C` returns `res` with the special-part hook giving
`(snum, sden)` (differentiating to `specialVal`) and the corrected normal part `nrm` (satisfying the
antiderivative predicate `hNrmField`), and the parts reconstruct `a/d` (`hrecon`), then `res` is an
antiderivative of `a/d`. Proven once, from the abstract core `combineSN_isIntegralResult`. -/
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
  rw [hshape]
  exact combineSN_isIntegralResult Dt a d (crNormNum Dt a d) (crNormDen Dt a d) snum sden nrm
    specialVal hsden hgden hSpecField hNrmField hrecon

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

variable [CRischField α]

/-! ## The materializable solver bundle (`RischSolver`)

The whole two-stage discipline, packaged as one structure. A `RischSolver` bundles the case hooks
(`case`), the special-value function, and the three soundness laws (`specialSound`, `reducedSound`,
`recon`) plus the completeness descent law (`descend` over the frontier predicates `SpecElem`/`NrmElem`).
Materializing all fields — each discharged by a Stage-2 realization (`cSqfreeYunFFGWf_lawful…`,
`cHermiteReduceTowerGWf_lawful…`, `cIntegrateReducedGWf_lawfulResidueLogPart`, the case's `hSpecField`,
`canonicalReconstruction`) — yields the assembled integrator `.integrate` together with its soundness
(`.sound`), constructive completeness (`.isElementaryIntegrable_of_run`), and the completeness frontier
(`.not_isElementaryIntegrable`) *for free*, all derived from the abstract cores in `Assemble.lean`. -/

/-- **A materializable one-level Risch solver.** The case hooks + special value + the soundness laws
(`specialSound`/`reducedSound`/`recon`) + the completeness descent law (`descend`). Every field is
discharged by an independent Stage-2 realization; instantiating the bundle assembles the algorithm and
both proofs. -/
structure RischSolver (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] where
  /-- The per-monomial-case computable hooks. -/
  case : MonomialCase α
  /-- **Automatically computed residue candidates.** The constant-root list the reduced stage needs,
  computed from the input `Dt a d` — so the assembled integrator takes no `cands` argument. -/
  candidates : CPolyG α → CPolyG α → CPolyG α → List α
  /-- The value the special part `snum/sden` differentiates to (a function of the input). -/
  specialVal : CPolyG α → CPolyG α → CPolyG α → RatFunc (CFieldSpec.K α)
  /-- **Special-hook soundness law.** A successful `integrateSpecial` gives a nonzero denominator and a
  fraction differentiating to `specialVal`. Discharged by the case's own `hSpecField` realization. -/
  specialSound : ∀ (Dt a d snum sden : CPolyG α),
    case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
    toPolyG sden ≠ 0 ∧ towerFractionFieldDerivG Dt (fieldFrac snum sden) = specialVal Dt a d
  /-- **Reduced-hook soundness law.** A successful `reducedCorrect` on `redNorm` gives a nonzero
  denominator and an antiderivative of the normal part. Discharged via `LawfulHermiteReduction` +
  `LawfulResidueLogPart` through `cIntegrateReducedGWf_isIntegralResult_of_lawful`. -/
  reducedSound : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α),
    case.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
    toPolyG nrm.rational.2 ≠ 0 ∧ IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm
  /-- **Canonical reconstruction law.** The special value and normal fraction recombine to `⟦a/d⟧`.
  Discharged by `canonicalReconstruction` (modulo the split frontier). -/
  recon : ∀ (Dt a d : CPolyG α),
    specialVal Dt a d + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d
  /-- Special-part elementarity obstruction predicate (the completeness frontier). -/
  SpecElem : CPolyG α → CPolyG α → CPolyG α → Prop
  /-- Normal-part elementarity obstruction predicate (the completeness frontier). -/
  NrmElem : CPolyG α → CPolyG α → CPolyG α → Prop
  /-- **Completeness descent law.** Elementary integrability of `a/d` descends to elementarity of both
  the special and normal obligations. The Liouville / residue-criterion content — the frontier contract. -/
  descend : ∀ (Dt a d : CPolyG α),
    IsElementaryIntegrableG Dt a d → SpecElem Dt a d ∧ NrmElem Dt a d

namespace RischSolver

/-- **The assembled integrator (fully automatic).** Materializing the bundle gives the algorithm: run
`cIntegrateCase` on the bundle's case hooks with the solver's own computed candidate list
`S.candidates Dt a d`. A function of `(Dt, a, d)` alone — no `cands` argument. -/
def integrate (S : RischSolver α) (Dt a d : CPolyG α) : Option (IntegralResultG α) :=
  cIntegrateCase S.case Dt a d (S.candidates Dt a d)

/-- **Derived soundness.** Any successful run of the assembled integrator is an antiderivative of `a/d`,
proven once by composing the bundle's laws through the abstract core `cIntegrateCase_sound`. -/
theorem sound (S : RischSolver α) (Dt a d : CPolyG α) (res : IntegralResultG α)
    (h : S.integrate Dt a d = some res) : IsIntegralResultG Dt a d res := by
  set cands := S.candidates Dt a d with hcands
  have h0 : cIntegrateCase S.case Dt a d cands = some res := h
  rw [integrate, cIntegrateCase, ← hcands] at h
  rcases hcrep : canonicalRepresentationFastGWf Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
  rw [hcrep] at h
  dsimp only at h
  rcases hspec : S.case.integrateSpecial Dt fp b ds with _ | ⟨snum, sden⟩
  · rw [hspec] at h; simp at h
  · rw [hspec] at h
    rcases hcorr : S.case.reducedCorrect Dt (cIntegrateReducedGWf Dt cn dn cands) with _ | nrm
    · rw [hcorr] at h; simp at h
    · rw [hcorr] at h
      have hSpec : S.case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d)
          = some (snum, sden) := by
        simp only [crPoly, crSpecNum, crSpecDen, hcrep]; exact hspec
      have hCorr : S.case.reducedCorrect Dt (redNorm Dt a d cands) = some nrm := by
        simp only [redNorm, crNormNum, crNormDen, hcrep]; exact hcorr
      obtain ⟨hsden, hSpecField⟩ := S.specialSound Dt a d snum sden hSpec
      obtain ⟨hgden, hNrmField⟩ := S.reducedSound Dt a d cands nrm hCorr
      exact cIntegrateCase_sound S.case Dt a d cands res snum sden nrm (S.specialVal Dt a d)
        hsden hgden hSpec hCorr h0 hSpecField hNrmField (S.recon Dt a d)

/-- **Derived constructive completeness.** A successful run certifies `a/d` is elementary integrable
(the soundness witness fed through the Stage-1 bridge). -/
theorem isElementaryIntegrable_of_run (S : RischSolver α) (Dt a d : CPolyG α)
    (res : IntegralResultG α) (h : S.integrate Dt a d = some res) :
    IsElementaryIntegrableG Dt a d :=
  IsElementaryIntegrableG.of_isIntegralResult (S.sound Dt a d res h)

/-- **Derived completeness frontier.** A certified obstruction in either the special or normal part makes
`a/d` non-elementary, via the bundle's descent law through the abstract core. -/
theorem not_isElementaryIntegrable (S : RischSolver α) (Dt a d : CPolyG α)
    (hobstruct : ¬ S.SpecElem Dt a d ∨ ¬ S.NrmElem Dt a d) : ¬ IsElementaryIntegrableG Dt a d :=
  not_isElementaryIntegrableG_of_obstruction Dt a d (S.descend Dt a d) hobstruct

end RischSolver

end DeepWiki.SymbolicIntegration
