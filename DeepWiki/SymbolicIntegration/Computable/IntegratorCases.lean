import DeepWiki.SymbolicIntegration.Computable.IntegratorAssembly

/-! # Concrete one-level Risch cases (realizations of the generic assembler)

The concrete `MonomialCase` instances — `primitiveCase` (`Dt ∈ α`) and `hyperexpCase` (`Dt = η·t`) — the
`native_decide` validations that one assembler reproduces the antiderivative identity on both, and the
per-case reduced-stage soundness realizations assembled from the Stage-2 interface realizations
(`LawfulHermiteReduction` + `LawfulResidueLogPart`). Everything here names a concrete algorithm; the generic
assembler (`cIntegrateCase`, `cIntegrateCase_sound`) lives in `IntegratorAssembly.lean`, and the recursive
Risch-solver abstraction is `LawfulRischLevelLrt` (`RischTowerLrt.lean`). See `docs/risch-two-stage-discipline.md`.
-/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

variable [CFracGcdCoreWf α]

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

open CPolyG

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

open QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

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
    simp only [denote]
    simp
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

end DeepWiki.SymbolicIntegration
