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

/-! # The generic one-level Risch assembler + the materializable `RischSolver` bundle

The **generic** integrator `cIntegrateCase` (parameterized by a `MonomialCase` record), the canonical-split
accessors (`crPoly`/…/`redNorm`), the canonical reconstruction, the generic soundness `cIntegrateCase_sound`,
and the abstract solver bundle `RischSolver` (whose `.integrate`/`.sound`/`.isElementaryIntegrable_of_run`/
`.not_isElementaryIntegrable` are derived from the abstract cores). The concrete *case instances*
(`primitiveCase`, `hyperexpCase`), the `native_decide` validations, and the per-case reduced-stage
realizations live in `IntegratorCases.lean`, which imports this file. The abstract soundness/completeness
cores (`combineSN_isIntegralResult`, `IsElementaryIntegrableG`, `MonomialCase`, `combineSN`, `fieldFrac`)
live in `Assemble.lean`. See `docs/risch-two-stage-discipline.md`.
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

end CPolyG

open CPolyG
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
