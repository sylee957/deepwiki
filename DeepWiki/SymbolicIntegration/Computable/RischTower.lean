import DeepWiki.SymbolicIntegration.Computable.IntegratorAssembly

/-! # `LawfulRischLevel` — the one Risch-solver abstraction (write one instance, assembled)

The single abstraction for the assembled Risch integrator: the `X` / `LawfulX` idiom. The per-level
obligations — computable data (`case` + `candidates`) and the soundness/completeness laws — are the fields
of a **class** `LawfulRischLevel α`. Materialize **one** instance and the whole solver assembles by
resolution, parameter-free: `LawfulRischLevel.integrate` / `.sound` / `.isElementaryIntegrable_of_run` /
`.not_isElementaryIntegrable`, wherever `[LawfulRischLevel α]` is in scope.

Because the tower carriers iterate generically (`CField`/`CDiffField`/`CRischField`/`CFracGcdCoreWf` of
`QFunNZG β` are recursive instances), a recursive instance
`[LawfulRischLevel α] → LawfulRischLevel (QFunNZG α)` (the tower step) makes solvers at *every* depth resolve
automatically — base and step each written once. See `docs/recursive-risch-solver.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The Risch solver as a class.** The computable data (`case` + `candidates`) and the
soundness/completeness laws (`specialSound` carrying the special value existentially, `reducedSound`, and
the completeness contract `SpecElem`/`NrmElem`/`descend`). One `instance` assembles the solver and
everything derived from it by resolution — no threaded parameters. -/
class LawfulRischLevel (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] where
  /-- The per-monomial-case computable hooks for this level. -/
  case : MonomialCase α
  /-- The level's residue-candidate generator (so the integrator takes no `cands` argument). -/
  candidates : CPolyG α → CPolyG α → CPolyG α → List α
  /-- Special-part soundness + reconstruction (existential special value — no stored `RatFunc` data). -/
  specialSound : ∀ (Dt a d snum sden : CPolyG α),
    case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
    toPolyG sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDerivG Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d
  /-- Reduced-part soundness: a corrected normal part is an antiderivative of `cₙ/dₙ`. -/
  reducedSound : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α),
    case.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
    toPolyG nrm.rational.2 ≠ 0 ∧ IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm
  /-- Special-part elementarity obstruction (completeness frontier). -/
  SpecElem : CPolyG α → CPolyG α → CPolyG α → Prop
  /-- Normal-part elementarity obstruction (completeness frontier). -/
  NrmElem : CPolyG α → CPolyG α → CPolyG α → Prop
  /-- Completeness descent law: elementary integrability descends to the two part obligations. -/
  descend : ∀ (Dt a d : CPolyG α),
    IsElementaryIntegrableG Dt a d → SpecElem Dt a d ∧ NrmElem Dt a d

namespace LawfulRischLevel

/-- **The assembled integrator** — a function of `(Dt, a, d)` alone (the candidate list is the instance's
`candidates`). Parameter-free: the case hooks come from the `[LawfulRischLevel α]` instance. -/
def integrate [LawfulRischLevel α] (Dt a d : CPolyG α) : Option (IntegralResultG α) :=
  cIntegrateCase case Dt a d (candidates Dt a d)

/-- **Derived soundness.** Any successful run is an antiderivative of `a/d`, composed from the instance's
laws through the abstract core `cIntegrateCase_sound`. No threaded hypotheses. -/
theorem sound [LawfulRischLevel α] (Dt a d : CPolyG α) (res : IntegralResultG α)
    (h : integrate Dt a d = some res) : IsIntegralResultG Dt a d res := by
  rw [integrate] at h
  set cands := candidates Dt a d with hcands
  have h0 : cIntegrateCase case Dt a d cands = some res := h
  rw [cIntegrateCase] at h
  rcases hcrep : canonicalRepresentationFastGWf Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
  rw [hcrep] at h
  dsimp only at h
  rcases hspec : case.integrateSpecial Dt fp b ds with _ | ⟨snum, sden⟩
  · rw [hspec] at h; simp at h
  · rw [hspec] at h
    rcases hcorr : case.reducedCorrect Dt (cIntegrateReducedGWf Dt cn dn cands) with _ | nrm
    · rw [hcorr] at h; simp at h
    · rw [hcorr] at h
      have hSpec : case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d)
          = some (snum, sden) := by
        simp only [crPoly, crSpecNum, crSpecDen, hcrep]; exact hspec
      have hCorr : case.reducedCorrect Dt (redNorm Dt a d cands) = some nrm := by
        simp only [redNorm, crNormNum, crNormDen, hcrep]; exact hcorr
      obtain ⟨hsden, v, hSpecField, hrecon⟩ := specialSound Dt a d snum sden hSpec
      obtain ⟨hgden, hNrmField⟩ := reducedSound Dt a d cands nrm hCorr
      exact cIntegrateCase_sound case Dt a d cands res snum sden nrm v
        hsden hgden hSpec hCorr h0 hSpecField hNrmField hrecon

/-- **Derived constructive completeness.** A successful run certifies `a/d` is elementary integrable. -/
theorem isElementaryIntegrable_of_run [LawfulRischLevel α] (Dt a d : CPolyG α)
    (res : IntegralResultG α) (h : integrate Dt a d = some res) : IsElementaryIntegrableG Dt a d :=
  IsElementaryIntegrableG.of_isIntegralResult (sound Dt a d res h)

/-- **Derived completeness frontier.** A certified obstruction in either part makes `a/d` non-elementary. -/
theorem not_isElementaryIntegrable [LawfulRischLevel α] (Dt a d : CPolyG α)
    (hobstruct : ¬ SpecElem Dt a d ∨ ¬ NrmElem Dt a d) : ¬ IsElementaryIntegrableG Dt a d :=
  not_isElementaryIntegrableG_of_obstruction Dt a d (descend Dt a d) hobstruct

end LawfulRischLevel

end DeepWiki.SymbolicIntegration
