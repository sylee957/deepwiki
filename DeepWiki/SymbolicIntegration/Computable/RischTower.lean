import DeepWiki.SymbolicIntegration.Computable.IntegratorAssembly

/-! # `LawfulRischLevel` — the one Risch-solver abstraction (write one instance, assembled)

The single abstraction for the assembled Risch integrator: the `X` / `LawfulX` idiom. The per-level
obligations — computable data (`case` + `candidates`), the soundness laws (`specialSound`, `reducedSound`),
and the **residue guard** `caseGuardsResidues` — are the fields of a **class** `LawfulRischLevel α`.
Materialize **one** instance and the whole solver assembles by resolution, parameter-free:
`LawfulRischLevel.integrate` / `.sound` / `.isElementaryIntegrable_of_run`, wherever `[LawfulRischLevel α]` is
in scope.

The derived `sound` certifies a **genuine** integral result (`IsGenuineIntegralResultG`) — the formal
log-derivative identity *plus* all residues constant — so a successful run is a true antiderivative, not merely
a formal identity. The residue-constancy comes from `caseGuardsResidues` (the case's `reducedCorrect` is a real
integrability guard, e.g. `primitiveGuardedCase`). **Completeness** — a decidable non-integrability certificate
— is decoupled into `LiouvilleFrontier` (`LiouvilleCompleteness.lean`), so soundness resolution never depends
on the completeness frontier.

Because the tower carriers iterate generically (`CField`/`CDiffField`/`CRischField`/`CFracGcdCoreWf` of
`QFunNZG β` are recursive instances), a recursive instance
`[LawfulRischLevel α] → LawfulRischLevel (QFunNZG α)` (the tower step) makes solvers at *every* depth resolve
automatically — base and step each written once. See `docs/recursive-risch-solver.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The Risch solver as a class.** The computable data (`case` + `candidates`), the soundness laws
(`specialSound` carrying the special value existentially, `reducedSound`), and the residue guard
(`caseGuardsResidues` — the case's `reducedCorrect` only accepts constant-residue results). One `instance`
assembles the solver and everything derived from it by resolution — no threaded parameters. The derived
`sound` is **genuine** (`IsGenuineIntegralResultG`); completeness lives in `LiouvilleFrontier`. -/
class LawfulRischLevel (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] where
  /-- The per-monomial-case computable hooks for this level. -/
  case : MonomialCase α
  /-- The level's residue-candidate generator (so the integrator takes no `cands` argument). -/
  candidates : CPolyG α → CPolyG α → CPolyG α → List α
  /-- Special-part soundness + reconstruction (existential special value — no stored `RatFunc` data). The
  `d ≠ 0` precondition is *supplied by the integrator's guard*, so it is not a materialization burden. -/
  specialSound : ∀ (Dt a d snum sden : CPolyG α), toPolyG d ≠ 0 →
    case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
    toPolyG sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDerivG Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d
  /-- Reduced-part soundness: a corrected normal part is an antiderivative of `cₙ/dₙ`. The `d ≠ 0`
  precondition is supplied by the integrator's guard. -/
  reducedSound : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α), toPolyG d ≠ 0 →
    case.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
    toPolyG nrm.rational.2 ≠ 0 ∧ IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm
  /-- The case's `reducedCorrect` is a real **integrability guard**: it only accepts constant-residue reduced
  results. This upgrades the derived soundness from the formal identity to a *genuine* antiderivative. -/
  caseGuardsResidues : CaseGuardsResidues case

namespace LawfulRischLevel

/-- **The assembled integrator** — a function of `(Dt, a, d)` alone (the candidate list is the instance's
`candidates`). Parameter-free: the case hooks come from the `[LawfulRischLevel α]` instance. **Guards on
`d ≠ 0`** (declines the degenerate `a/0`), so a successful run supplies `d ≠ 0` to the soundness laws. -/
def integrate [LawfulRischLevel α] (Dt a d : CPolyG α) : Option (IntegralResultG α) :=
  if cisZeroG d then none else cIntegrateCase case Dt a d (candidates Dt a d)

/-- **Formal soundness.** Any successful run satisfies the formal (log-derivative) integral identity,
composed from the instance's laws through the abstract core `cIntegrateCase_sound`. -/
theorem soundFormal [LawfulRischLevel α] (Dt a d : CPolyG α) (res : IntegralResultG α)
    (h : integrate Dt a d = some res) : IsIntegralResultG Dt a d res := by
  rw [integrate] at h
  by_cases hdz : cisZeroG d = true
  · rw [if_pos hdz] at h; simp at h
  · rw [if_neg hdz] at h
    have hd0 : toPolyG d ≠ 0 := fun hh => hdz ((cisZeroG_iff d).mpr hh)
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
        obtain ⟨hsden, v, hSpecField, hrecon⟩ := specialSound Dt a d snum sden hd0 hSpec
        obtain ⟨hgden, hNrmField⟩ := reducedSound Dt a d cands nrm hd0 hCorr
        exact cIntegrateCase_sound case Dt a d cands res snum sden nrm v
          hsden hgden hSpec hCorr h0 hSpecField hNrmField hrecon

/-- **All residues of a successful run are constant** — the corrected normal part came through the case's
residue guard (`caseGuardsResidues`), and the combined result keeps that log part (`combineSN`). -/
theorem allResiduesConstant_of_run [LawfulRischLevel α] (Dt a d : CPolyG α) (res : IntegralResultG α)
    (h : integrate Dt a d = some res) : AllResiduesConstantG res := by
  rw [integrate] at h
  by_cases hdz : cisZeroG d = true
  · rw [if_pos hdz] at h; simp at h
  · rw [if_neg hdz] at h
    set cands := candidates Dt a d with hcands
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
        simp only [Option.some.injEq] at h
        have hlogs : res.logs = nrm.logs := by rw [← h]; rfl
        have hnrm := caseGuardsResidues Dt (cIntegrateReducedGWf Dt cn dn cands) nrm hcorr
        unfold AllResiduesConstantG at hnrm ⊢
        rw [hlogs]; exact hnrm

/-- **Genuine soundness.** Any successful run is a *genuine* integral result — the formal identity
(`soundFormal`) plus all residues constant (`allResiduesConstant_of_run`) — so `⟦g⟧ + Σ cᵢ·log vᵢ` is a true
antiderivative of `a/d`, not merely a formal log-derivative identity. -/
theorem sound [LawfulRischLevel α] (Dt a d : CPolyG α) (res : IntegralResultG α)
    (h : integrate Dt a d = some res) : IsGenuineIntegralResultG Dt a d res :=
  ⟨soundFormal Dt a d res h, allResiduesConstant_of_run Dt a d res h⟩

/-- **Derived constructive completeness.** A successful run certifies `a/d` is *genuinely* elementary
integrable (an antiderivative in the Liouville form with constant residues). -/
theorem isElementaryIntegrable_of_run [LawfulRischLevel α] (Dt a d : CPolyG α)
    (res : IntegralResultG α) (h : integrate Dt a d = some res) : IsElementaryIntegrableGenuineG Dt a d :=
  IsElementaryIntegrableGenuineG.of_isGenuineIntegralResult (sound Dt a d res h)

/-- **Limited integration (rational, base-level)** — `integrate` restricted to log-free results. Because the
rational solver's `IsIntegralResultG` is a **base-level (`K`)** identity (not `∀E` like the LRT one), its
log-free specialization needs **no algebraic-closure descent** — making it the right coefficient integrator for
the tower recursion. -/
def integrateRational [LawfulRischLevel α] (Dt a d : CPolyG α) : Option (CPolyG α × CPolyG α) :=
  (integrate Dt a d).bind fun r => if r.logs.isEmpty then some r.rational else none

/-- **K-level rational-antiderivative soundness** — a log-free `integrateRational` run gives
`D_tower(num/den) = a/d` directly in `RatFunc (CFieldSpec.K α)`, no `∀E` descent (`IsIntegralResultG` is
already base-level; the empty log part drops via `logResidueSumG_nil`). This is the `intR` the tower
coefficient recursion needs on solid ground. -/
theorem integrateRational_sound [LawfulRischLevel α] (Dt a d num den : CPolyG α)
    (h : integrateRational Dt a d = some (num, den)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG num) / amG α (toPolyG den))
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  unfold integrateRational at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨r, hint, hguard⟩ := h
  split at hguard
  · rename_i hemp
    have hrat : r.rational = (num, den) := (Option.some.injEq _ _).mp hguard
    have hlogs : r.logs = [] := List.isEmpty_iff.mp hemp
    have hgen := (sound Dt a d r hint).1
    unfold IsIntegralResultG at hgen
    rw [hlogs, logResidueSumG_nil, add_zero, hrat] at hgen
    exact hgen
  · exact absurd hguard (by simp)

end LawfulRischLevel

end DeepWiki.SymbolicIntegration
