import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitive

/-! # Genuine soundness — the guard upgrades formal to genuine integral results

`LawfulRischLevel.sound` produces the *formal* `IsIntegralResultG` (the log-derivative identity). When the
case's `reducedCorrect` is a real **integrability guard** (`CaseGuardsResidues` — a successful reduced
correction forces all residues constant, as `primitiveGuardedCase`/`hyperexpCase` do), a successful run's
residues are constants, so the result is a *genuine* integral result (`IsGenuineIntegralResultG`) — a true
antiderivative, not just a formal identity. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- **A monomial case guards residues**: whenever its `reducedCorrect` accepts a reduced result, that result
has all residues constant (`AllResiduesConstantG`). The guarded primitive and hyperexp cases satisfy this; a
no-op `reducedCorrect _ nrm := some nrm` would not. This is the property that makes a successful run's output
a *genuine* (not merely formal) integral result. -/
def CaseGuardsResidues (C : MonomialCase α) : Prop :=
  ∀ (Dt : CPolyG α) (nrm nrm' : IntegralResultG α),
    C.reducedCorrect Dt nrm = some nrm' → AllResiduesConstantG nrm'

omit [CFieldSpec α] [CDiffFieldSpec α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]
  [CharZero (CFieldSpec.K α)] in
/-- **The guarded primitive case guards residues.** Its `reducedCorrect` accepts iff every residue is constant
(`nrm.logs.all (cisZeroG [D cᵢ])`), which is exactly `AllResiduesConstantG`. -/
theorem primitiveGuardedCase_guardsResidues :
    CaseGuardsResidues (primitiveGuardedCase : MonomialCase α) := by
  intro Dt nrm nrm' hcorr
  simp only [primitiveGuardedCase] at hcorr
  split at hcorr
  · rename_i hguard
    injection hcorr with h'
    subst h'
    exact hguard
  · exact absurd hcorr (by simp)

namespace LawfulRischLevel

omit [CharZero (CFieldSpec.K α)] in
/-- **Genuine soundness.** If the level's case guards residues (`hCG`), then any successful `integrate` run
returns a *genuine* integral result: the formal identity from `sound`, plus all residues constant (the
combined result's logs are the guarded reduced result's logs). -/
theorem sound_genuine [LawfulRischLevel α] (hCG : CaseGuardsResidues (case : MonomialCase α))
    (Dt a d : CPolyG α) (res : IntegralResultG α) (h : integrate Dt a d = some res) :
    IsGenuineIntegralResultG Dt a d res := by
  refine ⟨sound Dt a d res h, ?_⟩
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
        have hnrm := hCG Dt (cIntegrateReducedGWf Dt cn dn cands) nrm hcorr
        unfold AllResiduesConstantG at hnrm ⊢
        rw [hlogs]; exact hnrm

end LawfulRischLevel

/-- **The primitive solver's genuine soundness.** For `[PrimitiveFrontier α]`, a successful primitive-solver
run returns a genuine integral result (the guard forces constant residues). Hence a genuine
`IsElementaryIntegrableGenuineG` witness. -/
theorem instLawfulRischLevelPrimitive_sound_genuine [Fact (GcdFFCorrect (α := α))] [PrimitiveFrontier α]
    (Dt a d : CPolyG α) (res : IntegralResultG α) (h : LawfulRischLevel.integrate Dt a d = some res) :
    IsGenuineIntegralResultG Dt a d res :=
  LawfulRischLevel.sound_genuine primitiveGuardedCase_guardsResidues Dt a d res h

end DeepWiki.SymbolicIntegration
