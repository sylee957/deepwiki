import DeepWiki.ComputableAlgebra.PolyReprConvert
import DeepWiki.SymbolicIntegration.Engine.RischLevel

/-! # Risch-level representation conversion

One represented Risch solver can be exposed through another polynomial representation without changing
denotation, soundness, or relative completeness. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u

variable {P Q : Type u → Type u}
  [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
  [CPoly Q] [CPolyEngine Q] [LawfulCPolyEngine.{u,u} Q]
variable {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec.{u,u} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Convert every represented polynomial in an integral result. -/
def convertIntegralResult (res : IntegralResult α P) : IntegralResult α Q :=
  { rational := (CPolyEngine.convert res.rational.1, CPolyEngine.convert res.rational.2)
    logs := res.logs.map fun cv => (cv.1, CPolyEngine.convert cv.2) }

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- Representation conversion preserves the generic logarithmic residue sum. -/
theorem logResidueSumP_convert (Dt : P α) (logs : List (α × P α)) :
    logResidueSumP (CPolyEngine.convert Dt : Q α)
        (logs.map fun cv => (cv.1, CPolyEngine.convert cv.2)) =
      logResidueSumP Dt logs := by
  rw [logResidueSumP, logResidueSumP, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro cv _
  simp only [Function.comp_apply, CPolyEngine.toPoly_convert,
    CPolyEngine.toPoly_monomialDeriv]

/-- Representation conversion preserves an integral-result certificate. -/
theorem isIntegralResultP_convert (Dt a d : P α) (res : IntegralResult α P)
    (h : IsIntegralResultP Dt a d res) :
    IsIntegralResultP (CPolyEngine.convert Dt : Q α) (CPolyEngine.convert a)
      (CPolyEngine.convert d) (convertIntegralResult res) := by
  simpa only [IsIntegralResultP, convertIntegralResult, CPolyEngine.toPoly_convert,
    logResidueSumP_convert, towerFractionFieldDerivP] using h

/-- Representation conversion preserves genuine one-level Liouville witnesses. -/
theorem isRischLevelIntegrable_convert (Dt a d : P α)
    (h : IsRischLevelIntegrable Dt a d) :
    IsRischLevelIntegrable (CPolyEngine.convert Dt : Q α) (CPolyEngine.convert a)
      (CPolyEngine.convert d) := by
  rcases h with ⟨res, hres, hconst, hden⟩
  refine ⟨convertIntegralResult (Q := Q) res, isIntegralResultP_convert Dt a d res hres, ?_, ?_⟩
  · intro cv hcv
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hcv
    exact hconst source hsource
  · intro cv hcv
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hcv
    simpa only [CPolyEngine.toPoly_convert] using hden source hsource

/-- Expose a Risch-level solver through another polynomial representation. -/
def convertRischLevel (L : CRischLevel P α) : CRischLevel Q α where
  integrate fuel Dt a d :=
    (L.integrate fuel (CPolyEngine.convert Dt) (CPolyEngine.convert a)
      (CPolyEngine.convert d)).map (convertIntegralResult (Q := Q))

/-- Pull a Risch-level domain back along representation conversion. -/
def convertRischLevelDomain (domain : RischLevelDomain P α) : RischLevelDomain Q α :=
  fun Dt a d => domain (CPolyEngine.convert Dt) (CPolyEngine.convert a) (CPolyEngine.convert d)

set_option maxHeartbeats 3000000 in
/-- A lawful Risch level remains lawful through denotation-preserving representation conversion. -/
instance instLawfulCRischLevelConvert (L : CRischLevel P α) (domain : RischLevelDomain P α)
    [LawfulCRischLevel L domain] :
    LawfulCRischLevel (convertRischLevel (Q := Q) L) (convertRischLevelDomain domain) where
  sound fuel Dt a d res hdomain hd hrun := by
    change (L.integrate fuel (CPolyEngine.convert Dt) (CPolyEngine.convert a)
      (CPolyEngine.convert d)).map (convertIntegralResult (Q := Q)) = some res at hrun
    change domain (CPolyEngine.convert Dt) (CPolyEngine.convert a)
      (CPolyEngine.convert d) at hdomain
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨sourceRes, hsource, rfl⟩ := hrun
    have hdSource : CPoly.toPoly (CPolyEngine.convert d : P α) ≠ 0 := by
      simpa only [CPolyEngine.toPoly_convert] using hd
    have h := LawfulCRischLevel.sound fuel (CPolyEngine.convert Dt)
      (CPolyEngine.convert a) (CPolyEngine.convert d) sourceRes hdomain hdSource hsource
    exact isIntegralResultP_convert (Q := Q) _ _ _ _ h

set_option maxHeartbeats 3000000 in
/-- A relatively complete Risch level remains relatively complete through representation conversion. -/
instance instCompleteCRischLevelConvert (L : CRischLevel P α) (domain : RischLevelDomain P α)
    [LawfulCRischLevel L domain]
    [LawfulCRischLevel (convertRischLevel (Q := Q) L) (convertRischLevelDomain domain)]
    [CompleteCRischLevel L domain] :
    CompleteCRischLevel (convertRischLevel (Q := Q) L) (convertRischLevelDomain domain) where
  relative_complete Dt a d hdomain hd hintegrable := by
    have hsourceIntegrable := isRischLevelIntegrable_convert (P := Q) (Q := P) Dt a d hintegrable
    have hdSource : CPoly.toPoly (CPolyEngine.convert d : P α) ≠ 0 := by
      simpa only [CPolyEngine.toPoly_convert] using hd
    obtain ⟨fuel, sourceRes, hrun⟩ := CompleteCRischLevel.relative_complete
      (L := L) (domain := domain) (CPolyEngine.convert Dt) (CPolyEngine.convert a)
        (CPolyEngine.convert d) hdomain hdSource hsourceIntegrable
    refine ⟨fuel, convertIntegralResult (Q := Q) sourceRes, ?_⟩
    change (L.integrate fuel (CPolyEngine.convert Dt) (CPolyEngine.convert a)
      (CPolyEngine.convert d)).map (convertIntegralResult (Q := Q)) = some _
    simpa only [Option.map_some] using congrArg (Option.map (convertIntegralResult (Q := Q))) hrun

end DeepWiki.SymbolicIntegration
