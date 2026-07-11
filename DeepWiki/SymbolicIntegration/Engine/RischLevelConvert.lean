import DeepWiki.ComputableAlgebra.PolyReprConvert
import DeepWiki.SymbolicIntegration.Engine.RischLevel

/-! # Risch-level representation conversion

One represented Risch solver can be exposed through another polynomial representation without changing
the denotation of its inputs and outputs. -/

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

/-- Representation conversion preserves certified normal-result witnesses. -/
theorem certifiedNormalResult_convert (Dt a d : P α) (res : IntegralResult α P)
    (h : CertifiedNormalResult Dt a d res) :
    CertifiedNormalResult (CPolyEngine.convert Dt : Q α) (CPolyEngine.convert a)
      (CPolyEngine.convert d) (convertIntegralResult res) where
  integral := isIntegralResultP_convert Dt a d res h.integral
  rationalDen_nonzero := by
    simpa only [convertIntegralResult, CPolyEngine.toPoly_convert] using h.rationalDen_nonzero
  coefficients_constant := by
    intro cv hcv
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hcv
    exact h.coefficients_constant source hsource
  arguments_nonzero := by
    intro cv hcv
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hcv
    simpa only [CPolyEngine.toPoly_convert] using h.arguments_nonzero source hsource

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

end DeepWiki.SymbolicIntegration
