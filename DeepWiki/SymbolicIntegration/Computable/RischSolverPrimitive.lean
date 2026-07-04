import DeepWiki.SymbolicIntegration.Computable.RischSolver
import DeepWiki.SymbolicIntegration.Computable.IntegratorCases

/-! # The primitive Risch solver, assembled (`RischSolverPrimitive`)

A concrete `RischSolver` for the **primitive case** (`Dθ ∈ k`), with `case := primitiveCase` wired in. The
`specialSound` field is discharged *internally*: unfolding `primitiveCase.integrateSpecial` (the `b = 0`
guard + poly-RDE `some qₚ` match), proving the `[CField.one]` denominator is nonzero, and supplying the
existential special value `v := ⟦fₚ⟧` from the two named frontier facts —

* `hspecialField` — the poly-RDE identity `D(⟦qₚ⟧) = ⟦fₚ⟧` (discharged in the canonical `Dt = 1` regime by
  `cPolyRischDEGWf_nil_field_identity`, which needs `CharZero` + the primitive condition `mapCoeffs fₚ = 0`);
* `hrecon` — the reconstruction `⟦fₚ⟧ + ⟦cₙ/dₙ⟧ = ⟦a/d⟧` (discharged by `canonicalReconstruction`, modulo the
  `cSplitFactorFastGWf` split frontier).

`hreduced` is the reduced-part soundness (via `cIntegrateReducedGWf_primitive_isIntegralResult_via_interfaces`,
modulo the `native_decide` Hermite/residue compute frontier) and `SpecElem`/`NrmElem`/`hdescend` are the
completeness contract (the Liouville frontier). The bundle is computable data (`case` + `candidates`); the
denotation machinery stays in `Prop`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The assembled primitive Risch solver.** `case := primitiveCase`; `specialSound` proven internally from
the poly-RDE regime fact `hspecialField` (special value `⟦fₚ⟧`) and reconstruction `hrecon`. The reduced-part
(`hreduced`) and completeness-descent (`SpecElem`/`NrmElem`/`hdescend`) obligations are the remaining named
frontiers. Computable (no `noncomputable`): the bundle stores only `case` + `candidates`. -/
def RischSolverPrimitive
    (candidates : CPolyG α → CPolyG α → CPolyG α → List α)
    (SpecElem NrmElem : CPolyG α → CPolyG α → CPolyG α → Prop)
    (hspecialField : ∀ (Dt a d qp : CPolyG α),
      cisZeroG (crSpecNum Dt a d) = true →
      cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) = some qp →
      towerFractionFieldDerivG Dt (fieldFrac qp [CField.one]) = fieldFrac (crPoly Dt a d) [CField.one])
    (hrecon : ∀ (Dt a d : CPolyG α),
      fieldFrac (crPoly Dt a d) [CField.one] + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d)
        = fieldFrac a d)
    (hreduced : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α),
      primitiveCase.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
      toPolyG nrm.rational.2 ≠ 0 ∧ IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm)
    (hdescend : ∀ (Dt a d : CPolyG α),
      IsElementaryIntegrableG Dt a d → SpecElem Dt a d ∧ NrmElem Dt a d) :
    RischSolver α where
  case := primitiveCase
  candidates := candidates
  specialSound := by
    intro Dt a d snum sden hhook
    simp only [primitiveCase] at hhook
    by_cases hb : cisZeroG (crSpecNum Dt a d) = true
    · rw [if_pos hb] at hhook
      rcases hqp : cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) with _ | qp
      · rw [hqp] at hhook; simp at hhook
      · rw [hqp] at hhook
        simp only [Option.some.injEq, Prod.mk.injEq] at hhook
        obtain ⟨rfl, rfl⟩ := hhook
        refine ⟨?_, fieldFrac (crPoly Dt a d) [CField.one], hspecialField Dt a d qp hb hqp,
          hrecon Dt a d⟩
        rw [show toPolyG ([CField.one] : CPolyG α) = 1 from by
          rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]]
        exact one_ne_zero
    · rw [if_neg hb] at hhook; simp at hhook
  reducedSound := hreduced
  SpecElem := SpecElem
  NrmElem := NrmElem
  descend := hdescend

end DeepWiki.SymbolicIntegration
