import DeepWiki.SymbolicIntegration.Computable.RischSolverRec
import DeepWiki.SymbolicIntegration.Computable.IntegratorCases

/-! # The primitive base of the recursion (`SubSolver.primitive`, `RischSolverPrimitive`)

The bottom of the recursive tower: `SubSolver.primitive` is the primitive-case (`Dθ ∈ k`) special-part
capability, and `RischSolverPrimitive` assembles it into a full closed-form `RischSolver` via
`RischSolver.ofSub`. The special-part law is proven internally — unfolding `primitiveCase.integrateSpecial`
(the `b = 0` guard + poly-RDE `some qₚ` match), the `[CField.one]` denominator nonzero, and the existential
value `v := ⟦fₚ⟧` — from the two named frontier facts:

* `hspecialField` — the poly-RDE identity `D(⟦qₚ⟧) = ⟦fₚ⟧` (canonical `Dt = 1` regime via
  `cPolyRischDEGWf_nil_field_identity`, needs `CharZero` + `mapCoeffs fₚ = 0`);
* `hrecon` — reconstruction `⟦fₚ⟧ + ⟦cₙ/dₙ⟧ = ⟦a/d⟧` (via `canonicalReconstruction`, modulo the split
  frontier).

`hreduced` (reduced-part, via the interfaces / `native_decide` frontier) and `SpecElem`/`NrmElem`/`hdescend`
(Liouville frontier) are the remaining named walls. See `docs/recursive-risch-solver.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The base `SubSolver`: the primitive case.** The special-part capability at the bottom of the tower.
Its `special` law is discharged from the poly-RDE identity `hspecialField` (special value `⟦fₚ⟧`) and the
reconstruction `hrecon`. -/
def SubSolver.primitive
    (hspecialField : ∀ (Dt a d qp : CPolyG α),
      cisZeroG (crSpecNum Dt a d) = true →
      cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) = some qp →
      towerFractionFieldDerivG Dt (fieldFrac qp [CField.one]) = fieldFrac (crPoly Dt a d) [CField.one])
    (hrecon : ∀ (Dt a d : CPolyG α),
      fieldFrac (crPoly Dt a d) [CField.one] + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d)
        = fieldFrac a d) :
    SubSolver α primitiveCase where
  special := by
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

/-- **The assembled primitive Risch solver.** `RischSolver.ofSub` applied to the base `SubSolver.primitive`,
with this level's reduced-part (`hreduced`) and completeness contract (`SpecElem`/`NrmElem`/`hdescend`).
Computable data (`case = primitiveCase` + `candidates`); soundness/completeness via the derived API. -/
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
    RischSolver α :=
  RischSolver.ofSub (SubSolver.primitive hspecialField hrecon) candidates SpecElem NrmElem hreduced hdescend

end DeepWiki.SymbolicIntegration
