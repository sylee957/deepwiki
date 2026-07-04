import DeepWiki.SymbolicIntegration.Computable.RischSolver
import DeepWiki.SymbolicIntegration.Computable.IntegratorCases

/-! # The primitive Risch solver, assembled (`RischSolverPrimitive`)

A concrete `RischSolver` for the **primitive case** (`Dθ ∈ k`), with `case := primitiveCase` wired in and the
special-part soundness law discharged *internally* from the poly-RDE identity: the caller supplies only the
per-input primitive-regime fact `hspecialField` (the `b = 0` RDE output `qₚ` differentiates back to the
polynomial part `⟦fₚ⟧`), and the assembled solver's `specialSound` field is proven from it plus the fixed
`specialVal := ⟦fₚ⟧`. The reduced-part, reconstruction, and completeness-descent obligations remain honest
hypotheses (`hreduced`/`hrecon`/`hdescend`) — the shared Hermite/residue and split frontiers. Materializing
those yields the primitive integrator with soundness/completeness via the derived `RischSolver.*` API. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The assembled primitive Risch solver.** `case := primitiveCase`, `specialVal := ⟦fₚ⟧`; the
`specialSound` field is discharged from the poly-RDE regime fact `hspecialField`. The reduced-part
(`hreduced`), reconstruction (`hrecon`), and completeness-descent (`SpecElem`/`NrmElem`/`hdescend`)
obligations are the remaining frontier hypotheses. -/
noncomputable def RischSolverPrimitive
    (candidates : CPolyG α → CPolyG α → CPolyG α → List α)
    (SpecElem NrmElem : CPolyG α → CPolyG α → CPolyG α → Prop)
    (hspecialField : ∀ (Dt a d qp : CPolyG α),
      cisZeroG (crSpecNum Dt a d) = true →
      cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) = some qp →
      towerFractionFieldDerivG Dt (fieldFrac qp [CField.one]) = fieldFrac (crPoly Dt a d) [CField.one])
    (hreduced : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α),
      primitiveCase.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
      toPolyG nrm.rational.2 ≠ 0 ∧ IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm)
    (hrecon : ∀ (Dt a d : CPolyG α),
      fieldFrac (crPoly Dt a d) [CField.one] + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d)
        = fieldFrac a d)
    (hdescend : ∀ (Dt a d : CPolyG α),
      IsElementaryIntegrableG Dt a d → SpecElem Dt a d ∧ NrmElem Dt a d) :
    RischSolver α where
  case := primitiveCase
  candidates := candidates
  specialVal := fun Dt a d => fieldFrac (crPoly Dt a d) [CField.one]
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
        refine ⟨?_, hspecialField Dt a d qp hb hqp⟩
        rw [show toPolyG ([CField.one] : CPolyG α) = 1 from by
          rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]]
        exact one_ne_zero
    · rw [if_neg hb] at hhook; simp at hhook
  reducedSound := hreduced
  recon := hrecon
  SpecElem := SpecElem
  NrmElem := NrmElem
  descend := hdescend

end DeepWiki.SymbolicIntegration
