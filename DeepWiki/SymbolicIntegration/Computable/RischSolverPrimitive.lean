import DeepWiki.SymbolicIntegration.Computable.RischTower
import DeepWiki.SymbolicIntegration.Computable.IntegratorCases

/-! # The primitive base as a resolved instance (`PrimitiveFrontier` ⇒ `LawfulRischLevel`)

The primitive-case (`Dθ ∈ k`) base of the tower, packaged so **no hypotheses are threaded**. The engine
frontier facts are the fields of one class, `PrimitiveFrontier α` (materialized *once*); from it, the
`LawfulRischLevel α` instance — and hence the assembled `integrate` / `sound` / completeness — resolve
**automatically**, parameter-free, wherever `[PrimitiveFrontier α]` is in scope. The special-part law is
proven inside the instance (unfolding `primitiveCase.integrateSpecial`); the frontier facts stay isolated in
`PrimitiveFrontier`:

* `hspecialField` — the poly-RDE identity (canonical `Dt = 1` regime, `cPolyRischDEGWf_nil_field_identity`);
* `hrecon` — reconstruction (`canonicalReconstruction`, modulo the split frontier);
* `hreduced` — reduced-part soundness (the `native_decide` Hermite/residue frontier);
* `SpecElem`/`NrmElem`/`hdescend` — the Liouville completeness contract.

See `docs/recursive-risch-solver.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The primitive-case engine frontier, as a class.** Bundle the named frontier facts once; the
`LawfulRischLevel` instance (hence the whole solver) then resolves from `[PrimitiveFrontier α]` with no
threaded parameters. -/
class PrimitiveFrontier (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] where
  /-- The level's residue-candidate generator. -/
  candidates : CPolyG α → CPolyG α → CPolyG α → List α
  /-- Poly-RDE identity: the `b = 0` RDE output `qₚ` differentiates back to `⟦fₚ⟧`. -/
  hspecialField : ∀ (Dt a d qp : CPolyG α),
    cisZeroG (crSpecNum Dt a d) = true →
    cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) = some qp →
    towerFractionFieldDerivG Dt (fieldFrac qp [CField.one]) = fieldFrac (crPoly Dt a d) [CField.one]
  /-- Canonical reconstruction: `⟦fₚ⟧ + ⟦cₙ/dₙ⟧ = ⟦a/d⟧`. -/
  hrecon : ∀ (Dt a d : CPolyG α),
    fieldFrac (crPoly Dt a d) [CField.one] + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d)
      = fieldFrac a d
  /-- Reduced-part soundness (the shared Hermite/residue frontier). -/
  hreduced : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α),
    primitiveCase.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
    toPolyG nrm.rational.2 ≠ 0 ∧ IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm
  /-- Special-part elementarity obstruction (completeness frontier). -/
  SpecElem : CPolyG α → CPolyG α → CPolyG α → Prop
  /-- Normal-part elementarity obstruction (completeness frontier). -/
  NrmElem : CPolyG α → CPolyG α → CPolyG α → Prop
  /-- Completeness descent (the Liouville frontier). -/
  hdescend : ∀ (Dt a d : CPolyG α),
    IsElementaryIntegrableG Dt a d → SpecElem Dt a d ∧ NrmElem Dt a d

/-- **The primitive `LawfulRischLevel` instance — assembled from `PrimitiveFrontier` by resolution.**
Materialize one `PrimitiveFrontier α` and the whole solver (`LawfulRischLevel.integrate` / `.sound` /
completeness) resolves automatically, parameter-free. The `specialSound` law is proven here from the
frontier's `hspecialField` + `hrecon` (unfolding `primitiveCase.integrateSpecial`). -/
instance instLawfulRischLevelPrimitive [PrimitiveFrontier α] : LawfulRischLevel α where
  case := primitiveCase
  candidates := PrimitiveFrontier.candidates
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
        refine ⟨?_, fieldFrac (crPoly Dt a d) [CField.one],
          PrimitiveFrontier.hspecialField Dt a d qp hb hqp, PrimitiveFrontier.hrecon Dt a d⟩
        rw [show toPolyG ([CField.one] : CPolyG α) = 1 from by
          rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]]
        exact one_ne_zero
    · rw [if_neg hb] at hhook; simp at hhook
  reducedSound := PrimitiveFrontier.hreduced
  SpecElem := PrimitiveFrontier.SpecElem
  NrmElem := PrimitiveFrontier.NrmElem
  descend := PrimitiveFrontier.hdescend

end DeepWiki.SymbolicIntegration
