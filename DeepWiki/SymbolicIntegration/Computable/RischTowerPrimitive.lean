import DeepWiki.SymbolicIntegration.Computable.RischTower
import DeepWiki.SymbolicIntegration.Computable.IntegratorCases
import DeepWiki.SymbolicIntegration.Computable.CanonicalReconstructionCharZero

/-! # The primitive base as a resolved instance (`PrimitiveFrontier` ⇒ `LawfulRischLevel`)

The primitive-case (`Dθ ∈ k`) base of the tower, packaged so **no hypotheses are threaded**. The engine
frontier facts are the fields of one class, `PrimitiveFrontier α` (materialized *once*); from it, the
`LawfulRischLevel α` instance — and hence the assembled `integrate` / `sound` / completeness — resolve
**automatically**, parameter-free, wherever `[PrimitiveFrontier α]` is in scope. The special-part law and the
**reconstruction** are proven inside the instance; the residual frontier facts stay isolated in
`PrimitiveFrontier`:

* `hgcd` — the fraction-free gcd correctness `GcdFFCorrect` (a *proven theorem* `gcdFFCorrect_Q` at the `ℚ`
  base); with `[CharZero]` it discharges the whole canonical reconstruction via
  `canonicalReconstruction_of_charZero` (split factorization + special ⊥ normal coprimality) — the split
  frontier is **gone**, no longer a hypothesis;
* `hden` — the mild scope condition that a successful special integration has `d ≠ 0` (a genuine fraction);
* `hspecialField` — the poly-RDE identity (canonical `Dt = 1` regime, `cPolyRischDEGWf_nil_field_identity`;
  the general non-constant-coefficient case is the P2 algorithm gap);
* `hreduced` — reduced-part soundness (grounded in `cIntegrateReducedGWf_primitive_isIntegralResult_via_interfaces`
  under the Rothstein–Trager residue-data conditions — *not* a `native_decide` wall).

This is a **soundness-only** solver: the completeness contract (`SpecElem`/`NrmElem`/`descend`) is trivial in
the instance, so `not_isElementaryIntegrable` is vacuous. Completeness is the Liouville frontier, deferred.
See `docs/recursive-risch-solver.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- **The primitive-case engine frontier, as a class.** Bundle the named frontier facts once; the
`LawfulRischLevel` instance (hence the whole solver) then resolves from `[PrimitiveFrontier α]` with no
threaded parameters. -/
class PrimitiveFrontier (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] where
  /-- The level's residue-candidate generator. -/
  candidates : CPolyG α → CPolyG α → CPolyG α → List α
  /-- The fraction-free gcd correctness (a *proven theorem* `gcdFFCorrect_Q` at the `ℚ` base). With
  `[CharZero]` this discharges the entire canonical reconstruction — the split frontier is gone. -/
  hgcd : GcdFFCorrect (α := α)
  /-- Scope condition: a successful special integration is of a genuine fraction (`d ≠ 0`). -/
  hden : ∀ (Dt a d snum sden : CPolyG α),
    primitiveCase.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d)
      = some (snum, sden) → toPolyG d ≠ 0
  /-- Poly-RDE identity: the `b = 0` RDE output `qₚ` differentiates back to `⟦fₚ⟧`. -/
  hspecialField : ∀ (Dt a d qp : CPolyG α),
    cisZeroG (crSpecNum Dt a d) = true →
    cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) = some qp →
    towerFractionFieldDerivG Dt (fieldFrac qp [CField.one]) = fieldFrac (crPoly Dt a d) [CField.one]
  /-- Reduced-part soundness (the shared Hermite/residue frontier). -/
  hreduced : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α),
    primitiveCase.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
    toPolyG nrm.rational.2 ≠ 0 ∧ IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm

/-- **The primitive `LawfulRischLevel` instance — assembled from `PrimitiveFrontier` by resolution.**
Materialize one `PrimitiveFrontier α` and the whole solver (`LawfulRischLevel.integrate` / `.sound` /
completeness) resolves automatically, parameter-free. `specialSound` is proven here: the special-part
identity from `hspecialField`, and the **reconstruction from `canonicalReconstruction_of_charZero`** (the
split frontier discharged) with the `b = 0` special term vanishing. -/
instance instLawfulRischLevelPrimitive [PrimitiveFrontier α] : LawfulRischLevel α where
  case := primitiveCase
  candidates := PrimitiveFrontier.candidates
  specialSound := by
    intro Dt a d snum sden hhook
    have hd0 : toPolyG d ≠ 0 := PrimitiveFrontier.hden Dt a d snum sden hhook
    simp only [primitiveCase] at hhook
    by_cases hb : cisZeroG (crSpecNum Dt a d) = true
    · rw [if_pos hb] at hhook
      rcases hqp : cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) with _ | qp
      · rw [hqp] at hhook; simp at hhook
      · rw [hqp] at hhook
        simp only [Option.some.injEq, Prod.mk.injEq] at hhook
        obtain ⟨rfl, rfl⟩ := hhook
        refine ⟨?_, fieldFrac (crPoly Dt a d) [CField.one],
          PrimitiveFrontier.hspecialField Dt a d qp hb hqp, ?_⟩
        · rw [show toPolyG ([CField.one] : CPolyG α) = 1 from by
            rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]]
          exact one_ne_zero
        · -- reconstruction `⟦fₚ⟧ + ⟦cₙ/dₙ⟧ = ⟦a/d⟧`, split frontier discharged
          have hvan : fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d) = 0 := by
            simp only [fieldFrac, (cisZeroG_iff (crSpecNum Dt a d)).mp hb, map_zero, zero_div]
          have hrec := canonicalReconstruction_of_charZero PrimitiveFrontier.hgcd Dt a d hd0
          rw [hvan, add_zero] at hrec
          exact hrec
    · rw [if_neg hb] at hhook; simp at hhook
  reducedSound := PrimitiveFrontier.hreduced
  -- Soundness-only: the completeness contract is trivial (`not_isElementaryIntegrable` is vacuous here).
  -- Completeness (a nontrivial `descend`) is the Liouville frontier, deferred.
  SpecElem := fun _ _ _ => True
  NrmElem := fun _ _ _ => True
  descend := fun _ _ _ _ => ⟨trivial, trivial⟩

end DeepWiki.SymbolicIntegration
