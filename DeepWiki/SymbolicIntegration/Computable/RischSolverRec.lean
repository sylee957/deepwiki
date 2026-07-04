import DeepWiki.SymbolicIntegration.Computable.RischSolver

/-! # Recursive Risch-solver skeleton (`SubSolver` / `RischSolver.ofSub`)

The recursion interface and step for building solvers up the differential tower. `SubSolver α case` is the
special-part (polynomial + RDE) capability that level `n` consumes from level `n-1`; `RischSolver.ofSub`
assembles a full closed-form `RischSolver` from a `SubSolver` plus this level's reduced-part soundness and
completeness contract. The base case is the primitive `LawfulRischLevel` instance (`RischSolverPrimitive.lean`,
via `PrimitiveFrontier`); the engine bridge from a lower `RischSolver` (the poly-RDE coefficient recursion) is
the deferred frontier. See `docs/recursive-risch-solver.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)]

/-- **The recursion interface.** For a monomial `case`, the special-part capability level `n` consumes from
level `n-1`: whenever `integrateSpecial` succeeds with `(snum, sden)`, a nonzero denominator and a special
value `v` that the fraction differentiates to and that reconstructs `⟦a/d⟧` with the normal part. Exactly
the shape of `RischSolver.specialSound`; in the tower it is produced by the coefficient-level solver via the
poly-RDE. -/
structure SubSolver (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] (case : MonomialCase α) where
  /-- The special-part soundness + reconstruction, delegated from the level below. -/
  special : ∀ (Dt a d snum sden : CPolyG α),
    case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
    toPolyG sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDerivG Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d

/-- **The recursive step.** A `SubSolver` for `case` (the level-below special capability) together with this
level's candidate generator, reduced-part soundness, and completeness contract assemble a full closed-form
`RischSolver`. Its `.integrate`/`.sound`/`.isElementaryIntegrable_of_run`/`.not_isElementaryIntegrable`
follow from the derived API — soundness/completeness are assembled, not re-proven. -/
def RischSolver.ofSub {case : MonomialCase α} (sub : SubSolver α case)
    (candidates : CPolyG α → CPolyG α → CPolyG α → List α)
    (SpecElem NrmElem : CPolyG α → CPolyG α → CPolyG α → Prop)
    (reduced : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α),
      case.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
      toPolyG nrm.rational.2 ≠ 0 ∧ IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm)
    (descend : ∀ (Dt a d : CPolyG α),
      IsElementaryIntegrableG Dt a d → SpecElem Dt a d ∧ NrmElem Dt a d) :
    RischSolver α where
  case := case
  candidates := candidates
  specialSound := sub.special
  reducedSound := reduced
  SpecElem := SpecElem
  NrmElem := NrmElem
  descend := descend

/-- **The recursion step: a `SubSolver` built from a sub-`RischSolver`.** The special part is *computed by
another solver* `sub` (the level below): whenever this level's `integrateSpecial` succeeds, running `sub` on
the special subproblem `⟦specSubNum/specSubDen⟧` returns a log-free result whose rational part equals
`snum/sden` and reconstructs `⟦a/d⟧` with the normal part (`hrun` — the engine bridge relating the case hook
to a sub-run). The special-part field identity is then **derived from `sub.sound`**, not assumed. This is
how recursive integration is encoded in `RischSolver`: `RischSolver.ofSub (SubSolver.ofLower sub …) …`
delegates the special part downward, bottoming out at the primitive `LawfulRischLevel`. Only `hrun` (the case-hook ↔
sub-run bridge) remains — the algorithm-level fact the tower keystone will supply. -/
def SubSolver.ofLower {case : MonomialCase α} (sub : RischSolver α)
    (specSubNum specSubDen : CPolyG α → CPolyG α → CPolyG α → CPolyG α)
    (hrun : ∀ (Dt a d snum sden : CPolyG α),
      case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
      toPolyG sden ≠ 0 ∧ ∃ res : IntegralResultG α,
        sub.integrate Dt (specSubNum Dt a d) (specSubDen Dt a d) = some res ∧
        res.logs = [] ∧
        fieldFrac res.rational.1 res.rational.2 = fieldFrac snum sden ∧
        fieldFrac (specSubNum Dt a d) (specSubDen Dt a d)
            + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d) :
    SubSolver α case where
  special := by
    intro Dt a d snum sden hhook
    obtain ⟨hsden, res, hres, hlogs, heq, hrecon⟩ := hrun Dt a d snum sden hhook
    refine ⟨hsden, fieldFrac (specSubNum Dt a d) (specSubDen Dt a d), ?_, hrecon⟩
    have hs := sub.sound Dt (specSubNum Dt a d) (specSubDen Dt a d) res hres
    rw [IsIntegralResultG, hlogs, logResidueSumG_nil, add_zero] at hs
    rw [← heq]
    exact hs

end DeepWiki.SymbolicIntegration
