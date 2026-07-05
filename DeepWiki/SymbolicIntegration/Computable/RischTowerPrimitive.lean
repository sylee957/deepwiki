import DeepWiki.SymbolicIntegration.Computable.RischTower
import DeepWiki.SymbolicIntegration.Computable.IntegratorCases
import DeepWiki.SymbolicIntegration.Computable.CanonicalReconstructionCharZero
import DeepWiki.SymbolicIntegration.Computable.PrimitiveGuarded

/-! # The primitive base as a resolved instance (`PrimitiveFrontier` ⇒ `LawfulRischLevel`)

The primitive-case (`Dθ ∈ k`) base of the tower. `[PrimitiveFrontier α]` resolves the whole
`LawfulRischLevel α` instance — hence the assembled `integrate` / `sound` / completeness — parameter-free.
The incidental conditions are all handled *by the algorithm/instance*, so `PrimitiveFrontier` has shrunk to a
**single field**: the gcd correctness is a resolved **`[Fact (GcdFFCorrect α)]`** instance (proven at ℚ),
`d ≠ 0` is **supplied by the integrator's guard**, the **special-part identity is guaranteed by the
`primitiveGuardedCase` guard** (P2 — `hspecialField` gone), the reconstruction is proven via
`canonicalReconstruction_of_charZero`, the reduced denominator is proven, and the **candidate list is
computed automatically** (`defaultResidueCandidates`, a bounded rational sweep — no `candidates` field). The
single residual field:

* `hreduced` — reduced-part soundness (grounded in `cIntegrateReducedGWf_primitive_isIntegralResult_via_interfaces`
  under the Rothstein–Trager residue-data conditions — the P3 frontier, *not* a `native_decide` wall).

This is a **soundness-only** solver: the completeness contract (`SpecElem`/`NrmElem`/`descend`) is trivial in
the instance, so `not_isElementaryIntegrable` is vacuous. Completeness is the Liouville frontier, deferred.
See `docs/recursive-risch-solver.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- **The primitive-case engine frontier, as a class.** Bundle the named frontier facts once; the
`LawfulRischLevel` instance (hence the whole solver) then resolves from `[PrimitiveFrontier α]` with no
threaded parameters. -/
class PrimitiveFrontier (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    [Fact (GcdFFCorrect (α := α))] where
  /-- Reduced-part soundness (the shared Hermite/residue frontier — the P3 gap). Only the
  `IsIntegralResultG` obligation remains: the denominator-nonzero conjunct is now *proven* in the instance
  (Hermite denominator ≠ 0 from `d ≠ 0`). -/
  hreduced : ∀ (Dt a d : CPolyG α) (cands : List α) (nrm : IntegralResultG α), toPolyG d ≠ 0 →
    primitiveGuardedCase.reducedCorrect Dt (redNorm Dt a d cands) = some nrm →
    IsIntegralResultG Dt (crNormNum Dt a d) (crNormDen Dt a d) nrm

/-- **Primitive special-part soundness** (shared by the rational and LRT primitive solvers). The special
part is `primitiveGuardedCase.integrateSpecial`: under the guard (`b = 0`, `Dθ = 1`, constant `fₚ`) it solves
the polynomial RDE and the reconstruction (`canonicalReconstruction_of_charZero`) closes with the special term
vanishing; off the guard the hook returns `none`. Independent of any reduced frontier, so both solvers reuse
it. -/
theorem primitiveGuardedCase_specialSound [Fact (GcdFFCorrect (α := α))]
    (Dt a d snum sden : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hhook : primitiveGuardedCase.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
      (crSpecDen Dt a d) = some (snum, sden)) :
    toPolyG sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDerivG Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d := by
  simp only [primitiveGuardedCase] at hhook
  by_cases hguard : (cisZeroG (crSpecNum Dt a d) && cisZeroG (csubG Dt [CField.one])
      && cisZeroG (cmapDeriv (crPoly Dt a d))) = true
  · rw [if_pos hguard] at hhook
    rw [Bool.and_eq_true, Bool.and_eq_true] at hguard
    obtain ⟨⟨hb, hDt1g⟩, hconstg⟩ := hguard
    rcases hqp : cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) with _ | qp
    · rw [hqp] at hhook; simp at hhook
    · rw [hqp] at hhook
      simp only [Option.some.injEq, Prod.mk.injEq] at hhook
      obtain ⟨rfl, rfl⟩ := hhook
      have hDt1 : toPolyG Dt = 1 := by
        have hh := (cisZeroG_iff (csubG Dt [CField.one])).mp hDt1g
        rw [toPolyG_csubG, toPolyG_one_singleton, sub_eq_zero] at hh; exact hh
      have hconst := mapCoeffs_eq_zero_of_cisZeroG_cmapDeriv (crPoly Dt a d) hconstg
      refine ⟨?_, fieldFrac (crPoly Dt a d) [CField.one], ?_, ?_⟩
      · rw [toPolyG_one_singleton]; exact one_ne_zero
      · exact primitive_special_identity Dt (crPoly Dt a d) qp hDt1 hconst hqp
      · have hvan : fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d) = 0 := by
          simp only [fieldFrac, (cisZeroG_iff (crSpecNum Dt a d)).mp hb, map_zero, zero_div]
        have hrec := canonicalReconstruction_of_charZero (Fact.out (p := GcdFFCorrect (α := α))) Dt a d hd0
        rw [hvan, add_zero] at hrec
        exact hrec
  · rw [if_neg hguard] at hhook; simp at hhook

/-- **The primitive `LawfulRischLevel` instance — assembled from `PrimitiveFrontier` by resolution.**
Materialize one `PrimitiveFrontier α` and the whole solver resolves automatically, parameter-free. The
`case` is `primitiveGuardedCase`, so `specialSound` is **fully proven** here: the special-part identity is
*guaranteed by the guard* (`primitive_special_identity` — `toPolyG Dt = 1` + constant coefficients extracted
from the successful hook), and the **reconstruction from `canonicalReconstruction_of_charZero`** with the
`b = 0` special term vanishing; `d ≠ 0` is supplied by the integrator's guard. No `hspecialField`. -/
instance instLawfulRischLevelPrimitive [Fact (GcdFFCorrect (α := α))] [PrimitiveFrontier α] :
    LawfulRischLevel α where
  case := primitiveGuardedCase
  -- **Automatic candidates** (P2): the bounded rational sweep, no field. `cRationalResiduesGWf` filters it
  -- to genuine residues; the bound grows with the denominator degree.
  candidates := fun _ _ d => defaultResidueCandidates (cdegG d + 3)
  specialSound := fun Dt a d snum sden hd0 hhook =>
    primitiveGuardedCase_specialSound Dt a d snum sden hd0 hhook
  reducedSound := by
    intro Dt a d cands nrm hd0 hcorr
    have hcn : toPolyG (crNormDen Dt a d) ≠ 0 :=
      crNormDen_ne_zero_of_charZero (Fact.out (p := GcdFFCorrect (α := α))) Dt a d hd0
    have hpp : (toPolyG (crNormDen Dt a d)).primPart ≠ 0 := Polynomial.primPart_ne_zero _
    refine ⟨?_, PrimitiveFrontier.hreduced Dt a d cands nrm hd0 hcorr⟩
    -- the reduced denominator is the Hermite fold denominator, nonzero since `dₙ ≠ 0`
    simp only [primitiveGuardedCase] at hcorr
    split at hcorr
    · obtain rfl : nrm = redNorm Dt a d cands := (Option.some.injEq _ _).mp hcorr.symm
      exact toPolyG_cHermiteReduceTowerGWf_den_ne_zero (Fact.out (p := GcdFFCorrect (α := α)))
        Dt (crNormNum Dt a d) (crNormDen Dt a d) hcn hpp
    · exact absurd hcorr (by simp)
  -- Soundness-only: the completeness contract is trivial (`not_isElementaryIntegrable` is vacuous here).
  -- Completeness (a nontrivial `descend`) is the Liouville frontier, deferred.
  SpecElem := fun _ _ _ => True
  NrmElem := fun _ _ _ => True
  descend := fun _ _ _ _ => ⟨trivial, trivial⟩

end DeepWiki.SymbolicIntegration
