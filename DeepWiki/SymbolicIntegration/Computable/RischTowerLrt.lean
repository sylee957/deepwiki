import DeepWiki.SymbolicIntegration.Computable.LrtAssembly
import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitive

/-! # `LawfulRischLevelLrt` — the root-free (LRT) one-level Risch solver

The algebraic-residue analogue of `LawfulRischLevel`. Its reduced base is the root-free `cIntegrateReducedLrtG`
(symbolic Lazard–Rioboo–Trager log part) rather than the rational `cIntegrateReducedGWf`, so its soundness is
`IsIntegralResultLrtG` (algebraic residues) rather than the rational-residue-bound `IsIntegralResultG`. The
special part is *shared* with the rational solver (`primitiveGuardedCase_specialSound`). Materialize one
`PrimitiveFrontierLrt α` and the whole root-free solver — `integrateLrt` / `soundLrt` — resolves
parameter-free, exactly as `PrimitiveFrontier` assembles the rational `LawfulRischLevel`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- **The root-free (LRT) one-level Risch solver, as a class.** Computable data (`case`) plus the two
soundness laws: the *shared* special-part soundness (`specialSound`, identical to `LawfulRischLevel`) and the
*root-free* reduced soundness (`hreducedLrt`, `IsIntegralResultLrtG` for `cIntegrateReducedLrtG`). One
instance assembles `integrateLrt` / `soundLrt`. Unlike `LawfulRischLevel.reducedSound`, the reduced law has
**no** rational-residue restriction. -/
class LawfulRischLevelLrt (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    [Fact (GcdFFCorrect (α := α))] where
  /-- The per-monomial-case computable hooks for this level (special part). -/
  case : MonomialCase α
  /-- Special-part soundness + reconstruction (shared with the rational solver). -/
  specialSound : ∀ (Dt a d snum sden : CPolyG α), toPolyG d ≠ 0 →
    case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
    toPolyG sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDerivG Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d
  /-- Root-free reduced-part soundness: `cₙ/dₙ` integrates to `cIntegrateReducedLrtG …` with algebraic
  residues (`IsIntegralResultLrtG`). No rational-residue restriction. -/
  hreducedLrt : ∀ (Dt a d : CPolyG α), toPolyG d ≠ 0 →
    IsIntegralResultLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d))

namespace LawfulRischLevelLrt

/-- **The assembled root-free integrator** — a function of `(Dt, a, d)` alone. Guards on `d ≠ 0`, else runs
the one-level primitive LRT case integrator `cIntegrateCaseLrt`. -/
def integrateLrt [Fact (GcdFFCorrect (α := α))] [LawfulRischLevelLrt α] (Dt a d : CPolyG α) :
    Option (LrtResultG α) :=
  if cisZeroG d then none else cIntegrateCaseLrt case Dt a d

/-- **Derived root-free soundness.** Any successful `integrateLrt` run is an antiderivative of `a/d` — over
every algebraically-closed differential extension `E`, with symbolic algebraic residues. Assembled from the
instance's `specialSound` + `hreducedLrt` through `cIntegrateCaseLrt_sound`. -/
theorem soundLrt [Fact (GcdFFCorrect (α := α))] [LawfulRischLevelLrt α] (Dt a d : CPolyG α)
    (res : LrtResultG α) (h : integrateLrt Dt a d = some res) : IsIntegralResultLrtG Dt a d res := by
  rw [integrateLrt] at h
  by_cases hdz : cisZeroG d = true
  · rw [if_pos hdz] at h; simp at h
  · rw [if_neg hdz] at h
    have hd0 : toPolyG d ≠ 0 := fun hh => hdz ((cisZeroG_iff d).mpr hh)
    have h0 : cIntegrateCaseLrt case Dt a d = some res := h
    rw [cIntegrateCaseLrt] at h
    rcases hcrep : canonicalRepresentationFastGWf Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
    rw [hcrep] at h
    dsimp only at h
    rcases hspec : case.integrateSpecial Dt fp b ds with _ | ⟨snum, sden⟩
    · rw [hspec] at h; simp at h
    · rw [hspec] at h
      have hSpec : case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d)
          = some (snum, sden) := by
        simp only [crPoly, crSpecNum, crSpecDen, hcrep]; exact hspec
      obtain ⟨hsden, v, hSpecField, hrecon⟩ := specialSound Dt a d snum sden hd0 hSpec
      exact cIntegrateCaseLrt_sound (Fact.out (p := GcdFFCorrect (α := α))) case Dt a d res snum sden v
        hd0 hSpec h0 hsden hSpecField (hreducedLrt Dt a d hd0) hrecon

end LawfulRischLevelLrt

/-- **The primitive root-free solver instance — assembled from `PrimitiveFrontierLrt` by resolution.**
Materialize one `PrimitiveFrontierLrt α` and the whole root-free solver resolves. `case` is
`primitiveGuardedCase`; `specialSound` is the shared `primitiveGuardedCase_specialSound`; the reduced base is
`PrimitiveFrontierLrt.hreducedLrt` (algebraic residues). The LRT counterpart of
`instLawfulRischLevelPrimitive`. -/
instance instLawfulRischLevelLrtPrimitive [CRischField α] [Fact (GcdFFCorrect (α := α))]
    [PrimitiveFrontierLrt α] : LawfulRischLevelLrt α where
  case := primitiveGuardedCase
  specialSound := fun Dt a d snum sden hd0 hhook =>
    primitiveGuardedCase_specialSound Dt a d snum sden hd0 hhook
  hreducedLrt := PrimitiveFrontierLrt.hreducedLrt

end DeepWiki.SymbolicIntegration
