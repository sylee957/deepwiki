import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitive
import DeepWiki.SymbolicIntegration.Computable.LrtAssembly

/-! # `LawfulRischLevelLrt` — the recursive LRT (algebraic-residue) Risch-solver abstraction

The re-based analogue of `LawfulRischLevel`: same `X`/`LawfulX` idiom, but the assembled solver produces an
`LrtResultG` (symbolic algebraic-residue logs `Σ_{Rᵢ(c)=0} c·log Sᵢ(c,t)`) via the root-free assembler
`cIntegrateCaseLrt`. The payoff is that its reduced-part frontier is the **dischargeable** `PrimitiveFrontierLrt`
(closed to `LrtReducedGenuineData` by `hreducedLrt_of_genuineAll`) rather than the rational `PrimitiveFrontier`,
which is *not* universally dischargeable — the rational reduced soundness `IsIntegralResultG` forces the reduced
denominator to split over `K`, false when the residues are algebraic. The special/polynomial part is unchanged
(`specialSound`, a `K`-level identity, shared verbatim with the rational solver).

Materialize one `LawfulRischLevelLrt` instance and the assembled integrator `integrate` / `soundFormalLrt`
resolve parameter-free. The base is `instLawfulRischLevelLrtPrimitive` (from `[PrimitiveFrontierLrt α]`, reusing
`primitiveGuardedCase_specialSound` — no coefficient recursion at the base); the tower step (the recursion into
the coefficient field) is built in `RischSolverTowerLrt.lean`. See `docs/recursive-lrt-typeclass.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
  [Fact (GcdFFCorrect (α := α))]

/-- **The recursive LRT Risch solver as a class.** The computable data (`case`) plus the two soundness laws:
`specialSound` (the special/polynomial part reconstructs `a/d`, a `K`-level identity — shared with the rational
solver) and `reducedSoundLrt` (the reduced normal part integrates to `cIntegrateReducedLrtG` with algebraic
residues, `IsIntegralResultLrtG` over every alg-closed extension `E`). One `instance` assembles `integrate` /
`soundFormalLrt` by resolution. The reduced law is the *dischargeable* frontier `PrimitiveFrontierLrt` — no
rational-residue restriction. -/
class LawfulRischLevelLrt (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    [Fact (GcdFFCorrect (α := α))] where
  /-- The per-monomial-case computable hooks for this level (the special/polynomial-part integrator). -/
  case : MonomialCase α
  /-- Special-part soundness + reconstruction (`K`-level, existential special value — identical to the rational
  solver's `specialSound`). The `d ≠ 0` precondition is supplied by the integrator's guard. -/
  specialSound : ∀ (Dt a d snum sden : CPolyG α), toPolyG d ≠ 0 →
    case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
    toPolyG sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDerivG Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d
  /-- Reduced-part soundness with algebraic residues: `cₙ/dₙ` integrates to `cIntegrateReducedLrtG …` over every
  alg-closed differential extension `E`. This is exactly `PrimitiveFrontierLrt.hreducedLrt` — the dischargeable
  frontier (no rational-residue restriction). -/
  reducedSoundLrt : ∀ (Dt a d : CPolyG α), toPolyG d ≠ 0 →
    IsIntegralResultLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d))

namespace LawfulRischLevelLrt

/-- **The assembled LRT integrator** — a function of `(Dt, a, d)` alone, via the root-free assembler
`cIntegrateCaseLrt` (no candidate sweep). **Guards on `d ≠ 0`**, so a successful run supplies `d ≠ 0` to the
soundness laws. -/
def integrate [LawfulRischLevelLrt α] (Dt a d : CPolyG α) : Option (LrtResultG α) :=
  if cisZeroG d then none else cIntegrateCaseLrt case Dt a d

/-- **Formal LRT soundness.** Any successful run satisfies the algebraic-residue log-derivative identity
`IsIntegralResultLrtG` — over every alg-closed differential extension `E`, `D_E(rational) + Σ residue logs =
a/d`. Composed from the instance's `specialSound` + `reducedSoundLrt` through the assembler soundness
`cIntegrateCaseLrt_sound`. -/
theorem soundFormalLrt [LawfulRischLevelLrt α] (Dt a d : CPolyG α) (res : LrtResultG α)
    (h : integrate Dt a d = some res) : IsIntegralResultLrtG Dt a d res := by
  rw [integrate] at h
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
      have hNrm := reducedSoundLrt Dt a d hd0
      exact cIntegrateCaseLrt_sound (Fact.out (p := GcdFFCorrect (α := α))) case Dt a d res snum sden v
        hd0 hSpec h0 hsden hSpecField hNrm hrecon

/-- **Derived broad elementary integrability.** A successful LRT run certifies `a/d` is elementary integrable in
the broad (algebraic-residue) sense — `IsElementaryIntegrableLrtG`, via `soundFormalLrt`. -/
theorem isElementaryIntegrableLrt_of_run [LawfulRischLevelLrt α] (Dt a d : CPolyG α)
    (res : LrtResultG α) (h : integrate Dt a d = some res) : IsElementaryIntegrableLrtG Dt a d :=
  ⟨res, soundFormalLrt Dt a d res h⟩

end LawfulRischLevelLrt

/-- **The primitive LRT base instance — assembled from `PrimitiveFrontierLrt` by resolution.** Materialize one
`PrimitiveFrontierLrt α` and the whole LRT solver resolves. The `case` is `primitiveGuardedCase`, so
`specialSound` is the proven `primitiveGuardedCase_specialSound` (the `Dθ = 1` special identity + the
`canonicalReconstruction_of_charZero`, `b = 0` special term vanishing); `reducedSoundLrt` is the frontier field
`PrimitiveFrontierLrt.hreducedLrt`. No coefficient recursion — the primitive base has constant-coefficient
special parts. -/
instance instLawfulRischLevelLrtPrimitive [CRischField α] [PrimitiveFrontierLrt α] :
    LawfulRischLevelLrt α where
  case := primitiveGuardedCase
  specialSound := fun Dt a d snum sden hd0 hhook =>
    primitiveGuardedCase_specialSound Dt a d snum sden hd0 hhook
  reducedSoundLrt := fun Dt a d hd0 => PrimitiveFrontierLrt.hreducedLrt Dt a d hd0

/-- **Validation: the base LRT solver resolves from the reduced frontier.** Given `[PrimitiveFrontierLrt α]`,
`LawfulRischLevelLrt α` resolves parameter-free — the base of the recursive LRT tower. -/
example [CRischField α] [PrimitiveFrontierLrt α] : LawfulRischLevelLrt α := inferInstance

end DeepWiki.SymbolicIntegration
