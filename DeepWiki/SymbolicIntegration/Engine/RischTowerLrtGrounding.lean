import DeepWiki.SymbolicIntegration.Engine.RischSolverTowerLrt

/-! # Grounding the recursive LRT solver — the honest end state of the re-base

The re-based recursive solver `LawfulRischLevelLrt` resolves at every tower depth (`instLawfulRischLevelLrtPrimitive`
+ `instLawfulRischLevelLrtTower`), and its assembled soundness `soundFormalLrt` produces a genuine `∀E`
antiderivative. This file crystallizes what the solver **depends on**, on the concrete carrier `CFrac ℚ`
(the ℚ(x)-tower the whole engine runs over): the recursion bottoms out at exactly two **honest** frontiers per
level, and no others:

* `PrimitiveFrontierLrt` — the reduced-part soundness. Closed (`hreducedLrt_of_genuineAll`) to the bundled
  genuine data `LrtReducedGenuineData` — Bronstein's *necessary* residue/normality conditions, which a
  properly-built tower satisfies but which are not derivable from the computable data. This **replaced** the
  rational `PrimitiveFrontier`, whose `IsIntegralResult` was not dischargeable at all (it forces the reduced
  denominator to split over `K`).
* `Fact (GcdFFCorrect …)` — the fraction-free-gcd correctness. Proven unconditionally at `ℚ`
  (`instFactGcdFFCorrectQ`); at tower levels it is the engine's PRS-regularity frontier.

So "no dangling frontier" is achieved in the honest sense: every remaining hypothesis is a **named genuine
mathematical condition**, not an opaque assumed lemma. Completeness (the decidable non-integrability
certificate) is the separate `LrtLiouvilleFrontier` (Liouville criterion). See `docs/recursive-lrt-typeclass.md`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-- **★ The re-based recursive LRT solver is sound on the concrete ℚ(x)-tower, from the honest frontiers alone.**
At carrier `CFrac ℚ` (so `a/d ∈ (CFrac ℚ)(t)`, a genuine two-level tower), a successful run of the
assembled integrator `LawfulRischLevelLrt.integrate` is a true `∀E` antiderivative — depending only on the two
honest reduced frontiers (`PrimitiveFrontierLrt` at the base `ℚ` and at this level) and the tower-level gcd
`Fact` (the base `Fact (GcdFFCorrect ℚ)` is a resolved instance). No rational-residue restriction, no
undischargeable `PrimitiveFrontier`. -/
theorem lrtSolver_sound_on_tower [PrimitiveFrontierLrt ℚ]
    [Fact (GcdFFCorrect (α := CFrac ℚ))] [PrimitiveFrontierLrt (CFrac ℚ)]
    (Dt a d : DensePoly (CFrac ℚ)) (res : LrtResult (CFrac ℚ))
    (h : LawfulRischLevelLrt.integrate Dt a d = some res) :
    IsIntegralResultLrt Dt a d res :=
  LawfulRischLevelLrt.soundFormalLrt Dt a d res h

/-- **The reduced frontier reduces to the genuine data — the whole solver from `LrtReducedGenuineData`.**
Threading `hreducedLrt_of_genuineAll`: supplying Bronstein's genuine residue/normality data for every reduced
input at each level *constructs* the `PrimitiveFrontierLrt` instances, hence (with the gcd `Fact`s) the whole
recursive LRT solver at that depth. This is the honest closure — the solver's soundness rests on genuine
integrability conditions, nothing opaque. -/
noncomputable example [Fact (GcdFFCorrect (α := CFrac ℚ))]
    (hgenℚ : ∀ (Dt a d : DensePoly ℚ), toPoly d ≠ 0 → LrtReducedGenuineData Dt a d)
    (hgenℚx : ∀ (Dt a d : DensePoly (CFrac ℚ)), toPoly d ≠ 0 → LrtReducedGenuineData Dt a d) :
    LawfulRischLevelLrt (CFrac ℚ) :=
  letI : PrimitiveFrontierLrt ℚ := ⟨hreducedLrt_of_genuineAll gcdFFCorrect_Q hgenℚ⟩
  letI : PrimitiveFrontierLrt (CFrac ℚ) :=
    ⟨hreducedLrt_of_genuineAll (Fact.out (p := GcdFFCorrect (α := CFrac ℚ))) hgenℚx⟩
  inferInstance

end DeepWiki.SymbolicIntegration
