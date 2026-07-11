# Refactoring the recursive Risch solver onto the genuine, root-free LRT path

> **STATUS (2026-07-05): the coefficient recursion is rational; the LRT `IsAlgClosed` gap is a developable
> direction, not a wall.** Two separate facts, which an earlier draft of this note wrongly conflated:
>
> 1. **Why the *coefficient recursion* uses the rational path** — not because LRT is "blocked", but because a
>    coefficient integral is **limited integration**: the antiderivative must lie in the coefficient field
>    (log-free). Any algebraic-residue logarithm the LRT could produce would leave that field and be rejected
>    anyway. So `LawfulRischLevel.integrateRational` (rational, `K`-level `IsIntegralResultG`, descent-free) is
>    the *correct* tool there on its own merits (shipped: `recursive-risch-tower.md`, `40d41280`→`bb3d183c`).
>
> 2. **The LRT log part** (`IsIntegralResultLrtG`, `LrtSoundness.lean`) *is* stated `∀ E [IsAlgClosed E]`
>    (algebraically **closed** differential extension). Mathlib's differential-field library
>    (`FieldTheory/Differential/`) stops at **finite** extensions (`differentialFiniteDimensional`,
>    `IntermediateField`), so instantiating it as-stated needs `Differential (AlgebraicClosure K)`, which
>    Mathlib lacks. This was a real gap but a *developable* one — and **Direction (A) is now DONE**:
>    - **(A) — BUILT** (`DifferentialAlgebraicClosure.lean`, commit `bada3a2c`): `Differential
>      (AlgebraicClosure K)` + `DifferentialAlgebra K (AlgebraicClosure K)`, axiom-clean. Not the colimit
>      slog it looked like — the key is Mathlib's `Derivation.algHom_deriv` (an injective differential-algebra
>      hom commutes with `′` on separable elements): `derivAt x`, computed in the finite `K⟮x⟯`, agrees with
>      the derivation of *any* finite intermediate field ∋ x (`derivAt_eq_val_deriv`), so the laws reduce any
>      finite element set to the common finite `K⟮x,y⟯`. Char 0 gives separability. **Payoff**
>      (`LrtAlgebraicClosure.lean`, `6c814a17`): `isIntegralResultLrtG_algebraicClosure` instantiates the LRT
>      `∀E` identity at `E = AlgebraicClosure (CFieldSpec.K α)` — a single concrete identity, not just "∀ E".
>    - **(B)** — alternative, not pursued: weaken `[IsAlgClosed E]` to "residues split in E" and instantiate at
>      the finite `Polynomial.SplittingField`. Would refactor the LRT statement; (A) un-blocks as-stated.
>
> The LRT reduced-part soundness (`descendGenuine`) is untouched and valuable; **(A) makes it usable
> end-to-end**. Lesson: re-grep Mathlib before calling something a wall — `algHom_deriv` was the key.

## Motivation (two questions)

1. **Why can't the primitive integrator just "use LRT"?** The main solver `LawfulRischLevel`
   is built on `IntegralResultG`, whose log part is `List (α × CPolyG α)` — the residue is a
   **rational constant** `α`. Its reduced call is the rational `cIntegrateReducedG`. LRT
   produces `LrtResultG`, whose log part is `List (CPolyG α × List (CPolyG α))` — the residue
   is a **root of a polynomial `Rᵢ`** (algebraic, implicit). `LrtResultG` is strictly more
   general; the two result types are incompatible (no `IsIntegralResultLrtG → IsIntegralResultG`),
   so you cannot swap the reduced call in place. The LRT path is the parallel solver
   `LawfulRischLevelLrt` / `integrateLrt` / `soundLrt`.

2. **Which precondition does LRT eliminate?** The **rational-residue restriction**
   (`hden`-split-over-`K` / `hsplit`) that makes `PrimitiveFrontier.hreduced` genuinely limited
   is simply **absent** from the LRT frontier `hreducedLrt`. LRT is also root-free, so it drops
   the `candidates` field the rational solver carries.

Neither solver has external consumers (nothing calls `integrate`/`integrateLrt`), so the
recursive machinery is scaffolding — safe to restructure.

## Done

- **`hreducedLrt` closed** to `LrtReducedGenuineData` (`hreducedLrt_of_genuineAll`,
  `isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine`): the LRT primitive reduced frontier
  reduces to an explicit bundle of the genuine Rothstein–Trager residue-data + tower-nondegeneracy
  conditions (necessary; not provable from computable data). `PrimitiveFrontierLrt =
  ⟨hreducedLrt_of_genuineAll hgcd data⟩`.
- **`LawfulRischLevelLrt` genuine-ified** (parity with the rational solver): `integrateLrt`
  applies the residue-constancy guard `allResiduesConstantLrtG` (each residue minimal polynomial
  `Rᵢ` monic-constant ⟺ its roots, the algebraic residues, are constants), so `soundLrt` returns
  the **genuine** `IsGenuineIntegralResultLrtG` (`IsIntegralResultLrtG ∧ AllResiduesConstantLrtG`)
  — a true antiderivative, declining non-elementary inputs like `∫1/log x`.

So the recursive solver's root-free path is a genuine antiderivative certifier with no
rational-residue restriction — the primitive integrator using LRT, at parity with the rational one.

## Remaining (blocked / large — not a clean refactor)

- **Class-field restructure** (`PrimitiveFrontierLrt.hreducedLrt` → a `genuine :
  LrtReducedGenuineData` field): skipped. `LrtReducedGenuineData` has a three-universe signature
  (the extension universe appears in two slots), so a class field over it fails universe
  inference (`failed to infer universe levels`). The reduction is already proven as a theorem
  (`hreducedLrt_of_genuineAll`), which is the honest content; the class-field form is cosmetic.

- **Tower step** (`[LawfulRischLevelLrt α] → LawfulRischLevelLrt (CFracG α)`): unbuilt in *both*
  solvers (only the primitive base is instantiated). Two obstructions: (1) the recursive carrier
  typeclasses `CharZero (CFieldSpec.K (CFracG α))` / `Algebra ℚ …` / `Fact (GcdFFCorrect (CFracG α))`
  exist only as **local-per-file** instances, not global recursive ones (`CRischField`/`CFracGcdCoreWf`
  at `CFracG` *are* global); (2) the reduced soundness at level `CFracG α` is gated by the genuine
  conditions for `CFracG-α` inputs — per-input hypotheses (the Bronstein frontier), so no
  unconditional recursive `PrimitiveFrontierLrt (CFracG α)` instance exists; a tower step would have
  to thread the genuine data at each level. This is a large new construction, not a refactor.

- **Retiring the rational `LawfulRischLevel`**: it is now subsumed by the genuine LRT solver
  (LRT ⊇ rational residues, both genuine). Retiring it would remove the rational-residue-restricted
  path, but breaks the legacy rational assembly (including its dense canonical plumbing,
  `LiouvilleCompleteness`). Deferred — a large deletion, only worth it once the LRT path carries the
  completeness certificate too.
