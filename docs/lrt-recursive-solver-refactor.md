# Refactoring the recursive Risch solver onto the genuine, root-free LRT path

> **STATUS (2026-07-05): SUPERSEDED — the recursion landed on the RATIONAL path instead.** Putting the
> *coefficient recursion* on the LRT path (`LrtResultG`, `∀E [IsAlgClosed E]` soundness) is blocked: the
> tower step needs base-level (`K`) coefficient soundness, and descending the LRT `∀E` identity to `K` needs
> a `Differential (AlgebraicClosure K)` instance Mathlib lacks (and the dev structurally avoids). The
> shipped solution (`recursive-risch-tower.md`, commits `40d41280`→`bb3d183c`) uses the **rational**
> `LawfulRischLevel.integrateRational`, whose `IsIntegralResultG` is already `K`-level (descent-free) — so
> the coefficient recursion is sound with no algebraic-closure machinery. The LRT reduced-part *soundness*
> (`LrtSoundness.lean`, `descendGenuine`) is untouched and valuable; only its use as the *coefficient
> integrator* was abandoned. Kept as a record of why the rational path was chosen.

## Motivation (two questions)

1. **Why can't the primitive integrator just "use LRT"?** The main solver `LawfulRischLevel`
   is built on `IntegralResultG`, whose log part is `List (α × CPolyG α)` — the residue is a
   **rational constant** `α`. Its reduced call is the rational `cIntegrateReducedGWf`. LRT
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

- **Tower step** (`[LawfulRischLevelLrt α] → LawfulRischLevelLrt (QFunNZG α)`): unbuilt in *both*
  solvers (only the primitive base is instantiated). Two obstructions: (1) the recursive carrier
  typeclasses `CharZero (CFieldSpec.K (QFunNZG α))` / `Algebra ℚ …` / `Fact (GcdFFCorrect (QFunNZG α))`
  exist only as **local-per-file** instances, not global recursive ones (`CRischField`/`CFracGcdCoreWf`
  at `QFunNZG` *are* global); (2) the reduced soundness at level `QFunNZG α` is gated by the genuine
  conditions for `QFunNZG-α` inputs — per-input hypotheses (the Bronstein frontier), so no
  unconditional recursive `PrimitiveFrontierLrt (QFunNZG α)` instance exists; a tower step would have
  to thread the genuine data at each level. This is a large new construction, not a refactor.

- **Retiring the rational `LawfulRischLevel`**: it is now subsumed by the genuine LRT solver
  (LRT ⊇ rational residues, both genuine). Retiring it would remove the rational-residue-restricted
  path, but breaks the rational assembly (`IntegratorCases`, `IntegratorAssembly`,
  `LiouvilleCompleteness`). Deferred — a large deletion, only worth it once the LRT path carries the
  completeness certificate too.
