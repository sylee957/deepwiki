# Front-facing surface vs. details — how to distinguish "what a human verifies" from "machine-checked internals"

**The goal.** In an autoformalized library, a human reviewer's job is to confirm the *formal statements*
match the *intended mathematics* — the **definitions**, **typeclasses**, and the **statements of the
results being claimed**. Once those typecheck and are believed faithful, the *proofs* are trusted (Lean
checked them). So we want to cleanly surface the **front-facing** layer and hide the **details**.

## Why a literal `Definitions/` + `Proofs/` directory split is the wrong tool

1. **Lean theorems are atomic.** A `theorem` bundles its *statement* and its *proof* in one declaration.
   You cannot put the statement in `Definitions/` and the body in `Proofs/`. And a spec theorem's
   *statement* is itself front-facing (e.g. `toPoly (cadd p q) = toPoly p + toPoly q` — the reviewer
   must check this homomorphism claim). So a def-vs-theorem file split would push the review surface
   (spec statements) *into* `Proofs/`, defeating the purpose.
2. **It fights a deliberate, documented discipline.** 225 of SymbolicIntegration's 427 files are *mixed*
   (def + its satellite lemmas) on purpose — CLAUDE.md's "every `def` ships its satellite lemmas in the
   defining file" (denotation squares, intro/elim, `_apply`). A reviewer finds a definition's contract
   *next to* the definition. Scattering that into a parallel `Proofs/` tree makes the API harder to read,
   not easier.
3. **It doesn't fit the areas uniformly.** `ComputableAlgebra` is 4 all-mixed core files (defs beside
   their spec squares — nothing to separate). `Algebra` is a Mathlib-*gap lemma library* (7/11 proof-only,
   ~all theorems) — its `Definitions/` would be nearly empty. Only a fraction of `SymbolicIntegration`
   would split cleanly.
4. **Churn.** 400+ files, every import rewritten, for a boundary that tooling already draws for free.

## What already draws the boundary — and what to add

**(A) doc-gen4 *is* the front-facing view (already exists, zero cost).** It renders every declaration's
signature + one-line docstring and **hides proof bodies**. Reading the published docs
(https://sylee957.github.io/deepwiki/) *is* "review the definitions and statements, trust the proofs."
This is the primary answer: the front-facing surface is the rendered API, not a directory.

**(B) The spec surface is already tagged — make it the explicit contract layer.** The codebase already
marks the reviewable contracts: **31 `@[denote]`** homomorphism squares (`⟦f x⟧ = F ⟦x⟧`) and
**153 `_sound`/`_spec`/`_complete`/`_correct`** theorems. Definitions + typeclasses + these tagged
theorems ≈ the front-facing surface; the remaining internal lemmas are details. Recommendation: adopt a
single explicit marker (a `@[front]`/`@[spec]` label attribute, or keep the `_sound`/`@[denote]`
conventions) so a reviewer — or a doc-gen filter — can show *only* the contract layer.

**(C) Per-topic reading-guide / interface modules (the proven pattern).** `Engine/PrimitiveCase.lean`
already does exactly this: a module that *defines nothing*, names — in algorithm order — the computable
**definitions** that make up a result, and *points at where each step's proof lives*. That is the
front-facing/details separation done right: a narrative interface over the trusted surface, with the
proof bulk left in the cited files. **Recommendation: one such reading-guide/interface module per major
topic** (there is precedent; extend it), giving a human a single "here is what to review" entry point
per area without relocating a single proof.

**(D) File-level def/proof split where it's already natural (light, opportunistic).** The codebase
already has 32 def-only + 112 proof-only files and the `RealCurves`/`RealCurvesRegularity`,
`Compute/`-defs-vs-`*Correctness`-proofs conventions. Keep splitting a *heavy* concept into a thin
definitions file + a regularity/soundness proof file **when the proof bulk dwarfs the interface** — but
as a per-concept judgment, not a blanket `Definitions/`/`Proofs/` reorg, and never at the cost of
divorcing a small def from its defining satellites.

## Recommendation

Do **A + B + C**, not the directory split:
- Treat **doc-gen4 as the front-facing review surface** (it already hides proofs).
- Make the **contract layer explicit** by standardizing the spec markers (`@[denote]` + `_sound`/`_spec`),
  optionally a `@[front]` label + a doc-gen filter, so the reviewer can see definitions + typeclasses +
  spec statements alone.
- Add a **reading-guide/interface module per topic** (à la `PrimitiveCase.lean`) as the human entry point.
- Split individual heavy concepts into def-file + proof-file **opportunistically** (existing convention).

This gives exactly the front-facing-vs-details distinction, is Lean-idiomatic (works *with* atomic
theorems), preserves the satellite discipline, and costs a fraction of a 400-file reorg.

## The front-facing surface today (measured)

| area | files | definitions/typeclasses (front) | theorems (mostly detail) | tagged spec theorems |
|---|---|---|---|---|
| ComputableAlgebra | 4 | 60 | 53 | (core `@[denote]` squares) |
| Algebra | 11 | 7 | 43 | — (gap-lemma library) |
| SymbolicIntegration | 427 | 1631 | 2835 | 31 `@[denote]` + 153 `_sound`/… |

The front-facing surface a reviewer must check ≈ the ~1700 definitions/typeclasses + the ~184 tagged
spec theorems + each topic's main results — a small, taggable slice of the 2900+ theorems. That slice is
what a reading-guide module names and what doc-gen already renders.
