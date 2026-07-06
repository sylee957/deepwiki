# Project: rewrite SymbolicIntegration proofs through front-loaded transfer

**Status:** in progress (kickoff) · **Owner:** autonomous agent · **Repo:** `deepwiki` (Lean 4, v4.31.0)

## Goal

Organize the topic's proofs so **denotation transport is separated from mathematics**, using the
general `DeepWiki.Transfer` framework. The value is uniformity + robustness (proofs that self-heal when
a square is renamed / an op is added), accepted even where line-count is flat.

## The methodology (grounded in the research)

The mature reference is **Isabelle's Lifting/Transfer** (Huffman–Kunčar, CPP 2013): a `transfer` tactic
moves a whole goal to the other representation in one step, via per-constant transfer rules, leaving a
goal *purely* on one side. **Sozeau's generalized rewriting** (the congruence/`Proper` engine) is what
lets transport push under arbitrary context — and Lean's `simp` already embodies it (it rewrites under
congruence), so for our *functional* denotation (`toPolyG`) `simp only [denote]` already IS whole-goal
transfer that pushes under math operators (`natDegree`, `∣`, `/`, …).

**Interleaving is a symptom of doing transport locally with `rw`.** The clean form **front-loads** it:

> open the proof with the transport step (`simp only [denote, <extra homs>]` or `transfer`) to move
> every denotation application to the abstract side, leaving a **pure abstract-math goal**; then finish
> with `ring`/`field_simp`/`omega`/Mathlib lemmas — no `toPolyG_*` interleaved.

Kickoff example ([`Assemble.lean` hcombine](../DeepWiki/SymbolicIntegration/Computable/Assemble.lean)):
`rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, map_add, map_mul, map_mul, map_mul];
field_simp` → `simp only [denote, map_add, map_mul]; field_simp` (8 ordered lemmas → one unordered
transport step, then the math).

## Target idioms

- **Interleaved `rw [toPolyG_c…, <hom lemmas>, …]; <math>`** → `simp only [denote, <hom lemmas>]; <math>`
  (front-load transport; the `<math>` is pure). The dominant, highest-value case (≈242 `rw` chains,
  most partially convertible this way).
- **`simp only [toPolyG_a, toPolyG_b, …]`** (≈45) → `simp only [denote]` (drop the explicit list).
- **`have h : toPolyG (cop …) = <denote-normal form> := by <transport>`** → `have h := transfer% (…)`
  *only* when the RHS is exactly the denote-normal form (many of the ≈82 `have`s are not — they use a
  local abbreviation or an atom needing a hypothesis; leave those).
- **Whole-goal `toPolyG X = q`** closable by transport → `by transfer`.
- **Keep** the `native_decide` zero-test reflection (`RefinesPolyG.eq_of_csub_cisZero`) — distinct.

## Phase order & discipline

By file, densest first (transport-rewrite counts): `HermiteValuationTower` (32), `OneShotSoundness` (24),
`CoupledDE/Assembly` (21), `LaurentSoundness` (19), `RischDE/Structural` (18), `YunTowerCorrect` (16), …

Per file: front-load convertible proofs; **gate each file green** (`scripts/check.sh <module>`); commit
per file/batch. **Do not force** `simp only [denote]` where it over-fires or where transport is genuinely
inseparable from the math (curated `simp only` feeding `linear_combination` — leave as-is). **Retire
duplication** found along the way (`scripts/wiki rdeps` before deleting). When a proof needs a denotation
square that is not yet `@[denote]` (e.g. `toPolyG_radDeriv`), tag it `@[denote]` in its defining file so
front-loading works — that is part of the work.

## Guardrails

Same as the topic: no change to the executable/`native_decide` path; warnings are errors; one-line
docstrings; `-/` trap; library-not-catalog; commit per gate-green step. The framework itself lives in
`DeepWiki/Transfer/` (topic-agnostic) — do not re-couple it to SymbolicIntegration.
