# Project: rewrite SymbolicIntegration proofs through front-loaded transfer

**Status:** in progress · **Owner:** Codex-executable · **Repo:** `deepwiki` (Lean 4, v4.32.1)

This document is self-contained; it assumes no conversation context. Read top to bottom before editing.

## For the executing agent (Codex): the loop

Prepend `export PATH="$HOME/.elan/bin:$PATH"` to every shell call. Work **one file at a time**, in the
worklist order below. For each file:

1. **Find convertible sites:**
   `grep -nE "rw \[.*toPolyG_c|simp only \[.*toPolyG_c" <file>`
2. **Convert only the clean cases** (patterns below). Leave anything that doesn't match cleanly.
3. **Gate the module:** `scripts/check.sh DeepWiki.SymbolicIntegration.Computable.<Module>` — must print
   `GATE: PASS` (warnings are failures). If a conversion breaks the proof or `simp only [denote]`
   over-fires, **revert that one site** and move on (do not fight it).
4. **Commit per file:** `refactor(transfer): front-load transport in <Module>`, ending the body with
   `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.
5. Mark the file done in the worklist and continue.

Two conversions are already committed as **templates** — copy their shape:
- `Assemble.lean` (commit `baba3648`) and `HermiteValuationTower.lean` (commit `a5a1ee10`).

## The framework (already built, do not rebuild)

`DeepWiki/Transfer/` (topic-agnostic): the `denote` simp attribute + the `transfer%` term elaborator and
`transfer` whole-goal tactic. Every `toPolyG_c*` homomorphism square is `@[denote]`, so `simp only
[denote]` pushes the denotation to the leaves under any surrounding context (Lean's simp congruence =
Sozeau generalized rewriting). Import `DeepWiki.Transfer` where you use `transfer`/`transfer%` (most
files already reach `denote` transitively via `GenericPolyEngine`).

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

## Conversion patterns (the only four; concrete before → after)

1. **Interleaved chain — front-load** (highest value). A `rw` mixing `toPolyG_c*` + homomorphism
   lemmas (`map_add`/`map_mul`/`map_sub`/`map_pow`) then math:
   ```
   rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, map_add, map_mul, map_mul, map_mul,
     div_add_div _ _ h1 h2]; ring
   -- →
   simp only [denote, map_add, map_mul]      -- front-loaded transport (unordered, robust)
   rw [div_add_div _ _ h1 h2]; ring          -- pure math
   ```
   Rule: move the `toPolyG_c*` and `map_*` lemmas into `simp only [denote, map_*]`; keep the genuinely
   mathematical rewrites (`div_add_div`, `field_simp`, `ring`, `mul_comm`, a named lemma, a hypothesis)
   as the following step.
2. **Simp-list — swap for `denote`.** `simp only [toPolyG_a, toPolyG_b, …, <non-denote lemmas>]` →
   `simp only [denote, <non-denote lemmas>]` (drop every `toPolyG_c*`; keep the rest, e.g. a def unfold
   like `cHermiteReduceTowerG`, `map_*`, `← hDef`).
3. **`have` synthesis — `transfer%`** *only when the RHS is exactly the denote-normal form*:
   `have h : toPolyG (cop …) = <denote-normal> := by rw [toPolyG_c…]` → `have h := transfer% (toPolyG (cop …))`.
   Most `have`s do NOT qualify (RHS uses a local abbrev, or the LHS is a variable needing a hypothesis
   first) — leave those.
4. **Whole-goal `toPolyG X = q`** closable purely by transport → `by transfer`.

**Do NOT convert:** curated `simp only [toPolyG_*, coeff_*]` feeding `linear_combination` (coefficient
bashes — leave as-is); single-lemma `simp only [toPolyG_cnormG]` (no gain); anything where
`simp only [denote]` over-fires and breaks a downstream step. **Keep** the `native_decide` zero-test
reflection `RefinesPolyG.eq_of_csub_cisZero` — a distinct capability, not transfer.

When a proof needs a denotation square that is not yet `@[denote]` (e.g. `toPolyG_radDeriv` in
`Algebraic/RadicalDerivationInvariant`), tag it `@[denote]` in its defining file so front-loading works —
that is part of the job.

## Worklist (densest first; update status as you go)

- [x] `Computable/Assemble.lean` — done (template, `baba3648`)
- [x] `Computable/HermiteValuationTower.lean` — done (template, `a5a1ee10`)
- [x] `Computable/OneShotSoundness.lean`
- [x] `Computable/CoupledDE/Assembly.lean`
- [x] `Computable/LaurentSoundness.lean`
- [x] `Computable/RischDE/Structural.lean`
- [x] `Computable/YunTowerCorrect.lean`
- [x] `Computable/FuelFreeDiophantine.lean`
- [x] `Computable/Tower/GcdFFCorrect.lean`
- [x] `Computable/Algebraic/RadicalIntegralSoundness.lean`
- [x] `Computable/TranscendentalOverAlgebraic.lean`
- [ ] sweep the rest: `for f in $(find DeepWiki/SymbolicIntegration -name '*.lean'); do grep -qE "rw \[.*toPolyG_c|simp only \[.*toPolyG_c" "$f" && echo "$f"; done`

After the worklist, run the full gate once (`scripts/check.sh`, bare) to confirm `GATE: PASS` across all
default targets.

## Guardrails

Same as the topic: no change to the executable/`native_decide` path; warnings are errors; one-line
docstrings; `-/` trap; library-not-catalog; commit per gate-green step. The framework itself lives in
`DeepWiki/Transfer/` (topic-agnostic) — do not re-couple it to SymbolicIntegration.
