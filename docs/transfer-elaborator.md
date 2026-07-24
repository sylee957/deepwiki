# Plan: a `transfer` elaborator plugin (the Lean Trocq analog)

**Status:** DONE (all phases; gate-green) · **Owner:** autonomous agent · **Repo:** `deepwiki` (Lean 4, v4.32.1)

## Why (the finding that motivates this)

The CoqEAL `⟹`/`refines_apply` pure-typeclass kernel **does not work in Lean 4**: selecting
`refines_app : Refines (R ⟹ S) f g → Refines R a b → Refines S (f a) (g b)` requires unifying
`?g ?b =?= cop x y` — a metavariable function head — which Lean's TC unifier cannot solve, so the
composition never fires (confirmed empirically, even at priority 5000; the atom rule always wins).
This is exactly why **Trocq is a Coq-Elpi plugin** and CoqEAL leans on canonical structures.

The working Lean analog is a **metaprogram** that does the recursive decomposition itself (the HOU that
TC won't), synthesizing the abstract term + proof. `simp only [denote]` already performs the recursive
decomposition for the functional (`toPolyG`) case; the elaborator's unique value over raw `simp` is
**handing back the abstract term as first-class data** (RHS computed, not hand-written) — solving the
`= _` hole problem where Lean elaborates the type before the tactic runs.

## Architecture

- **`transfer% e`** (term elaborator): elaborate `e` (a denotation application `φ b`), normalize it via
  the `denote` simp set to its abstract form `a`, and produce a **proof term of `e = a`** with `a`
  *computed*. Usage: `have h := transfer% (toPolyG (cmulG (caddG p q) r))` gives
  `h : toPolyG … = (toPolyG p + toPolyG q) * toPolyG r` without writing the RHS.
- **`transfer` (tactic)**: whole-goal — rewrite every denotation application in the goal to its abstract
  form (built on the same normalization; deterministic because the `denote` lemmas are confluent toward
  the abstract side). Closes `φ b = q` goals; leaves the residual otherwise.
- **Registry:** reuse the existing `@[denote]` simp set (already the op-squares `toPolyG_cmulG`, …).
  No new attribute needed for the functional case; the elaborator reads the `denote` `SimpExtension`.
- **Generality:** works for any denotation whose squares are `@[denote]` (`toPolyG`, `toK`, `radDeriv`),
  since it is driven by the simp set, not a fixed carrier.

## Phases

1. **`transfer%` term elaborator** — the core: elaborate + `simp only [denote]` normalize + return the
   proof. Test: the RHS-synthesis examples that `simp`/TC couldn't do. ← *building now*
2. **`transfer` tactic** — whole-goal rewrite via the same normalization; close equality goals.
3. **Validation** — reproduce the `RefinesPolyG` synthesis examples through `transfer%`; check whole-goal
   transfer on a `natDegree`/`dvd` goal (the relation-general reach).
4. **Retire / reconcile** — DONE. The elaborator `transfer`/`transfer%` supersede the aesop machinery:
   - `Computable/DenoteHom.lean` (classes + `derive_denote_hom` generator) **deleted** — 0 external uses.
   - `RefinesPolyG.lean` **trimmed** to the zero-test reflection core (`RefinesPolyG` def,
     `refinesPolyG_self`, `sub`, `eq_zero_of_cisZero`/`ne_zero_of_cisZero_false`,
     `eq_of_csub_cisZero`/`ne_of_csub_cisZero_false`) — the `native_decide` `cisZeroG` bridge, a distinct
     capability transfer does not cover. The aesop `transfer` macro, `hom₁`/`hom₂`, the `DenoteHom`
     instances and 10 `derive_denote_hom` calls are gone.
   - `Denote.lean` **trimmed**: dropped the `Refines` aesop rule set and the `refines` label attr
     (only the retired machinery used them); `register_simp_attr denote` stays (drives `transfer`).
   - The single external `by transfer` (LrtResidueResultantDischarge) migrated to `simp only [denote, hg1, hg2]`.
   - `Transfer` added to the `Computable` aggregator. Full gate green.

## Guardrails

Same as `docs/denotation-transfer-cleanup.md`: no change to the executable/`native_decide` path;
warnings are errors; one-line docstrings; commit per gate-green step; `scripts/wiki rdeps` before any
retire. The elaborator lives in a new `Computable/Transfer.lean`; nothing in `defaultTargets` breaks.
