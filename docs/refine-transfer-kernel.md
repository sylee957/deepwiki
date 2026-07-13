# Refine — a relational proof-transfer kernel for Lean (CoqEAL/Trocq analog)

**Status:** ACTIVE (started 2026-07-13). Isolated, relation-based, **no `simp`**. Scope chosen by
user: *minimal refinement kernel* (single relation level).

## Goal

An isolated Lean 4 transfer framework in the style of Isabelle `Transfer` / CoqEAL / **Trocq**
(ITP'24, TOPLAS'25; `rocq-community/trocq`) — the principled relational logic, not the `simp`/`@[denote]`
approximation in `DeepWiki/Transfer`. Motivation: refine proof-oriented Mathlib carriers
(`Polynomial`, `RatFunc`, …) to computation-oriented ones (`DensePoly`, `DenseFrac`) and transfer
theorems across. No Lean 4 port of this exists (the Lean Zulip parametricity thread is theory-only).

## Done (the logical kernel) — `DeepWiki/Refine/`

- `Refine/Basic.lean`: `Refines R c a` class; the respectful arrow `Respectful`/`⟹` (relations lifted
  to function types); the single composition rule `Refines.app` (CoqEAL `refines_apply`); the
  functional relation `DenoteRel denote` + leaf rule `refines_denote`.
- `Refine/Poly.lean`: per-op `Refines` witnesses for `DensePoly ⇄ Polynomial` (mul/add/sub/neg). Demo:
  `(p+q)*r - s` transfers to its `Polynomial` denotation by **pure `Refines.app` composition** — zero
  `simp`. This is the relational abstraction theorem instantiated by hand.

## ← NEXT: the `MetaM` resolver (the Trocq-Elpi analog)

Automate building the `Refines.app` tree so the user writes `refine_transfer%`/`refine_transfer`
instead of a nested composition by hand.

**Key design insight (why this can be done, and why TC couldn't):** the repo's old `transfer` docstring
noted typeclass synthesis won't solve `?g ?b =?= cop x y` (the head/arg split). But a metaprogram
**can**, because **`isDefEq` performs exactly that higher-order (beta) matching**: for a witness with
concrete op `F` and arity `k`, `isDefEq c (F ?x₁ … ?xₖ)` beta-reduces `F` and unifies, binding the
`?xᵢ`. So the resolver is `isDefEq`-driven, not TC-driven and not `simp`-driven.

Algorithm `resolve (c : Expr) : MetaM (a : Expr × proof : Expr)` — `proof : Refines R c a`:
1. For each registered witness `w : Refines (R ⟹ … ⟹ R) F G` (arity `k`, read off from the `⟹`
   count in `w`'s type): make `k` fresh mvars `xs`; if `isDefEq c (mkAppN F xs)` succeeds,
   - recurse: `(xs'ᵢ, pxᵢ) ← resolve (xs ᵢ)`,
   - abstract `a := mkAppN G xs'`,
   - proof `:= xs.foldl (fun acc (px) => mkAppM ``Refines.app #[acc, px]) w`,
   - return `(a, proof)`.
2. Leaf (no witness matches): `a := denote c`, `proof := refines_denote denote c` (extract `denote`
   from the goal relation `R = DenoteRel denote`).

Implementation caveats (found while designing):
- Instantiate each witness's own binders (`{R} [CommRing R] [DecidableEq R]`) with
  `forallMetaTelescopeReducing`; after `isDefEq c (F ?xs)` fixes `R`, the instance mvars must be
  **synthesized** (`synthInstanceMVars` / `synthAppInstances`) before `mkAppM ``Refines.app` — else the
  proof term has unassigned instance holes.
- Arity = count nested `Respectful` in the witness's `rel` (peel `rel.getAppFnArgs = (``Respectful,
  …, RB)` and recurse on `RB`). `Respectful` is `@[reducible]`, so `whnf`/`getAppFnArgs` see it.

Layers:
- **3a** — a `@[refines]` attribute + `SimpleScopedEnvExtension` mapping the concrete op's head constant
  → witness const name (indexed lookup instead of scanning all witnesses).
- **3b** — the `resolve` recursion in `MetaM` (above), + `refine_transfer%` term elab (returns
  `Refines R c (computed a)`) and `refine_transfer` tactic (closes `Refines R c ?a` / rewrites a goal
  through the transfer).
- **3c** — witnesses for `DenseFrac ⇄ RatFunc`, `deriv`, and the `n`-ary / constant leaves (`0`, `1`,
  `C x`) so closed terms transfer end-to-end.

## Honest scope

The single-relation-level kernel is a few hundred lines and directly usable on our `equiv`s; it is
NOT the full Trocq lattice (proof-relevant, univalence-optional, dependent — research-grade). For our
functional (denotation) relations the resolver's payoff is producing the *decomposed* abstract form
(`denote((p+q)*r)` ⤳ `(denote p + denote q)·denote r`); the honest prior finding
([[leanproofs-refinement-transfer-layer]]) is that transport is a readability win, not a line-count
win. Relevance: Phase 6 of the CAlgebra rewrite (re-anchoring the Risch engine) is mass proof-transfer,
so this tooling serves it directly.
