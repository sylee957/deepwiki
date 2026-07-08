# Migration loop — keep `DeepWiki/` well-organized for random access

A self-contained, Codex-executable loop. The goal: any newcomer landing on any in-scope file by
chance is oriented — predictable names, coherent files, no redundancy, everything where its name
promises. Work gate-green, one file (or a tight cluster) per iteration, driven by your own semantic
exploration with the RAG graph as your constant tool.

## Scope

Everything under `DeepWiki/` **except** the five frozen topics — `MeasureTheory`, `NetworkCalculus`,
`ReactiveSystems`, `RelationalDatabases`, `TimeSeries`. Do not touch those. In scope: `SymbolicIntegration`
(primary), `Transfer`, `Algebra`, and other non-excluded infra. Never edit the executable/`native_decide`
path or change what a declaration *means* — behaviour and statements are preserved; only *shape, name,
location, and redundancy* change.

## The loop

**Run this loop continuously — do not stop after one file.** Keep sampling, fixing, gating, and
committing, file after file, for as many iterations as you can this turn. Do not ask for confirmation
between iterations; make the safe decision and proceed. Only end when you have made many passes and
several fresh random samples in a row need no change — then print `CONVERGED`. If the turn is cut off
by a limit, resume the same loop from a new random sample; there is no per-file hand-back.

**1. Pick a unit of work — alternate two modes, don't only ever sample files.** A random file only ever
reveals *local* fixes (a docstring, a rename); module-scale reorganization is invisible one file at a
time. So alternate:

- **(a) File mode** — sample a random in-scope file and read it as a newcomer (step 2). Take what the
  sample gives you; don't cherry-pick. (Portable reservoir sampler — `shuf` is GNU-only and absent on
  this macOS host; `awk` here is *sampling*, not a bulk edit, so the "never `awk`" move rule doesn't apply.)
  ```
  find DeepWiki -name '*.lean' | grep -vE '/(MeasureTheory|NetworkCalculus|ReactiveSystems|RelationalDatabases|TimeSeries)/' | awk -v seed="$RANDOM$$" 'BEGIN{srand(seed)} rand()*NR<1{l=$0} END{if(l)print l}'
  ```
- **(b) Partition mode — the module-reorganization driver.** Ask the engine for one concrete action:
  ```
  scripts/wiki recommend --prefix=DeepWiki.SymbolicIntegration --seed=$RANDOM
  ```
  It computes a Pareto front per action type — **regroup-theme** (a `uses`-community spanning ≥2 dirs →
  one module), **split-dir** (a grab-bag directory → split), **merge** (a thin module → absorb into its
  neighbour), **move-decl** (a misplaced declaration) — and **stratified-samples one action card** with
  its Pareto objectives and a plan. (Since within a front nothing dominates, sampling is the principled
  selector; the fresh `--seed` rotates you across action types and areas.) Take the card, sanity-check
  it as a newcomer (keep-together guard? does it truly read better?), and make that **module-level
  project** — for a regroup-theme, `git mv` the scattered decls into one module + aggregator and, per the
  "reprove for theme groupings" goal, *unify the near-duplicate parallel lemmas into one abstraction*
  (`wiki rdeps` before moving). If a card is a false positive, re-roll with a new `--seed`; ask for
  `--k=5` to see a slate. This is the bold, cross-module work random file-sampling never surfaces —
  prefer partition mode.

**2. Read it as a newcomer who landed here by chance.** Would someone with no prior context be oriented?
Check: the module `/-! … -/` docstring says what the file is about and matches its contents; the file
holds **one coherent concept**, not a grab-bag; every declaration has a clear one-line docstring and a
**semantic** name; nothing here is redundant with or a special case of something elsewhere; the file is
in the **right place** in the tree.

**3. Use RAG constantly — it is the main tool, not a fallback.** For essentially every declaration you
look at:
- `scripts/wiki search/context "<meaning>"` — is there a similar or duplicate declaration elsewhere?
  (unify / retire / subsume candidate)
- `scripts/wiki show <name>` — signature + docstring + immediate uses / used-by;
- `scripts/wiki deps/rdeps <name>` — what it builds on / its impact set (**always before deleting,
  moving, or renaming**);
- `scripts/wiki recommend --prefix=<namespace> --seed=$RANDOM` — one sampled Pareto action
  (regroup-theme / split-dir / merge / move-decl) with its objectives and a plan; `--k=N` for a slate.
Query liberally; it's cheap and it shows you the whole graph a newcomer can't see.

**4. Fix what's off** (whatever the file needs):
- **retire / unify / subsume — and actually DELETE, don't leave a compatibility layer.** When `wiki
  search` shows two declarations saying the same thing, or one generalizing another, keep the general one
  and retire the redundant one *through* it (`rdeps` first). Crucially: after you rewire the callers,
  **delete the old declaration outright** — do **not** leave a `@[deprecated] alias`, a forwarding
  `abbrev old := new`, a re-export, or a thin wrapper "for compatibility." This library has **no external
  consumers**, and Lean's `rdeps` + the gate let you update *every* caller safely, so a compat shim buys
  nothing and costs a newcomer double the surface to understand. A migration is finished only when the old
  name is *gone*, not aliased. (This is different from the intentional **base + `abbrev`** pattern for
  sharing one definition across two carriers, and from a genuinely-load-bearing wrapper — those stay; only
  *backwards-compatibility* shims for names you are retiring get deleted.) If you find such shims left over
  from an earlier pass, removing them is itself good loop work.
- **regroup / move** — a declaration whose home doesn't fit goes where it belongs.
- **split** — a file doing several things splits along the concept axis into a subdirectory + aggregator.
- **merge** — the inverse of split: a thin file (few decls, weak internal cohesion) whose outward `uses`
  concentrate on one neighbour is a fragment of that neighbour — absorb it and delete the file. The
  `recommend` **merge** action names each thin module and its absorption target; `rdeps` first, then
  move the decls in and `git rm` the emptied file.
- **bundle / re-docstring** — collapse recurring hypothesis clusters into a `Prop` structure; make module
  and declaration docstrings orient a newcomer.

**5. Be bold — moving and renaming are SAFE here, so prefer them over the timid local patch.**

> **Why you can move with confidence.** Lean fully type-checks *every* reference across the whole
> library. A move or rename that breaks anything — a missed import, a stale reference, a wrong
> `namespace` — **cannot** compile: `scripts/check.sh` turns red and names the exact broken site. There
> is no silent breakage, no runtime surprise, no "did I catch every caller?" — the gate answers that
> for you, exhaustively. So a reorganization is *low-risk and fully reversible* (it's a `git` revert if
> the gate ever fails), not a leap of faith. **Treat the type checker as your net and move.** The
> failure mode to avoid is not a broken build (the gate catches that) — it is leaving the library
> disorganized because a move *felt* risky when it wasn't.

A newcomer should be able to *predict* what a thing is called and where it lives, so actively:
- **Rename declarations** to a consistent, semantic scheme; unify naming *families* so the same concept is
  named the same way everywhere (Mathlib's `conclusion_of_hypothesis` order; one term per object across a
  group; `Is<Concept>` predicates; no primed names). If half a family is `…_left`/`…_right` and the rest
  is `…_fst`/`…_snd`, make it uniform in one pass — use `wiki search/context` to find *every* member first.
- **Rename / move files** when the name doesn't match the contents or breaks the directory's naming
  grammar — a newcomer should infer a file's role from its path. Grow a distinct sub-theory into a
  suffixed sibling rather than a misnamed catch-all.
- **Standardize the shape** — uniform module-docstring style, section headers, and hypothesis-binder
  conventions, so every file *feels* the same to read.

**Plan the move in a file first — then execute it mechanically.** For any multi-file reorganization
(a partition-mode regroup, a directory split, a family-wide rename), don't improvise edit-by-edit —
that is what makes an agent hesitate. Write a short scratch plan (`docs/reorg-<theme>.md`, delete it
when the reorg lands) that pins the move down completely *before touching code*, so execution is
rote:
```
# Reorg: <theme>            e.g. the derivation-on-FractionRing cluster
Target module: DeepWiki.SymbolicIntegration.<Dir>.<NewFile>
Decls to move (from `wiki show`/`context`):
  derivation_fractionRing_unique_of_restrict   [Core/Differential/Foo.lean → here]
  existsUnique_derivation_fractionRing         [Compute/Bar.lean          → here]
  ...
Impact (`wiki rdeps` on each): <callers to re-import>
Unify: <near-duplicate lemmas in the cluster to collapse into one abstraction>
Steps: 1) mkdir -p the target dir + create aggregator  2) git mv / move decls  3) fix imports  4) gate  5) unify  6) gate
```
With the plan written, the moves are deterministic; follow it and let the gate confirm each step.

**The plan is scratch — `git rm` it in the same commit the reorg lands in.** `docs/reorg-*.md` is a
throwaway you delete the moment the move is done, in the *same* commit; never leave it behind, never
maintain it, and never edit an *old* landed plan with a "superseded" note — a landed plan is deleted,
not annotated. Durable design rationale goes in the module docstring, not a reorg plan. If you find
stale `docs/reorg-*.md` from earlier passes, deleting them is good loop work.

Bold means larger-scoped, not reckless — the discipline that keeps a bold move clean:
- **Always `scripts/wiki rdeps <name>` first** — a rename touches every reference; the plan lists them,
  then update them all in one deliberate, atomic change (real edits, not `sed`) and gate. Nothing
  half-renamed. (`rdeps` tells you the blast radius up front, so a red gate is a surprise you've already
  ruled out — not a risk you're taking.)
- **A file/module rename** touches every import + the aggregator + doc-gen URLs — do it as a
  **`git mv`-only commit** (imports + aggregator only, zero declaration change), separate from content
  edits, so the gate can verify it's moves-only. Moving into a *new* subdirectory: `git mv` does **not**
  create intermediate dirs and reports a misleading "source … No such file or directory" — `mkdir -p`
  the target directory first.
- **When the gate goes red, it's doing its job** — read the error, fix the named site, re-gate. A red
  gate mid-reorg is normal and expected, not a signal to abandon the move; only an *unfixable* red gate
  (a genuine semantic clash) is a reason to `git` revert and rethink.

## Guardrails

- **Never leave a single-import re-export shim FILE.** The retire-don't-shim rule is not just about
  declaration aliases — a *file* that imports one module, defines zero declarations, and re-exports it
  "for compatibility" is the same anti-pattern at module scale. When you move decls out of `Old.lean`,
  rewire the (few, `rdeps`-listed) callers to import the new home and **`git rm Old.lean`** — do not
  leave it as a one-line forwarding import. A docstring that says "Compatibility aggregator/import" is a
  self-admitted shim: delete it. (A *real* aggregator imports **≥2** sibling modules of a directory it
  heads and carries a `/-! … -/` describing that directory — that stays; a 1-import re-export does not.)
  Finding and retiring leftover shims from earlier passes is good loop work.
- **When you move decls out of a file, fix that file's module docstring in the same edit.** A `/-! … -/`
  that still advertises decls that have moved away misleads the next newcomer worse than no docstring.
  The docstring must always match what the file *now* contains.
- **A split must raise cohesion, not just count files.** Split a grab-bag into files that each hold a
  coherent cluster of *related* declarations; do **not** manufacture single-declaration or single-import
  leaf files just to make the tree deeper — that trades a real navigation cost for no cohesion gain and
  is over-refactoring. If a proposed piece would be one decl with one import, it belongs *in* its
  sibling, not in its own file. Aggregators (import-only directory heads) are the *only* legitimate tiny
  files.
- **Keep conceptually-bonded pairs together** — symmetric siblings (`_mul_left`/`_mul_right`, `_add`/`_sub`,
  `Minimal`/`Maximal`), near-identical docstrings, high `dis` in the regroup vector — even when their
  `uses`-dependencies differ. The structural view misleads there; do not split them.
- **Don't churn for its own sake.** Boldness is warranted when it raises *uniformity and predictability*
  for a newcomer — not for cosmetic renames that change names without making the library more guessable.
  The test for any change: *does this make the codebase more predictable to someone who's never seen it?*
  If yes, do the big version; if no, leave it and move to the next sample.
- **Move deliberately, never by script** — no `sed`/`awk` bulk moves; real edits so imports, `namespace`s,
  and proofs stay correct.
- **Frozen topics and the executable/`native_decide` path are off-limits.**

## Log tooling friction to `feedbacks/`

The RAG graph and this loop are themselves works in progress. Whenever a tool or step **surprises you** —
`wiki search`/`context`/`recommend` missed something or pointed at the wrong change, the index was stale,
the gate or doc-gen behaved oddly, a convention fought the natural change — **write a short note in
`feedbacks/`** (see `feedbacks/README.md` for the format) *in the same turn*, before you forget the
detail. A friction that is only felt and never recorded gets re-hit by the next agent. This is a standing
duty, not optional: over-recording a small friction is cheap; a silently re-hit RAG blind spot is not.
These notes are how the tools get better — treat improving them as part of the loop.

## Refresh, gate, commit

- After a batch of structural changes (not every edit), re-run `scripts/wiki build` (module structure +
  `uses`), then `scripts/wiki cochange` and `scripts/wiki index` if you want the `evo`/`con` signals
  current — so the next iteration's candidates reflect the new structure.
- `scripts/check.sh <module>` per file, then bare `scripts/check.sh` before finishing — must print
  `GATE: PASS` (warnings are failures). Restate a changed theorem as an `example` if a change is subtle.
  **Run gates one at a time — never two `scripts/check.sh` concurrently.** Parallel `lake build`s race
  on generated `.setup.json`/IR artifacts and produce a *spurious* `unexpected end of input` failure
  unrelated to your edit; the loop is sequential, so keep gates sequential too.
- Commit per logical change with a clear message; keep pure `git mv` splits/renames in their own commits.
  **Stage explicitly and verify before committing** — after `git add`, check `git status` (a failed
  `git add` pathspec does **not** abort the following `git commit`, which will then commit only whatever
  was already staged — a partial commit). Prefer `git add -A -- <moved-paths> <plan-doc>` and confirm the
  staged set is the whole change. Don't push unless asked.

Repeat, sampling fresh files, until random samples consistently read as already well-organized and
uniform to a newcomer.
