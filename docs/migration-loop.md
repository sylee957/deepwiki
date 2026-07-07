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
  sample gives you; don't cherry-pick.
  ```
  find DeepWiki -name '*.lean' | grep -vE '/(MeasureTheory|NetworkCalculus|ReactiveSystems|RelationalDatabases|TimeSeries)/' | shuf | head -1
  ```
- **(b) Partition mode — the module-reorganization driver.** Run the global partition-diff and take a
  *whole cluster* as the unit of work:
  ```
  scripts/wiki modularity --prefix=DeepWiki.SymbolicIntegration --top=15
  ```
  The **COMMUNITIES** block lists `uses`-communities that span ≥2 directories — scattered mathematical
  themes (high `coh`/`con`, module-sized) that *should* be one module but aren't. The **DIRECTORY
  FRACTURE** block lists directories split across many communities — grab-bags to break up. Take the
  top-scoring theme (or the lowest-purity directory) and make the **module-level project**: `git mv`
  the scattered decls into one module/subdirectory + aggregator, and — per the "reprove for theme
  groupings" goal — *unify the near-duplicate parallel lemmas inside the theme into one abstraction*
  (`wiki search`/`context` to find every member; `rdeps` before moving). This is the bold,
  cross-module work random file-sampling never surfaces. Run partition mode at least as often as file
  mode; prefer it whenever a fresh run still shows a high-score community or a low-purity directory.

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
- `scripts/wiki modularity --prefix=<namespace>` — cross-check split / regroup / coupling and read the
  `(str, con, evo, dis)` vector.
Query liberally; it's cheap and it shows you the whole graph a newcomer can't see.

**4. Fix what's off** (whatever the file needs):
- **retire / unify / subsume** — when `wiki search` shows two declarations saying the same thing, or one
  generalizing another, keep the general one and retire the redundant one *through* it (`rdeps` first).
- **regroup / move** — a declaration whose home doesn't fit goes where it belongs.
- **split** — a file doing several things splits along the concept axis into a subdirectory + aggregator.
- **bundle / re-docstring** — collapse recurring hypothesis clusters into a `Prop` structure; make module
  and declaration docstrings orient a newcomer.

**5. Be bold — prefer the uniformity-raising change over the timid local patch.** A newcomer should be
able to *predict* what a thing is called and where it lives, so actively:
- **Rename declarations** to a consistent, semantic scheme; unify naming *families* so the same concept is
  named the same way everywhere (Mathlib's `conclusion_of_hypothesis` order; one term per object across a
  group; `Is<Concept>` predicates; no primed names). If half a family is `…_left`/`…_right` and the rest
  is `…_fst`/`…_snd`, make it uniform in one pass — use `wiki search/context` to find *every* member first.
- **Rename / move files** when the name doesn't match the contents or breaks the directory's naming
  grammar — a newcomer should infer a file's role from its path. Grow a distinct sub-theory into a
  suffixed sibling rather than a misnamed catch-all.
- **Standardize the shape** — uniform module-docstring style, section headers, and hypothesis-binder
  conventions, so every file *feels* the same to read.

Bold means larger-scoped, not reckless:
- **Always `scripts/wiki rdeps <name>` first** — a rename touches every reference; update them all in one
  deliberate, atomic change (real edits, not `sed`), then gate. Nothing half-renamed.
- **A file/module rename** touches every import + the aggregator + doc-gen URLs — do it as a
  **`git mv`-only commit** (imports + aggregator only, zero declaration change), separate from content
  edits, so the gate can verify it's moves-only.

## Guardrails

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

## Refresh, gate, commit

- After a batch of structural changes (not every edit), re-run `scripts/wiki build` (module structure +
  `uses`), then `scripts/wiki cochange` and `scripts/wiki index` if you want the `evo`/`con` signals
  current — so the next iteration's candidates reflect the new structure.
- `scripts/check.sh <module>` per file, then bare `scripts/check.sh` before finishing — must print
  `GATE: PASS` (warnings are failures). Restate a changed theorem as an `example` if a change is subtle.
- Commit per logical change with a clear message; keep pure `git mv` splits/renames in their own commits.
  Don't push unless asked.

Repeat, sampling fresh files, until random samples consistently read as already well-organized and
uniform to a newcomer.
