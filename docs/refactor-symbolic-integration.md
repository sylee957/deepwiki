# Refactoring plan: `DeepWiki/SymbolicIntegration/`

Self-contained instructions for reorganizing the SymbolicIntegration topic. Written to be
executed by an agent without prior conversation context. Read this whole file before
touching anything.

**Scope guard — read first.** This plan has two tracks. **Track A (this document's
executable part)** is a *purely mechanical* file reorganization: `git mv` + import
rewriting + aggregator regeneration. It changes **zero declarations, zero proofs, zero
docstrings** (except module docstrings' titles where they name the file). **Track B**
(§7) is a semantic consolidation done gradually *later*; it is described here only so new
files follow its rules. Do not attempt Track B changes while executing Track A.

---

## 1. Current state (measured 2026-07-02)

- 198 `.lean` files, ~88k lines, in the **flat** directory `DeepWiki/SymbolicIntegration/`.
- 135 files carry the `Computable` prefix — it no longer discriminates anything.
- Overlapping ad-hoc name families: `ComputableTowerRischDE`, `ComputableRischDETowerCorrectG`,
  `ComputableTowerRischDECompleteness`, `ComputableRischDETowerGlue` all exist (permutations
  of the same words).
- Historical variant markers survive in names: `G` (pre–CFracG-unification generic marker;
  ~151 `G`-suffixed defs), `FuelFree` / `WellFounded` / `Wf` (fuel-retirement transition;
  ~105 files still mention fuel), `Full`, `Fast`.
- The aggregator `DeepWiki/SymbolicIntegration.lean` is a raw 195-import hand-ordered list,
  zero section comments.
- Namespaces are healthy and must NOT change: everything under
  `DeepWiki.SymbolicIntegration`, with sub-namespaces `CPolyG` (~90 files), `RadElem`,
  `CFracG`, `Compute`, `GBPolyCore`.
- `Sources/Doi_10_1007_b138171/` (the Bronstein catalog) has 68 distinct
  `import DeepWiki.SymbolicIntegration.*` lines that must be rewritten in lockstep.

## 2. Diagnosis (why reorganize)

File names currently mangle four orthogonal dimensions into one flat string: pipeline
stage (Gcd/Hermite/LogPart/RischDE/…), carrier level (base ℚ(x) / tower / radical /
general curve), artifact kind (engine defs vs soundness vs completeness vs bench), and
historical variant. The fix: **directories encode the carrier-level area; leaf names
encode stage + kind; dead historical markers die (later, Track B); the `Computable`
prefix becomes a directory.**

## 3. Target layout

```
DeepWiki/SymbolicIntegration/          -- abstract theory on Mathlib carriers (~60 files, STAYS FLAT)
│    DifferentialFields, MonomialExtensions, Residues, Liouville*Extension,
│    RationalIntegration*, Rioboo*, Subresultant*, GroebnerBasis, …
├── Compute/                           -- concrete Mathlib-Polynomial ℚ(x) computations (`Compute` namespace)
│    Hermite, Subresultant, RtResultant, LogToAtan, Exercise22, …, Correctness
└── Computable/                        -- the generic executable engine (CField/CPolyG world)
     │   Field, GenericPolyEngine, FuelFreeGcd, GenericBezout, SplitFactor…,
     │   Hermite-, LogPart-, PolyPart-, Parametric-, Structure-, Parallel-, Integrate-,
     │   Liouville*- and OneShot-/Capstone-layer files
     ├── RischDE/    -- base Risch DE: Normal, Special, DegreeBound*, *Cancellation, Solve*, Completeness…
     ├── Hyperexp/   -- Normal, NormalCore, NormalSoundness, Special, LaurentCore, Eta, ExampleData
     ├── CoupledDE/  -- core, Assembly, TangentReconstruct
     ├── Tower/      -- arbitrary-depth towers (CFracG): Field, Deriv, Reduce, GcdFF*, RischDE*,
     │                  Integrate*, Unify, Bench, WellFounded
     └── Algebraic/  -- RadElem / algebraic curves: Radical*, General*, IntegralBasis*, Divisor*,
                        Picard*, Cantor*, Bareiss*, HenselLift, FiniteFieldFactor, Zassenhaus, Decide…
```

Module-name effect: `DeepWiki.SymbolicIntegration.ComputableTowerRischDEWellFounded`
becomes `DeepWiki.SymbolicIntegration.Computable.Tower.RischDEWellFounded`.

### 3.1 Placement rules (apply in this order, first match wins)

| Rule | Current name matches | Target |
|---|---|---|
| 1 | `ComputableTower*` | `Computable/Tower/<rest>.lean` |
| 2 | `ComputableRischDE*` | `Computable/RischDE/<rest>.lean` |
| 3 | `ComputableHyperexp*` | `Computable/Hyperexp/<rest>.lean` |
| 4 | `ComputableCoupledDE*` | `Computable/CoupledDE/<rest>.lean` |
| 5 | `ComputableRadical*`, `ComputableGeneral*`, `ComputableAlgebraic*`, `ComputableAlgFunctionField`, `ComputableHyperelliptic*`, `ComputableDivisor*`, `ComputableGeneralDivisor*`, `ComputableCantor*`, `ComputableTorsion*`, `ComputableRound2*`, `ComputableIntegralBasis*`, `ComputableHensel*`, `ComputableFiniteFieldFactor`, `ComputableZassenhaus*`, `ComputablePolynomialIrreducibility`, `ComputableBareiss*` | `Computable/Algebraic/<rest>.lean` |
| 6 | any other `Computable*` | `Computable/<rest>.lean` |
| 7 | `*Compute` (suffix) and `ComputeCorrectness` — the `Compute` namespace files (`HermiteCompute`, `SubresultantCompute`, `RtResultantCompute`, `RationalFunctionCompute`, `LogToAtanCompute`, `Exercise22Compute`, `Exercise23Compute`, `Exercise25Compute`) | `Compute/<name minus Compute-suffix>.lean` (`ComputeCorrectness` → `Compute/Correctness.lean`) |
| 8 | everything else | stays at top level, unchanged |

`<rest>` = the current basename with the matched prefix (`Computable` + the directory
word) stripped, **all remaining words kept verbatim** — including ugly ones like
`WellFounded`, `G`, `FF`, `Full`. Marker cleanup is Track B; keeping leaves verbatim keeps
Track A collision-free and auditable. Two exceptions:

- If stripping empties the name (`ComputableParallel` → `Parallel.lean`, fine; but a file
  named exactly like its directory, e.g. hypothetically `ComputableTower` → `Tower/`),
  name the leaf `Basic.lean`.
- Rule-5 files keep their distinguishing word: `ComputableRadicalExtension` →
  `Algebraic/RadicalExtension.lean` (strip only `Computable`), `ComputableGeneralCurveDecide`
  → `Algebraic/GeneralCurveDecide.lean`. Do NOT strip `Radical`/`General` — both
  sub-families live in `Algebraic/` and the word disambiguates them.

### 3.2 Ambiguity procedure

Some files are cross-cutting (assembly/capstone/bridge files, e.g.
`ComputableOneShotAssembly`, `ComputableSoundnessCapstone`, `ComputableUnifiedFuelFree`,
`ComputableLiouville*`, `ComputableTranscendentalOverAlgebraic`, `ComputableMixedTowerIntegrate`,
`ComputableElementaryIntegrate`, `ComputableFunctionAlgebraIntegrate`,
`ComputableResidueMatchSoundness`, `IntegrationFunctionsCatalog`). Default them to rule 6
(`Computable/` top level) — the top of `Computable/` is the "whole-pipeline" layer. When a
name alone is ambiguous, read the file's `/-! … -/` module docstring and its imports:
a file importing mostly `Tower/` files belongs in `Tower/`, etc. List every judgment call
in the mapping table (step P2) for the user to review; do not silently decide unusual cases.

## 4. Migration plan (Track A)

### P0 — Preconditions

1. `git status` must be clean (commit or stash any pending work first).
2. Ask the user whether the **fuel-API retirement** (deleting fuel-threaded defs in favor
   of the `Wf`/fuel-free versions) has finished. If it is still in flight, prefer to finish
   it first — it deletes defs/files this plan would otherwise move. If the user says
   proceed anyway, move files as-is (names verbatim per §3.1).
3. Every shell command needs `export PATH="$HOME/.elan/bin:$PATH"` prepended.
4. The gate is `scripts/check.sh [module]` — exit 0 = PASS; it treats warnings and `sorry`
   as failure. Run bare (no args) for the full gate.

### P1 — Sectioned aggregator (zero-risk, independent commit)

Rewrite `DeepWiki/SymbolicIntegration.lean` to group its imports under `/-! ## … -/`
section headers (abstract theory / Compute / engine core / RischDE / Hyperexp / CoupledDE
/ Tower / Algebraic / soundness & capstone) **without changing the set of imports**.
Gate, commit. This commit stands on its own even if the rest is deferred.

### P2 — Mapping table (no code changes; user checkpoint)

Produce `docs/refactor-symbolic-integration-mapping.tsv` with lines
`<OldModuleBasename>\t<NewRelativePath>` for **all 198 files** (rule-8 files map to
themselves — include them so the audit in P4 is total). Apply §3.1; flag every §3.2
judgment call with a trailing `\t# REVIEW: <reason>` comment. **Stop and show the table to
the user before P3.** Check for target collisions (two old files mapping to one new path)
— there must be none.

### P3 — Move + rewrite, phased

Phase order (one commit each, gate-green before the next):

1. `Compute/` (8 files) — smallest, validates the tooling.
2. `Computable/` core (rule 6).
3. `Computable/RischDE/` + `Hyperexp/` + `CoupledDE/`.
4. `Computable/Tower/`.
5. `Computable/Algebraic/`.

For each phase:

```bash
# 1. Move (preserves history):
git mv DeepWiki/SymbolicIntegration/<Old>.lean DeepWiki/SymbolicIntegration/<NewRel>.lean

# 2. Rewrite module references in ALL .lean files (imports in DeepWiki/, Sources/, tools/):
#    exact old flat names only; \b suffices because every old name is a maximal word
#    (process longest names first as extra safety).
perl -pi -e 's/\bDeepWiki\.SymbolicIntegration\.<Old>\b/DeepWiki.SymbolicIntegration.<NewDotted>/g' \
  $(grep -rl "DeepWiki\.SymbolicIntegration\.<Old>\b" DeepWiki Sources tools --include='*.lean')

# 3. Update aggregators (see below), then gate:
scripts/check.sh
```

Aggregator structure after the moves:

- `DeepWiki/SymbolicIntegration/Computable.lean` — imports everything under `Computable/`
  (including the sub-area aggregators).
- `DeepWiki/SymbolicIntegration/Computable/Tower.lean`, `.../RischDE.lean`,
  `.../Hyperexp.lean`, `.../CoupledDE.lean`, `.../Algebraic.lean` — one per subdirectory,
  importing its files. (`Foo.lean` alongside `Foo/` is the standard Lean pattern.)
- `DeepWiki/SymbolicIntegration/Compute.lean` — imports `Compute/*`.
- Root `DeepWiki/SymbolicIntegration.lean` — the flat abstract files + the two area
  aggregators. Alphabetical order within sections is fine (Lean does not require
  dependency-ordered imports).
- Each aggregator file needs a one-line `/-! … -/` module docstring (repo convention).

No `lakefile.toml` change is needed — the `DeepWiki` lib builds by following imports from
its root, and doc-gen4 handles nested modules natively.

### P4 — Post-move audits (same PR, final commit)

1. **No stragglers**: for every old basename in the mapping,
   `grep -rn "SymbolicIntegration\.<Old>\b" . --include='*.lean'` → empty (excluding
   self-maps).
2. **Docs links**: `docs/*.md` (the Risch tutorial etc.) link to local
   `DeepWiki/SymbolicIntegration/<file>.lean#L<n>` paths. Rewrite the path forms per the
   mapping, then run `scripts/regen-doc-links.py` (update its internal path table first if
   it hard-codes old paths). Line anchors stay valid — file contents did not change.
3. **Sources orphan audit** (repo-standard):
   `for d in Sources/*/; do m=$(basename $d); grep -q "import Sources.$m\." Sources.lean || echo "ORPHAN $m"; done`
4. **CLAUDE.md**: amend the "Flat layout — no subdirectories" bullet in
   *Chapter structure & naming* to say: flat is the default while a topic is small; a topic
   that outgrows it (≳50 files) may adopt one to two levels of concept subdirectories, with
   renames batched into dedicated commits; `DeepWiki/SymbolicIntegration/` is the precedent.
   Also record the §3.1 placement grammar there (directories = carrier-level area, leaves =
   stage + kind, kind suffixes `Sound`/`Complete`/`Spec`/`Bench`/`Examples`).
5. **Wiki graph**: `scripts/wiki build` (module graph changed; declaration embeddings
   survive because decl names/signatures/docstrings are unchanged).
6. Full bare gate: `scripts/check.sh` → PASS.
7. **Decl-invariance check**: the whole PR's diff must consist of renames, `import` lines,
   aggregator files, section comments, docs-link paths, and CLAUDE.md — if any diff hunk
   touches a declaration or proof, something went wrong; revert that hunk.

Accept that **doc-gen URLs churn** (module names are the URL scheme; the published wiki is
auto-generated and CI republishes on push) — this is expected, not a failure.

## 5. Hard constraints (do NOT)

- **Do not rename any declaration.** No namespace changes, no def/theorem renames, no
  dropping `G`/`Wf`/`FF` suffixes from *declarations*. `Sources/` aliases target decl
  names; they must keep compiling untouched (only their `import` lines change).
- **Do not edit proofs or statements.** Track A is `git mv` + import lines + aggregators only.
- **Do not merge `Compute/` (the `Compute.*` namespace, Mathlib-`Polynomial`-based) into
  `Computable/` (the CPolyG engine).** A 2026-07 empirical spike refuted that merge: they
  share only a defeq carrier, the math is genuinely separate.
- **Do not split the engine into a sibling `DeepWiki/<OtherTopic>/` library.** Bronstein is
  an algorithms book; the engine *is* the topic's content, and the soundness arc imports
  both layers constantly.
- **Do not introduce `@[implemented_by]`** to attach engine code to abstract defs — it is
  compiler-trusted with no proof obligation.
- Do not commit `references/`, `.wiki/`, or `.lake/` artifacts; do not push unless asked.
- Watch for macOS `" 2.lean"` duplicate files appearing during mass moves — delete any
  untracked ones; they are file-sync artifacts, never imported.

## 6. Naming grammar for NEW files (effective immediately)

- Path = `<Area>/<Stage><Aspect><Kind>.lean`; Area ∈ {top-level abstract, `Compute`,
  `Computable`, `Computable/{RischDE,Hyperexp,CoupledDE,Tower,Algebraic}`}.
- Kind suffix ∈ { ∅ (defs + their satellite lemmas), `Sound`, `Complete`, `Spec`, `Bench`,
  `Examples` }.
- **A name marker earns its place only while both sides of its contrast exist.** `FF`
  (fraction-free vs field gcd) is live — keep. `G` (generic vs the deleted concrete
  carrier), `FuelFree`/`Wf`/`WellFounded` (once fuel retirement lands), `Full`/`Fast`
  (where the counterpart died) are dead — never use them in new names; strip from old
  names opportunistically in Track B.
- No new file takes the `Computable` prefix — the directory says it.

## 7. Track B — semantic north star (LATER; gradual; not part of this execution)

For context so new work follows it; each item is its own future gated effort:

1. **Refinement discipline.** Abstract math lives on Mathlib carriers (Layer 0). The
   engine's only theorems are *commuting squares through a denotation*: for computable
   `f`, one satellite `⟦f x⟧ = F ⟦x⟧` (or `_sound`/`_complete` pair for option-valued
   deciders) **in the defining file**, where the right-hand side is a Layer-0 notion.
   No separate retrofitted `*Correct`/`*Sound` files for new algorithms; existing ones
   fold into their algorithm's file gradually.
2. **`X` / `LawfulX` class pairs** (Lean-core `BEq`/`LawfulBEq` idiom): computable ops in
   a Prop-free class (`native_decide`-friendly); the denotation hom + laws in a `Lawful*`
   companion mentioning the abstract carrier. This is the existing `CField`/`CFieldSpec`
   split — keep it, name new pairs by the idiom.
3. **One `@[denote]` simp attribute** (`register_simp_attr`) collecting all denotation
   homomorphism lemmas, so square proofs are `simp [denote]`-driven — replaces the ~151
   ad-hoc `G`-suffix bridge lemmas.
4. **Algorithms generic over the interface, extensions as instances.** One algorithm
   against `CDiffField α`-style classes; base/tower/radical/general-curve are instance
   constructors. Collapse the per-carrier file quadruplication one family at a time.
5. Worked examples with book-specific data migrate to `Sources/` (existing repo feedback
   convention); `native_decide` remains for examples/benchmarks, not as evidence once
   squares exist.

## 8. Acceptance criteria (Track A done)

- [ ] `scripts/check.sh` bare → `GATE: PASS`.
- [ ] `ls DeepWiki/SymbolicIntegration/*.lean` shows only abstract-theory files + the two
      area aggregators (`Computable.lean`, `Compute.lean`) — no `Computable*`-prefixed
      files remain at top level.
- [ ] Mapping-table audit: every old module name greps to zero hits across `*.lean`.
- [ ] `Sources` orphan audit clean; `Sources/Doi_10_1007_b138171/` compiles untouched
      except import lines.
- [ ] Diff contains no declaration/proof changes (P4.7).
- [ ] `docs/` links regenerated and resolving; CLAUDE.md amended; `scripts/wiki build` run.
- [ ] One commit per phase, each gate-green.
