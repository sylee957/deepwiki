# CLAUDE.md

Guidance for working in this repository.

## What this project is

**DeepWiki** — an AI-generated wiki of autoformalized mathematics (lake package
`deepwiki`). Topics are organized as sibling Lean chapter sets under `DeepWiki/`,
with source catalogs in `Sources/`.

It is a **plain Lean library**: real `def`/`theorem`/`instance` declarations live in
`DeepWiki/<Topic>/*.lean` chapter files as ordinary top-level Lean, each with a concise
one-line `/-- … -/` docstring and a `/-! … -/` module docstring per file. Each topic
has an aggregator `DeepWiki/<Topic>.lean`; `DeepWiki.lean` is the library root.
Rendered docs come from **doc-gen4** (standard Lean API documentation).

**Two-layer architecture** (one lake package, two libs):
- **Topic library** `DeepWiki/<Topic>/` — the book-number-free general theory (the
  chapter files).
- **Source catalogs** `Sources/<slug>/` — per-book, DOI-keyed. One or more `alias`/`abbrev`
  entries per book item, named by its book number (`Dnc.prop_10_1`, `Dnc.def_2_7`), linking to the
  library, with §/page in the docstring and the DOI in `Sources/<slug>/Source.lean`. The
  folder is named by the **sanitized DOI** (`Sources/Doi_10_1002_9781119440284/` — `/`
  and `.` → `_`, `Doi_` prefix because Lean module names can't start with a digit); the
  declaration namespace stays a short slug (`DeepWiki.Dnc`). Book numbers live **only** in
  the catalog — the library stays number-free. Every topic gets `DeepWiki/<Topic>/` over
  the same `Sources/` layer.
  - **The catalog is the complete coverage map.** A **formalized** book item is an
    `alias`/`abbrev`; the **still-missing** items of a chapter are listed in a
    `## NOT YET FORMALIZED` block (a `/-! … -/` section in that `Chapter*.lean`), one item per
    entry with a reason tag — `[deferred]` (engine exists; needs figure OCR / a judgment call,
    do with the user), `[infra]` (needs a representation or solver layer not yet built),
    `[research]` (research-grade / open), `[external]` (proof lives in a cited paper). So
    scanning a chapter shows exactly what is and isn't done, and **why** for the gaps. The
    block is **subtractive** (see [[feedback-subtractive-missing-markers]]): when an item is
    formalized, **delete its line** (no "done" notes, no "Done:" summary) in the same commit —
    an empty block means the chapter is complete. Enumerate items **one by one, never a range**
    (`Lemma 4.4.1; Lemma 4.4.2`, not `4.4.1–4.4.4`). The book drives what to record: a research
    monograph with no exercises records none; an erratum / non-theorem is cataloged as the
    repaired statement with the misprint noted. **Completion and missing-item status lives in
    the catalog, never in memory** — memory keeps only what the catalog cannot (correctness
    adjudications, reusable Lean lessons, project context). Keep all topic catalogs consistent
    with this block format.
- **Per-paper source catalogs.** A result the library takes from (or a book *defers to*) an
  individual **paper** gets its **own** `Sources/Doi_<sanitized-doi>/` catalog — a
  `Source.lean` (paper DOI + title + authors, short author-slug namespace, e.g.
  `DeepWiki.Llw`) plus catalog files pointing at the library theorems derived from it. Add
  this paper pointer **even when the book already references the paper** ("double
  reference"): the paper catalog is what lets a reader go straight to the *individual paper*
  (DOI in hand) rather than only the book. Collected reference papers live (gitignored) in
  `references/`, named freely; their DOI is recorded in the paper's `Source.lean`. Same
  sanitized-DOI folder rule as books (`Sources/Doi_10_7146_brics_v2i2_19504/`).

**Do not reintroduce Verso *into the library*.** The `DeepWiki/` chapters and `Sources/`
catalogs are plain Lean + doc-gen4: no `import VersoManual`, `#doc`, or ` ```lean ` blocks,
and no book declarations inside elaborated blocks (the library was once a Verso "Manual" and
was converted away for build-time reasons). If a root-level `Main.lean`, `VersoParse.lean`,
an `Introduction.lean`, or `"<Chapter> 2.lean"` duplicate reappears, it is stale — delete it.

There is currently no Verso target in `lakefile.toml`. If a standalone prose target is
reintroduced later, keep it out of `defaultTargets` and update this guidance in the same
commit.

## The autoformalization loop

When the user posts a capture/screenshot of a book passage or points at PDF pages in
`references/`, formalize it into the appropriate chapter:

1. **Read by OCR, never text extraction.** Transcribe theorem/definition statements only
   from *rendered* pages — the Read tool's PDF rendering (`pages` param, ≤20 pages/request),
   or if it errors on `pdftoppm` (stale extension PATH; poppler is installed) render
   manually: `pdftoppm -png -r 110 -f <p> -l <p> <pdf> /tmp/page` then Read the PNGs. Raw
   `pdftotext`/content scraping garbles math glyphs and statement *shape* (it has caused a
   misread quantifier structure); use `pdftotext -layout` only to grep for which page holds
   a passage. `references/` is a **gitignored** local dump; its PDFs are named by DOI
   (`references/10.1002_9781119440284.pdf` is the DNC source book).
2. **Search before writing.** Use `scripts/wiki` (below) to find the lemmas/definitions to
   build on — reuse and extend rather than redefine.
3. **Write** in the right chapter, in `namespace DeepWiki`, following the chapter DAG and
   the math orientation, gotchas, docstring, and naming/style conventions below. Mind the
   numeric-vs-dioid order inversion when transcribing inequalities.
4. **Gate** with `scripts/check.sh` (warning-/sorry-free).
5. **Check source fidelity** by elaborating the expected type against the book's wording
   while developing. Do not retain a thin anonymous `example` whose proof merely forwards
   to the named theorem; keep an `example` only when it adds a substantive computation,
   elaboration regression, or worked use case.
6. **Catalog** the book item in `Sources/<slug>/Chapter*.lean` (alias/abbrev + §/page
   docstring). The catalog file must `import` the chapter that defines the aliased
   declaration, or the build fails. Keep the catalog a **complete subtractive coverage map**
   (see Two-layer architecture): items you did *not* formalize get a reason-tagged
   `not formalized` note so the chapter file shows the whole gap list; status lives here, not
   in memory.

## Build & gate

- Toolchain `leanprover/lean4:v4.31.0` (`lean-toolchain`). Prepend
  `export PATH="$HOME/.elan/bin:$PATH"` to every `Bash` invocation (the shell is
  non-interactive and may not load `~/.zshrc`). Deps pinned to `v4.31.0`: `mathlib`,
  `doc-gen4`.
- `lakefile.toml`: libs `DeepWiki` (root `DeepWiki.lean`) and `Sources`;
  `defaultTargets = ["DeepWiki", "Sources"]`. The `Sources` lib has **no globs**, so every new
  `Sources/<folder>/` catalog module must be `import`ed into `Sources.lean` (the lib root) — an
  un-imported catalog is **silently skipped by the gate** (it compiles only under an explicit
  `lake build Sources.<mod>`), a false `GATE PASS`. Audit:
  `for d in Sources/*/; do m=$(basename $d); grep -q "import Sources.$m\." Sources.lean || echo "ORPHAN $m"; done`.
- Build one module: `lake build DeepWiki.<Topic>.<Module>`. Everything: `lake build`.
- **Gate: `scripts/check.sh [DeepWiki.<Topic>.<Module>]`** — runs the full
  `lake build`, exit `0` = `GATE: PASS`, `1` = `GATE: FAIL`. Treats
  `warning:`/`error:`/`declaration uses 'sorry'` as failure *even when lake itself exits 0*
  (lake exits 0 on `sorry`), enforcing the warning-/sorry-free requirement. Pass a module
  target for fast mid-iteration feedback; run bare (all default targets) as the final gate.
  Avoid hard-coding build-size or timing assumptions here; the closure grows with the library.
- Render docs: `DOCGEN_SRC=file lake build DeepWiki:docs Sources:docs` → `.lake/build/doc/`
  (gitignored). Needs a `references.bib` at the doc root (`touch` an empty one if rendering
  fails on it missing). If doc-gen "Replays" stale HTML, remove its facet markers
  (`.lake/build/doc-data/DeepWiki--library.docs_built*`) and the `.lake/build/doc` tree,
  then rebuild.

## Navigating with `scripts/wiki`

A local graph-RAG CLI over the compiled library (`lake exe wiki`; sources in
`tools/WikiRAG/`, own `README.md`). Extracts the `DeepWiki`+`Sources` environment into
`.wiki/graph.db` (gitignored): declaration nodes, the *exact* intra-library `uses` edges
(`ConstantInfo.getUsedConstantsAsSet`, over type and value), a module graph, and optional
local Ollama embeddings. **Prefer it over `grep` for structural questions** — it answers
exactly rather than by text match.

- `rdeps <name> [--depth D]` — dependents / impact set; run *before* changing or renaming a
  declaration.
- `deps <name> [--depth D]` — what a declaration builds on (proof context).
- `path <a> <b>` — a shortest `uses`-path between two declarations.
- `search <q>` (lexical) / `context <q>` (lexical + semantic) — locate by meaning;
  `show <name>` gives signature + docstring + immediate uses/used-by. Short names
  auto-resolve; `--json` for machine output.

Maintenance: `scripts/wiki build` after library changes (preserves embeddings for decls
whose name/kind/signature/docstring are unchanged), then `scripts/wiki index` re-embeds the
new/changed ones (needs a local Ollama server; default `nomic-embed-text`); `reindex` to
change model. `WikiRAG`/`wiki` are out of `defaultTargets`, so the gate is untouched.

The `recommend` subcommand emits **one sampled Pareto action** over the graph
(`--prefix`, `--seed`, `--k`): each action type — **regroup-theme** (a `uses`-community spanning
≥2 dirs → one module), **split-dir** (a grab-bag directory → split), **merge** (a thin module →
absorb into its neighbour), **move-decl** (a misplaced declaration) — is a Pareto front over its
own objectives (no weighting); it stratified-samples one action card with objectives + a plan.
Communities cluster with weighted Louvain over `uses` edges reinforced by conceptual (`--wcon`)
and co-change (`--wevo`) weight. Use it, not intuition, to decide *what modules should exist*.

**Log tooling/workflow friction to `feedbacks/`.** When `scripts/wiki` (RAG) misleads you or
misses something, the index is stale, or the gate/doc-gen/a convention behaves surprisingly,
write a short dated note in `feedbacks/` (format in `feedbacks/README.md`) *in the same turn* —
so the next agent doesn't re-hit it and the tools actually improve. This is for *tooling &
process* friction only; math adjudications and coverage status still go to memory and `Sources/`.

## Chapter structure & naming (`DeepWiki/NetworkCalculus/`)

Each chapter: imports first, then a `/-! … -/` module docstring, then declarations in
`namespace DeepWiki` (sub-namespace `Deviation` for the backlog/delay theory, whose short
names would clash with the curve catalog). Chapters `import` earlier chapters to form the
dependency DAG; `DeepWiki/NetworkCalculus.lean` is the live ordered chapter list (don't
duplicate it here). **Flat layout** is the default *while a topic is small*; a second topic
gets its own sibling `DeepWiki/<Topic>/` library (module renames touch every import and
doc-gen URL, so this is done once per topic, not per chapter). A topic that outgrows flat
(≳50 files) may adopt **one to two levels of concept subdirectories**, with the renames
batched into dedicated `git mv`-only commits (imports + aggregators only, zero declaration
changes); `DeepWiki/SymbolicIntegration/` is the precedent. Its placement grammar:
**directories encode the carrier-level area** (`Compute/` = the concrete ℚ reference layer,
`Engine/` = the generic executable Risch engine, and under the engine
`Engine/{RischDE,Hyperexp,CoupledDE,Tower,Algebraic}/`), **leaf names encode
stage + kind**, and **dead historical markers are dropped opportunistically** (never the
directory-implied `Engine` prefix). Kind suffixes: `Sound` / `Complete` / `Spec` /
`Bench` / `Examples`. A subdirectory gets an aggregator `Foo.lean` alongside `Foo/`, and the
topic root imports the area aggregators rather than every leaf.

- **Chapter names:** base concept first, qualifiers appended as suffixes so siblings sort
  together alphabetically — `ServiceCurveStrict`, `ArrivalCurvesShaper`,
  `ArrivalCurvesShaperGreedy`. Grow a distinct sub-theory into a suffixed sibling, not a
  bigger file. Counterexample-ladder chapters take suffix `Strict`
  (`ServersConcatenationStrict`, `ServiceCurveVariableCapacityStrict`); when the parent name
  already ends in or contains `Strict`, use `Strictness` (`ServersResidualStrictness`,
  `ServiceCurveWeaklyStrictStrictness`).
- **Singular vs plural:** plural for the theory of a class of objects (`Dioids`, `Servers`,
  `RealCurves`, `ArrivalCurves`, `Deviations`, `Closures`); singular for one operation,
  property, or distinguished concept (`Deconvolution`, `Continuity`, `PseudoInverse`,
  `ConvolutionMinimum`, `SubDioid`, `ConcaveDioid`). A family head is frozen verbatim across
  every sibling — the prefix is an identifier, not prose (`ArrivalCurves*` throughout, never a
  mixed `ArrivalCurve*`/`ArrivalCurves*` family). `ServiceCurve*` predates the rule and stays
  singular: within-family uniformity is the binding part.

## The mathematics (orientation — get this right or proofs invert)

- A **dioid** is `IdemCommSemiring`; the dioid sum `⊕ = +` is the lattice join
  `⊔`/`⨆`, the product `⊗ = *`, zero `𝟘 = 0`, unit `𝟙 = 1`, canonical order `≼ = ≤`.
- `CompleteDioid` adds a `CompleteLattice` + lower semi-continuity
  `mul_sSup : a * sSup s = ⨆ b ∈ s, a * b`.
- **Carriers are order-duals.** For (min,plus), the dioid order is the *reverse* of
  the numeric order (so `⊕ = min`, `𝟘 = +∞ = ⊥`). Each carrier is a one-field
  **`structure`** wrapping its numeric type, NOT a transparent `Mᵒᵈ` synonym — see
  gotcha below. A value `v` has underlying numeric value `v.toVal`; the constructor
  is `ofVal` (uniform across all five carriers).
- The **natural (numeric) order is the reverse of the dioid order.** "Non-negative",
  "non-decreasing", "sub-additive `f(s+t) ≤ f(s)+f(t)`" are *natural*-order notions,
  stated on `.toVal` values with numeric `+`. The *dioid* order (`≤` on the newtype)
  is what isotony / Kleene-star / convolution-as-product use.
- Carriers (newtypes in `DeepWiki/NetworkCalculus/ScalarDioids.lean`, sense + number-system names):
  `MinPlus` over `WithTop ℝ` (dioid, `R∪{+∞}`); `MinPlusNN` over `ℝ≥0∞` (complete);
  `MinPlusExt` over `WithTop (WithBot ℝ)` (complete, `R∪{±∞}`); plus the (max,plus)
  duals `MaxPlusNN` over `WithBot ℝ≥0∞` and `MaxPlusExt` over `WithBot (WithTop ℝ)`.
- The convolution `conv` (notation `∗`) is generic over `CompleteDioid`; the function
  dioid (`DeepWiki/NetworkCalculus/FunctionDioids.lean`) and the function classes `FPlus`/`FNondecr` are
  subtypes built by `IsSubCompleteDioid.toCompleteDioid` (the sub-complete-dioid
  builder in `DeepWiki/NetworkCalculus/CompleteDioids.lean`).

## Hard-won gotchas (read before editing)

1. **Newtype, not `OrderDual`.** `Mᵒᵈ` is a transparent type synonym, so it inherits
   *all* of `M`'s instances — including a stray `Mul` from carriers like `ℝ≥0∞` /
   `WithTop (WithBot ℝ)` that have native numeric multiplication. That stray `*` is
   NOT the dioid product and silently wins instance resolution. The fix throughout is
   to wrap carriers in a one-field **`structure`** (`MinPlus`, `MinPlusExt`, … each
   with `ofVal ::`/`toVal`) that inherits nothing, and attach the lattice + dioid
   algebra explicitly. Same for the function space (`Pi.commSemiring` has the wrong,
   pointwise `*`).

2. **`R̄min` needs `WithTop (WithBot ℝ)`, NOT `EReal`.** They are defeq types but have
   *different* addition: the book's convention is `(+∞)+(−∞) = +∞` (so `𝟘 = +∞` stays
   absorbing), which is exactly `WithTop`'s top-absorbing addition. `EReal` uses
   `(+∞)+(−∞) = −∞`, which breaks `mul_zero` — it isn't even a dioid under min-plus.

3. **`nsmul`/`natCast` defaults don't reduce** through the `min`-on-the-dual addition.
   The builder supplies them in closed form (idempotent: `n • a = a` for `n ≥ 1`)
   rather than via `nsmulRec`/`Nat.unaryCast`.

4. **Carrier/analysis boundary: dioid ALGEBRA stays on the WithTop/WithBot carriers;
   real ANALYSIS routes through `toEReal` (extends gotcha #2).** The two-sided extended
   carriers — `MinPlusExt` over `WithTop (WithBot ℝ)` (top-absorbing) and its dual
   `MaxPlusExt` over `WithBot (WithTop ℝ)` (bot-absorbing) — must keep their *absorbing*
   addition: that is exactly what makes `𝟘` absorbing and `mul_zero` hold. `EReal` has the
   opposite convention on one side (`(+∞)+(−∞) = −∞`) and is **not** a dioid under it, so
   do **not** "naturally" swap a carrier to `EReal` to borrow its topology — it silently
   breaks `mul_zero`. Instead, keep the algebra on the WithTop/WithBot carrier and do all
   *analysis* (limits, continuity, lsc, convolution-minimum) on `EReal` via the `toEReal`
   cast (`DeepWiki/NetworkCalculus/MinPlusExtTopology.lean`, and the max dual). The cast agrees with the dioid
   `+` *exactly* on the open `AddDefined` region (no `(+∞)+(−∞)` collision), so add an
   `AddDefined` hypothesis wherever a proof needs the two additions to coincide. Bridge
   entry points: `toEReal`, `toEReal_add`, `AddDefinedExt`,
   `continuousAt_add_of_addDefinedExt`.

## Docstring conventions

- Every named declaration (`def`/`theorem`/`lemma`/`class`/`structure`/`abbrev`/
  `instance`/`notation`) gets a **concise one-line `/-- … -/` docstring** — terse,
  API-style, NOT prose. Use Lean identifiers/notation in backticks. State *what*
  the declaration says or does, e.g. `` /-- `f ∗ g = g ∗ f`: convolution is
  commutative. -/ ``. Anonymous `instance :` and `notation` are auto-named by
  Lean, so doc-gen documents them too — give them docstrings as well.
- Anonymous `example`s carry no docstring (and don't appear in doc-gen output).
- Each file opens with a `/-! … -/` module docstring (1–3 short lines) **after the
  imports** — imports must come first or Lean errors `invalid 'import' command`.
- A docstring on a dioid-order (`≼`) statement must not be read in the reverse numeric
  order — the carrier files are where order-inversion mistakes hide (see the math section).
- **The `-/` trap:** any `-/` substring *inside* a docstring closes the comment
  early, even mid-word ("sub-/super", "left-/lower"). Write "sub- and super-".
  Audit with `grep -n -- '-/' file.lean | grep -vE -- '-/\s*$'`.
- Treat all linter warnings (unused variables, deprecations) as errors.

## File Audit Checklist

When asked to audit a Lean file, check both correctness and documentation-layer hygiene.
Lead with concrete findings, ordered by severity, and cite file/line references.

- Identify the layer first: `DeepWiki/<Topic>/` is source-neutral library code;
  `Sources/<slug>/` is the source catalog. Book numbers, §/page references, DOI/source
  provenance, and coverage status belong only in `Sources/`.
- For `DeepWiki/` files, scan module and declaration docstrings for source-catalog leakage:
  `Bronstein`, `§`, `Lemma 3.3.5`, `Definition ...`, `Exercise ...`, `remaining work`,
  `deferred`, `not yet`, or similar progress/source wording. Replace these with semantic
  API-style descriptions.
- For `Sources/` files, docstrings may cite the book/paper, but should be self-contained
  enough to explain what Lean declaration is being cataloged and how it maps to
  Mathlib/DeepWiki terminology.
- Check every named declaration has a concise one-line docstring; anonymous `example`s do
  not need one.
- Check module docstrings are current. Do not leave stale progress claims like "converse
  still open" once downstream files or catalog aliases formalize it.
- Mention section-level `variable` blocks in audits when they obscure the exported signature
  or when nearby files are using explicit declaration signatures.
- Verify with the affected target and, for catalog-facing changes, the relevant
  `Sources.<...>.Chapter...` target.

## Naming & style conventions

How declarations should be shaped (these reflect repeated authoring decisions,
not just defaults):

- **Calibrated generality.** Generalize a declaration off the concrete carrier
  when nothing pins it there — but to the *weakest **bundled** typeclass that
  fits*, not a long list of atomic ones. Prefer `[Semiring V]` /
  `[CompleteLinearOrder V]` over `[Mul V] [Add V] [Zero V] [Min V] [Top V] …`;
  add `[Sub V]` etc. only on the declarations whose shape needs it. Never
  over-strengthen: the carriers (`ℝ≥0`, `ℝ≥0∞`) are idempotent semirings with
  *truncated* `Sub`, **not** rings — `ℝ≥0∞` has no `Neg`, so `Ring`/`Group`
  bases don't even instantiate, and ring `-` would give the wrong `(t-T)₊`.
  Don't add generality nothing uses; a relation/typeclass parameter must earn
  its place by being instantiated more than once.

- **Name a declaration for what it *is*, not its consumer.** A set of times
  where `f t ⋈ x` is `levelSet`, not `pseudoInvSet` — even if today only the
  pseudo-inverse uses it. When a notion becomes standalone, give it its own
  file/name rather than leaving it coupled to a caller. Keep naming *families*
  uniform: Mathlib's `conclusion_of_hypothesis` order, and one consistent term
  for the same object across a related group (e.g. `apply` for `f t` across the
  four `*_of_*` inversion lemmas).

- **Inline theorem-only proposition wrappers.** Do not introduce
  `def FooClaim : Prop := P` when its only role is to be the type of
  `theorem foo : FooClaim`; state `theorem foo : P` directly. Keep a named
  `Prop` when it is part of the mathematical or public API: a reusable
  predicate, an independently meaningful specification/open interface or
  source-faithful claim, a subject of equivalence/transport/composition
  lemmas, or the common statement of a theorem family. Apply this
  semantically, not by raw reference count.

- **Prefer atomic library theorems; let catalogs assemble source items.** When a source
  theorem or example contains several independently meaningful claims, prove and name each
  claim separately in `DeepWiki/`. Do not add a conjunction, nested conjunction, or
  existential-packaging theorem solely to reproduce the source item's prose. In `Sources/`,
  catalog those atomic results with entries sharing the book-number prefix and descriptive
  suffixes (`ex_3_1_2_classification`, `ex_3_1_2_top_quotient`). Keep a single unsuffixed
  catalog entry when one library declaration already expresses the source item naturally;
  splitting is for independently reusable claims, not every connective inside a theorem.

- **The library is book-number-free; book numbers live ONLY in `Sources/`.**
  Neither a declaration NOR a module/file under `DeepWiki/<Topic>/` may be named
  after a book pointer — not `ex_3_25`/`thm_7_1`/`prop_7_2_if`/`def_9_2`/`eq_9_4`
  (decls), and not `Chapter2Examples`/`Chapter12Closed` (modules). Library modules
  are concept-named like the theory files (`ExpansionLaw`, `WeakBisimulationExample`,
  `TimedLightSwitch`, `CharacteristicFormulaExample`) with the module-docstring title
  matching; `Chapter<N>.lean` is the *catalog* (`Sources/`) file-naming, never the
  library's. Name library declarations *semantically* for
  what they state — including example/exercise content (a worked exercise is a
  theorem about concrete objects, so name it after those objects and the claim:
  `s325_weaklyBisimilar_t`, `e37_s_not_bisim_t`, `expansionLaw`, `lightDelay`).
  The book number appears exactly once, as the `alias`/`abbrev`/restatement in the
  `Sources/<slug>/Chapter*.lean` catalog (`ex_3_25 := …`), whose docstring carries
  the §/page. When formalizing an exercise, put the proof under a semantic name in
  the library and add the `ex_X_Y` catalog entry pointing to it — never the reverse.
  (Docstrings in the library likewise cite the math, not the book number; the
  catalog docstring is where "**Exercise 3.25**" belongs.)

- **Naming conventions** (codified; legacy names migrate gradually):
  - Predicates are `Is<Concept>` with the curve argument first
    (`IsMinimalServiceCurve beta S`); transport lemmas use dot notation on the
    predicate (`IsShaper.mono`, `IsGreedyShaper.isShaper`). No primed names.
  - Duality pairs are `Minimal`/`Maximal` — for arrival and service curves
    alike; `MinPlus`/`MaxPlus` are reserved for the dioid carriers.
  - The largest relation offering a property is `<concept>Rel`
    (`minimalServiceRel`, `maximalServiceRel`, `strictServiceRel`,
    `shaperRel`, `greedyShaperRel`), with the lemma family `mem_<rel>_iff`,
    `isServer_<rel>`, `is<Concept>_iff_subset` (predicate on the left),
    `is<Concept>_<rel>` (a relation offers its own property), `<rel>_mono`,
    `<rel>_closure`.
  - Relation-form residual wrappers: `is<Pred>_<curve>_of_<hyp>` when the
    chapter defines a named residual curve for the conclusion
    (`isStrictMinimalServiceCurve_drrResidual_of_isDrr`,
    `…_wrrResidualStaircase_of_isWrr`, `…_tdmaResidual_of_isTdma`);
    `is<Pred>_residualServer_of_<hyp>` when the conclusion curve is an
    unnamed expression (the GPS share, `residualCurve` applications).
  - Hypothesis binders: `hmono` monotone, `hnn` nonneg, `h0` null at origin,
    `hlc` left-continuous, `hsub` sub-additive, `hsup` super-additive,
    `hp` pair membership `S A D`, `hc` causal, `hSrv` server,
    `hjump` jump domination, `hcap` capacity domination,
    `hstrict` windowed strict service bound, `hws` start-anchored
    (weakly strict) service bound, `harr`
    arrival-curve, `hserv` service bound, `hcross` crossing, `hne` nonempty
    (crossing set) or the `≠` hypothesis of an `_of_ne` lemma. When two
    curves both need a property, tag the binder by the curve
    (`hαmono`/`hβmono`, `hAlc`/`hDlc`), keeping plain `hmono` where only
    one curve carries it; when a quantity is bounded on both sides, tag
    by side with `l`/`u` (`hDl`/`hDu` for the lower and upper service
    inequalities).
  - Carrier tags (target grammar; bare `E` is legacy and ambiguous):
    `NN` = `ℝ≥0∞` values on `ℝ≥0` domain, `ENN` = an `ℝ≥0∞` reading/lift,
    `EReal` = `EReal` values, `Ext` = `WithTop (WithBot ℝ)`; lowercase
    `_ereal`/`_ext` for theorem-variant suffixes. Cast helpers: `lift*` for
    exact embeddings (`Deviation.liftENN`), `to*` for truncating reads
    (`Deviation.toENN`, after Mathlib's lossy `EReal.toENNReal`).
  - Function-level vs pointwise lemma pairs follow Mathlib: the plain name
    states the function equality, `_apply` the pointwise one
    (`conv_coe_min` / `conv_coe_min_apply`) — not a primed variant.
  - Concrete curves live in the `RealCurves` catalog (all carrier variants
    of one curve side by side), with the base-value family `<curve>_zero_eq`;
    chapters state theorems about them but don't define them.

- **Bound convolutions through the intro/elim API**, not by hand-opening the
  split subtype `{p : D × D // p.1 + p.2 = t}`: `minConv_le_add` / `le_minConv`
  and the duals `add_le_maxConv` / `maxConv_le` (`DeepWiki/NetworkCalculus/FunctionDioids.lean`).
  Same for deconvolutions (`sub_le_minDeconv` / `minDeconv_le`,
  `maxDeconv_le_sub` / `le_maxDeconv`) and deviations (`vDevAt_le_vDev` /
  `vDev_le`, `hDevAt_le_hDev` / `hDev_le`, witness-elim `hDevAt_le`,
  `DeepWiki/NetworkCalculus/Deviations.lean`); `minConv_apply_zero` computes the origin value.
  Cross the `ℝ≥0∞`-vs-`EReal` reading of served-pair convolutions through the
  bridge iffs `coe_le_minConv_toENN_iff` / `minConv_toENN_le_coe_iff` /
  `coe_eq_minConv_toENN_iff` (`DeepWiki/NetworkCalculus/DeviationsBoundsServer.lean`), not a
  per-site `EReal.coe_ennreal_le_coe_ennreal_iff` + `coe_minConv_toENN`
  rewrite dance.

- **Every `def` ships its satellite lemmas, in the defining file.** A
  definition is findable only through its predictable API: intro rule, elim
  rule, closed-form/pointwise reading (`_apply`/`_coe`, `rfl`-provable,
  `@[simp]` when the gate tolerates it), origin value (`*_zero_eq`),
  monotonicity, and a transport through each standard cast it meets
  (`lift*`, `to*`, numeric `coe`) — transports named by dot notation on the
  predicate/helper (`IsSubadditive.liftENN`, `IsSubadditive.coe_real`) so a
  family enumerates under `grep "IsSubadditive\."`. A missing satellite gets
  re-derived inline at call sites (this is how cast noise accumulates); a
  reading lemma placed downstream of its definition is invisible upstream and
  gets re-proved verbatim (the `rateLatency_coe` lesson). Satellites live in
  the file that defines the object, not where its first consumer sits.

- **Refinement discipline (the executable engine).** Abstract math lives on
  Mathlib carriers (Layer 0), named for what it *states* — never in a retrofitted
  `*Correct`/`*Sound` file (those masquerading as engine correctness get renamed
  to their concept, e.g. `GcdCorrect`→`FilterProdMul`, `CanonicalRepCorrect`→
  `CanonicalFieldIdentity`, `SplitFactorCorrect`→`SplitFactorHelpers`). The
  `Engine/` engine's only theorems are **commuting squares through a
  denotation**: for a computable `f`, the *one* satellite `⟦f x⟧ = F ⟦x⟧` (RHS a
  Layer-0 notion; a `_sound`/`_complete` pair for option-valued deciders) lives in
  the file that *defines* `f` and is tagged `@[denote]` (see `Engine/Denote.lean`
  and [[leanproofs-symbolic-integration-reorg]]). A new algorithm ships its square
  in its own file — not a separate `*Correct` file; existing end-to-end soundness
  developments (`*Soundness` assemblies) stay separate, but single stray squares
  fold back to their def gradually.

- **`X` / `LawfulX` class pairs (Lean-core `BEq`/`LawfulBEq` idiom).** A computable
  interface splits into a **Prop-free** class of the computable operations
  (`native_decide`-friendly — no abstract structure, so its ops *reduce*) and a
  companion carrying the denotation homomorphism into the abstract carrier plus its
  laws. Name the companion **`Lawful<X>`** for a computable class `<X>`. The engine's
  `CField` / `CFieldSpec` (and `CDiffField` / `CDiffFieldSpec`) split *is* this idiom
  — the `*Spec` names are **grandfathered** (keep them; 1264+ refs), but **new** pairs
  use `X` / `LawfulX` (e.g. a new `CFoo` gets `LawfulCFoo`, not `CFooSpec`). The
  Prop-free half never gains a `Prop` field; the abstract carrier is mentioned only in
  the `Lawful` half. See [[leanproofs-symbolic-integration-reorg]].

- **Arrival curves: `*ArrivalBound` vs `*ArrivalCurve`.**
  `IsMaximalArrivalBound`/`IsMinimalArrivalBound` are the raw inequalities
  `A ≤ A ∗ α` / `A ⊼ α ≤ A`; the book's definitions (α ∈ ℱ↑) are the
  bundles `Is{Max,Min}imalArrivalCurve := Monotone α ∧ <bound>`. State
  theorems on the bound when monotonicity is unused; book restatements and
  monotonicity-consuming theorems (e.g. the `*_sInf_*` first-crossing
  bounds) take the bundle and pass `.2` down.

- **The first-crossing spelling is `crossingSet`/`firstCrossing`**
  (`DeepWiki/NetworkCalculus/ArrivalCurves.lean`, generic over the value order): state ℓmax-style
  hypotheses as `ℓmax ∈ crossingSet α β` and never re-spell
  `{x | 0 < x ∧ α x ≤ β x}` or its `⨅`/`sInf` inline.

- **Time-domain machinery is unbundled from `Curve`.** `IsBacklogged`,
  `start`, `backloggedAgeAt`, `maxBackloggedLength` (`DeepWiki/NetworkCalculus/ServersBacklog.lean`)
  — like `backlog`/`delay` and the deviations — are stated on plain
  `ℝ≥0 → ℝ≥0` functions with the properties they consume as hypotheses
  (`h0 : A 0 = D 0` only where the equality set must be inhabited;
  left-continuity only in `apply_start_eq`). `Curve` call sites pass
  `⇑A ⇑D` and discharge hypotheses via the wrappers `Curve.zero_eq` /
  `Curve.apply_start_eq`. Don't re-bundle new time-domain notions into
  `Curve`; right-continuous cumulative functions must remain stateable.

- **Definitions split from proofs; share one definition via base + abbrev.**
  Keep a definitions file (e.g. `RealCurves`) separate from its regularity/proof
  file (`RealCurvesRegularity`). When the same curve/notion lives over two carriers,
  define it *once* over a polymorphic base and specialize with `abbrev`s (the
  `delay` → `delayNN`/`delayENN` pattern), rather than duplicating bodies; bridge
  the variants with `*_coe` agreement lemmas where they are only propositionally
  (not defeq) equal.

- **A settled counterexample also refutes the general statement — state the
  `¬ ∀` theorem.** Ship the full ladder, each layer named: the witness lemmas
  (`witness_mem_<rel>`, `witness_not_mem_comp*`), the instance-level failing
  direction (`not_<rel>_le_<witness-tags>`), the strict inequality
  (`<rel>_lt_*` via `lt_of_le_not_ge`), and the refutation of the
  universally quantified converse (`not_forall_<rel>_le_comp`), whose
  quantified hypotheses mirror the forward theorem *verbatim* — so the pair
  reads "this direction is a theorem, the flipped direction is a
  non-theorem". Don't stop at the instance: the `¬ ∀` form is what makes
  the failure a citable general fact (`ServersConcatenationStrict` is the
  model).

## Workflow & CI

- **Commit or push only when asked.** Verify before claiming done: build the affected
  chapter, then `lake build`, and restate theorems as `example`s — don't trust that "it
  compiled" means "it says the right thing".
- **Large multi-session refactors get a `docs/<name>.md` plan.** For a migration/refactor
  too big for one pass (e.g. the fuel retirement, `docs/gcd-core-fuel-migration.md`), write a
  dependency-ordered phased plan under `docs/` — Wf/twin inventory, the pins keeping the old
  code alive, and the phase order (delete consumers before the ops they use). Keep it current
  as phases land; each phase is its own gate-green commit. Working autonomously through such a
  plan (writing the plan, taking sensible risks, committing per gate-green phase) is expected,
  not something to re-confirm each phase. Durable adjudications/lessons still go to memory; the
  plan doc holds the mechanical phase list.
- The repo is on macOS (`darwin`); doc-gen4 needs a clean native `MD4Lean` build
  (cross-platform `.lake` contamination once caused a link failure). Stale `" 2.lean"`
  duplicates from macOS file-sync/lock collisions are never imported — delete them if they
  appear untracked, and close the phantom editor tab that shows LSP errors on a deleted one.
- **CI** (`.github/workflows/ci.yml`): on push/PR to `main` runs `lake build` and
  `DOCGEN_SRC=file lake build DeepWiki:docs Sources:docs`; on pushes (not PRs) it publishes
  `.lake/build/doc` to GitHub Pages (https://sylee957.github.io/deepwiki/) via
  `upload-pages-artifact` + `deploy-pages`. doc-gen4 renders HTML for the DeepWiki + Sources
  libraries only (its long docInfo pass over Mathlib feeds cross-reference data, not
  published pages). CI uses `lake exe cache get` for Mathlib's prebuilt oleans so only our
  chapters recompile.
