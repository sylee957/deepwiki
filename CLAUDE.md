# CLAUDE.md

Guidance for working in this repository.

## What this project is

**DeepWiki** — an AI-generated wiki of autoformalized mathematics (lake package
`deepwiki`). The first topic is a Lean 4 + Mathlib formalization of the **(min,plus)
dioid algebra** and **deterministic network calculus**; further topics are added as
sibling chapter sets.

It is a **plain Lean library**: real `def`/`theorem`/`instance` declarations live in
`DeepWiki/NetworkCalculus/*.lean` chapter files as ordinary top-level Lean, each with a
concise one-line `/-- … -/` docstring and a `/-! … -/` module docstring per file.
`DeepWiki/NetworkCalculus.lean` is the topic aggregator (imports every chapter in
dependency order); `DeepWiki.lean` is the library root. Rendered docs come from
**doc-gen4** (standard Lean API documentation).

**Two-layer architecture** (one lake package, two libs):
- **Topic library** `DeepWiki/NetworkCalculus/` — the book-number-free general theory
  (the chapter files).
- **Source catalogs** `Sources/<slug>/` — per-book, DOI-keyed. One `alias`/`abbrev` per
  book item, named by its book number (`Dnc.prop_10_1`, `Dnc.def_2_7`), linking to the
  library, with §/page in the docstring and the DOI in `Sources/<slug>/Source.lean`. The
  folder is named by the **sanitized DOI** (`Sources/Doi_10_1002_9781119440284/` — `/`
  and `.` → `_`, `Doi_` prefix because Lean module names can't start with a digit); the
  declaration namespace stays a short slug (`DeepWiki.Dnc`). Book numbers live **only** in
  the catalog — the library stays number-free. A second topic gets `DeepWiki/<Topic>/` over
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
    adjudications, reusable Lean lessons, project context). All four topic catalogs use this block
    format; keep new ones consistent with it.
- **Per-paper source catalogs.** A result the library takes from (or a book *defers to*) an
  individual **paper** gets its **own** `Sources/Doi_<sanitized-doi>/` catalog — a
  `Source.lean` (paper DOI + title + authors, short author-slug namespace, e.g.
  `DeepWiki.Llw`) plus catalog files pointing at the library theorems derived from it. Add
  this paper pointer **even when the book already references the paper** ("double
  reference"): the paper catalog is what lets a reader go straight to the *individual paper*
  (DOI in hand) rather than only the book. Collected reference papers live (gitignored) in
  `references/`, named freely; their DOI is recorded in the paper's `Source.lean`. Same
  sanitized-DOI folder rule as books (`Sources/Doi_10_7146_brics_v2i2_19504/`).

**Do not reintroduce Verso.** This was once a Verso "Manual" book (declarations inside
elaborated ` ```lean ` blocks); Verso was removed in favour of plain Lean + doc-gen4. No
`import VersoManual`, `#doc`, or ` ```lean ` blocks. If `Main.lean`, `VersoParse.lean`, an
`Introduction.lean`, or `"<Chapter> 2.lean"` duplicates reappear, they are stale — delete
them.

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
5. **Restate** each new theorem as an anonymous `example` with its expected type against
   the book's wording — "it compiled" ≠ "it says the right thing".
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
- Build one chapter: `lake build DeepWiki.NetworkCalculus.<Chapter>`. Everything: `lake build`.
- **Gate: `scripts/check.sh [DeepWiki.NetworkCalculus.<Chapter>]`** — runs the full
  `lake build`, exit `0` = `GATE: PASS`, `1` = `GATE: FAIL`. Treats
  `warning:`/`error:`/`declaration uses 'sorry'` as failure *even when lake itself exits 0*
  (lake exits 0 on `sorry`), enforcing the warning-/sorry-free requirement. Pass a chapter
  target for fast mid-iteration feedback; run bare (all default targets) as the final gate.
  Floor ~2.4s no-op (lake's manifest/olean-stat over the ~1500-job closure), +0–3s per
  recompiled chapter, ~5–7s cold.
- Render docs: `DOCGEN_SRC=file lake build DeepWiki:docs Sources:docs` → `.lake/build/doc/`
  (gitignored). Needs a `references.bib` at the doc root (`touch` an empty one if rendering
  fails on it missing). If doc-gen "Replays" stale HTML, remove its facet markers
  (`.lake/build/doc-data/DeepWiki--library.docs_built*`) and the `.lake/build/doc` tree,
  then rebuild.

## Navigating with `scripts/wiki`

A local graph-RAG CLI over the compiled library (`lake exe wiki`; sources in
`tools/WikiRAG/`, own `README.md`). Extracts the `DeepWiki`+`Sources` environment into
`.wiki/graph.db` (gitignored): ≈3,150 decl nodes, the *exact* intra-library `uses` edges
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

## Chapter structure & naming (`DeepWiki/NetworkCalculus/`)

Each chapter: imports first, then a `/-! … -/` module docstring, then declarations in
`namespace DeepWiki` (sub-namespace `Deviation` for the backlog/delay theory, whose short
names would clash with the curve catalog). Chapters `import` earlier chapters to form the
dependency DAG; `DeepWiki/NetworkCalculus.lean` is the live ordered chapter list (don't
duplicate it here). **Flat layout** — no subdirectories; a second topic gets its own sibling
`DeepWiki/<Topic>/` library (module renames touch every import and doc-gen URL, so this is
done once per topic, not per chapter).

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
