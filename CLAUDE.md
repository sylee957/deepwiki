# CLAUDE.md

Guidance for working in this repository.

## What this project is

**DeepWiki** — an AI-generated wiki of autoformalized mathematics (lake package
`deepwiki`). The first entry is a Lean 4 + Mathlib formalization of the
**(min,plus) dioid algebra** (the algebra behind deterministic network calculus);
further topics are added as additional chapters.

The formalization is a **plain Lean library**: the real
`def`/`theorem`/`instance` declarations live in the `Book/*.lean` chapter files
as ordinary top-level Lean, each carrying a concise one-line `/-- … -/`
docstring, with a `/-! … -/` module docstring per file. `Book.lean` is the
aggregator that imports every chapter. Rendered docs are produced by **doc-gen4**
(standard Lean API documentation).

> **History:** this used to be a Verso "Manual"-genre book where declarations
> lived inside elaborated ` ```lean ` code blocks interleaved with prose, and the
> Verso book *was* the source of truth. Verso was removed (the per-block
> interpreted elaboration was ~70 ms/block, ~539 blocks) in favour of plain Lean
> + doc-gen4. The conversion was mechanical and verified code-identical to the
> Verso originals; the last Verso state is in git history. Do **not** reintroduce
> Verso, `#doc`, ` ```lean ` blocks, or `import VersoManual`. If `Main.lean`,
> `VersoParse.lean`, an `Introduction.lean`, or `"<Chapter> 2.lean"` duplicates
> reappear, they are stale — delete them.

## Toolchain & build

- Lean toolchain: `leanprover/lean4:v4.30.0` (see `lean-toolchain`). `elan`/`lake`
  are on PATH via `~/.zshrc`: prepend `export PATH="$HOME/.elan/bin:$PATH"` in any
  fresh `Bash` invocation (the shell is non-interactive and may not load it).
- Dependencies (pinned to `v4.30.0`, matching the toolchain): `mathlib`,
  `doc-gen4`. (Verso is gone.)
- `lakefile.toml` has one target: `Book` (lean_lib, root `Book.lean`);
  `defaultTargets = ["Book"]`.

Commands:
- Build one chapter: `lake build Book.<Chapter>` (e.g. `Book.Dioids`).
- Build everything: `lake build`. Must be warning-free and `sorry`-free.
- **Proof-result gate (agent loop): `scripts/check.sh [Book.<Chapter>]`.** Runs the
  full `lake build` and returns a single verdict — exit `0` = `GATE: PASS`, exit `1`
  = `GATE: FAIL`. Crucially it treats `warning:`/`error:`/`declaration uses 'sorry'`
  as failure *even when lake itself exits 0* (lake exits 0 on `sorry`), enforcing the
  warning-/sorry-free requirement. Pass a chapter target for faster mid-iteration
  feedback; run with no arg (`Book`) as the final gate. Timing on a warm filesystem
  cache: ~2.4s no-op (lake's manifest-parse + olean-stat floor over the ~1500-job
  dependency closure — intrinsic, not network/elan/reservoir), plus 0–3s when a
  chapter actually recompiles (the heaviest real-curve chapters elaborate in
  ~1–2s each). The first build after idle is colder (~5–7s). Don't expect below ~2.4s
  without bypassing lake.
- Render API docs to HTML (doc-gen4): `DOCGEN_SRC=file lake build Book:docs`.
  Output lands in `.lake/build/doc/` (gitignored). doc-gen expects a
  `references.bib` at the doc root — if rendering fails on a missing
  `.lake/build/doc/references.bib`, `touch` an empty one. If doc-gen "Replays"
  stale HTML instead of regenerating, remove its facet markers
  (`.lake/build/doc-data/Book--library.docs_built*`) and the `.lake/build/doc`
  tree, then rebuild.

## Chapter structure (`Book/`)

Each chapter is plain Lean: imports first, then a `/-! … -/` module docstring,
then declarations in `namespace DeepWiki`, each with a `/-- … -/` docstring.
Chapters `import` earlier chapters to form the dependency DAG; `Book.lean`
imports them all in dependency order — it is the live chapter list (do not
maintain a copy of it here).

All declarations live in `namespace DeepWiki` (sub-namespace `Deviation` for
the backlog/delay theory, whose short names would clash with the curve
catalog).

**Chapter naming:** base concept first, qualifiers appended as suffixes —
`ServiceCurveStrict`, `ArrivalCurvesShaper`, `ArrivalCurvesShaperGreedy` — so
related chapters sort together alphabetically. When a chapter grows a distinct
sub-theory, split it into a suffixed sibling rather than growing the file.

**Singular vs plural:** plural when the chapter is the theory of a class of
objects (`Dioids`, `Servers`, `RealCurves`, `ArrivalCurves`, `Deviations`,
`Closures`); singular when it names one operation, property, or
distinguished concept (`Deconvolution`, `Continuity`, `PseudoInverse`,
`ConvolutionMinimum`), including compounds where the concept is the
qualified head (`SubDioid`, `ConcaveDioid`). Whichever number a family head
gets, it is frozen verbatim across every sibling — the prefix is an
identifier, not prose (`ArrivalCurves*` throughout, never a mixed
`ArrivalCurve*`/`ArrivalCurves*` family). `ServiceCurve*` predates the rule
and stays singular: within-family uniformity is the binding part.

**Flat layout:** chapters stay flat in `Book/`, organized by the prefix
families above — no subdirectories. Revisit only when a second wiki topic
lands; then partition by topic (`Book/<Topic>/…`), not before (module
renames touch every import and doc-gen URL).

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
- Carriers (newtypes in `Book/ScalarDioids.lean`, sense + number-system names):
  `MinPlus` over `WithTop ℝ` (dioid, `R∪{+∞}`); `MinPlusNN` over `ℝ≥0∞` (complete);
  `MinPlusExt` over `WithTop (WithBot ℝ)` (complete, `R∪{±∞}`); plus the (max,plus)
  duals `MaxPlusNN` over `WithBot ℝ≥0∞` and `MaxPlusExt` over `WithBot (WithTop ℝ)`.
- The convolution `conv` (notation `∗`) is generic over `CompleteDioid`; the function
  dioid (`Book/FunctionDioids.lean`) and the function classes `FPlus`/`FNondecr` are
  subtypes built by `IsSubCompleteDioid.toCompleteDioid` (the sub-complete-dioid
  builder in `Book/CompleteDioids.lean`).

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
   cast (`Book/MinPlusExtTopology.lean`, and the max dual). The cast agrees with the dioid
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
- The math/order conventions still matter for *accuracy*: a docstring on a
  dioid-order (`≼`) statement must not be read in the reverse numeric order. The
  carrier files are where order-inversion mistakes hide — see the math section.
- **The `-/` trap:** any `-/` substring *inside* a docstring closes the comment
  early, even mid-word ("sub-/super", "left-/lower"). Write "sub- and super-".
  Audit with `grep -n -- '-/' file.lean | grep -vE -- '-/\s*$'`.
- Treat all linter warnings (unused variables, deprecations) as errors; the build
  must be warning-free and `sorry`-free.

## Style preferences

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
    `hjump` jump domination, `hcap` capacity domination, `harr`
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
  and the duals `add_le_maxConv` / `maxConv_le` (`Book/FunctionDioids.lean`).
  Same for deconvolutions (`sub_le_minDeconv` / `minDeconv_le`,
  `maxDeconv_le_sub` / `le_maxDeconv`) and deviations (`vDevAt_le_vDev` /
  `vDev_le`, `hDevAt_le_hDev` / `hDev_le`, witness-elim `hDevAt_le`,
  `Book/Deviations.lean`); `minConv_apply_zero` computes the origin value.
  Cross the `ℝ≥0∞`-vs-`EReal` reading of served-pair convolutions through the
  bridge iffs `coe_le_minConv_toENN_iff` / `minConv_toENN_le_coe_iff` /
  `coe_eq_minConv_toENN_iff` (`Book/DeviationsBoundsServer.lean`), not a
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
  (`Book/ArrivalCurves.lean`, generic over the value order): state ℓmax-style
  hypotheses as `ℓmax ∈ crossingSet α β` and never re-spell
  `{x | 0 < x ∧ α x ≤ β x}` or its `⨅`/`sInf` inline.

- **Time-domain machinery is unbundled from `Curve`.** `IsBacklogged`,
  `start`, `backloggedAgeAt`, `maxBackloggedLength` (`Book/ServersBacklog.lean`)
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

## Autoformalizing from source PDFs (`references/`)

- `references/` is a **gitignored** local dump of the source books/papers being
  formalized. Claude reads PDFs there directly with the Read tool (use the
  `pages` parameter; ≤20 pages per request).
- **Read statements by OCR, never by text extraction.** Transcribe
  theorem/definition statements only from *rendered pages*: the Read tool's PDF
  rendering, or — if it errors about `pdftoppm` (stale extension PATH; poppler
  is installed) — render manually with
  `pdftoppm -png -r 110 -f <p> -l <p> <pdf> /tmp/page` and Read the PNGs.
  Raw text extraction (`pdftotext`, content-stream scraping) garbles math
  glyphs and statement *shape* (it has caused a misread quantifier structure);
  use `pdftotext -layout` only to grep for which page holds a passage.
- **The autoformalization workflow:** when the user posts a capture/screenshot of
  a book passage (or points at pages of a PDF in `references/`), formalize that
  passage in the appropriate `Book/*.lean` chapter. Before writing anything new,
  search the existing library for the lemmas/definitions it should build on —
  reuse and extend rather than redefine; new statements go in `namespace DeepWiki`
  following the chapter DAG, docstring conventions, and style preferences above.
  Mind the order inversion (numeric vs dioid order) when transcribing inequalities.
  Finish with `scripts/check.sh` and `example`-restatements of the new theorems
  against the book's wording.

## Workflow conventions

- Verify before claiming done: build the affected chapter, then `lake build`, and for
  theorems re-state each with its expected type (an `example`) to confirm signatures
  match the math — don't trust that "it compiled" means "it says the right thing".
- Commit or push only when asked.
- The repo is on macOS (`darwin`); `nm` shows Mach-O symbols. doc-gen4 needs a clean
  native `MD4Lean` build (cross-platform `.lake` contamination caused a link failure
  once).
- **Stale `"<File> 2.lean"` duplicates:** macOS file-sync/lock collisions can leave
  ` 2.lean` copies of chapters (stale Verso versions). They are never imported; if
  they appear untracked, delete them. The editor may keep a stale tab open on a
  deleted one and show phantom LSP errors — close the tab.
- **CI builds and deploys to GitHub Pages.** The GitHub Actions workflow
  (`.github/workflows/ci.yml`) runs `lake build` and
  `DOCGEN_SRC=file lake build Book:docs` on push/PR to `main`; on pushes (not
  PRs) it then publishes `.lake/build/doc` to Pages
  (https://sylee957.github.io/deepwiki/) via `upload-pages-artifact` +
  `deploy-pages`. The artifact is small: doc-gen4 renders HTML for the Book
  library only — its long docInfo pass over Mathlib feeds cross-reference data,
  not published pages. CI uses `lake exe cache get` for Mathlib's prebuilt
  oleans so only `Book/*.lean` recompiles.
