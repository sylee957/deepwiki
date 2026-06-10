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
`ServiceCurveStrict`, `ArrivalCurveShaper`, `ArrivalCurveShaperGreedy` — so
related chapters sort together alphabetically. When a chapter grows a distinct
sub-theory, split it into a suffixed sibling rather than growing the file.

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
  - Hypothesis binders: `hmono` monotone, `hnn` nonneg, `h0` null at origin,
    `hlc` left-continuous, `hsub` sub-additive, `hsup` super-additive,
    `hp` pair membership `S A D`, `hc` causal, `hSrv` server, `harr`
    arrival-curve, `hserv` service bound, `hcross` crossing, `hne` nonempty
    (crossing set). When two curves both need a property, tag the binder by
    the curve (`hαmono`/`hβmono`), keeping plain `hmono` where only one
    curve carries it.
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

- **The first-crossing spelling is `crossingSet`/`firstCrossing`**
  (`Book/ArrivalCurves.lean`, generic over the value order): state ℓmax-style
  hypotheses as `ℓmax ∈ crossingSet α β` and never re-spell
  `{x | 0 < x ∧ α x ≤ β x}` or its `⨅`/`sInf` inline.

- **Definitions split from proofs; share one definition via base + abbrev.**
  Keep a definitions file (e.g. `RealCurves`) separate from its regularity/proof
  file (`RealCurvesRegularity`). When the same curve/notion lives over two carriers,
  define it *once* over a polymorphic base and specialize with `abbrev`s (the
  `delay` → `delayNN`/`delayE` pattern), rather than duplicating bodies; bridge
  the variants with `*_coe` agreement lemmas where they are only propositionally
  (not defeq) equal.

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
- **CI is build-only (no deploy).** The GitHub Actions workflow
  (`.github/workflows/ci.yml`) is an integrity check on push/PR to `main`: it runs
  `lake build` and `DOCGEN_SRC=file lake build Book:docs`, but produces no artifact
  and does not deploy to Pages. CI uses `lake exe cache get` for Mathlib's prebuilt
  oleans so only `Book/*.lean` recompiles. If you later want to publish the
  doc-gen4 HTML, add a Pages upload/deploy step pointing at `.lake/build/doc`.
