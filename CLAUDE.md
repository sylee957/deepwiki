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
imports them all in order: `Signatures`, `Dioids`, `Order`, `CompleteDioids`,
`ScalarDioids`, `DioidFunctions`, `FunctionDioids`, `Additivity`, `Closures`,
`Limits`, `Continuity`, `RealFunctionClasses`, `ConvolutionMinimum`, `Servers`,
`RealConvolution`, `Shapers` (the live list is `Book.lean`).

All declarations live in `namespace DeepWiki`.

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
- **Publishing is currently BROKEN and needs repointing.** The GitHub Actions
  workflow (`.github/workflows/deploy.yml`) still runs `lake exe generate-book` and
  deploys `_out/html-multi` — both Verso artifacts that no longer exist. It must be
  rewritten to render doc-gen4 (`DOCGEN_SRC=file lake build Book:docs`) and deploy
  `.lake/build/doc` before the next push to `main`. CI uses `lake exe cache get` for
  Mathlib's prebuilt oleans so only `Book/*.lean` recompiles.
