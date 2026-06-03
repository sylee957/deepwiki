# CLAUDE.md

Guidance for working in this repository.

## What this project is

**The Autoformalization Wiki** — an AI-generated wiki of autoformalized
mathematics, authored as a **Verso "Manual"-genre book** (lake package
`verified-wiki`). The first entry is a Lean 4 + Mathlib formalization of the
**(min,plus) dioid algebra** (the algebra behind deterministic network calculus);
further topics are added as additional chapters/articles.

The defining architectural decision: **the Verso book is the single source of
truth.** The real `def`/`theorem`/`instance` declarations live *inside* the
`Book/*.lean` chapter files, in elaborated ` ```lean ` code blocks interleaved
with prose. There is no separate library — building the book *is* building the
formalization. (An older `Leanproofs/MinPlus/` library was inlined into the book
and deleted; it is recoverable from git history at commit `4813a03~1` if ever
needed. Do not resurrect it — if those files reappear untracked, they are stale.)

## Toolchain & build

- Lean toolchain: `leanprover/lean4:v4.30.0` (see `lean-toolchain`). `elan`/`lake`
  are on PATH via `~/.zshrc`: prepend `export PATH="$HOME/.elan/bin:$PATH"` in any
  fresh `Bash` invocation (the shell is non-interactive and may not load it).
- Dependencies (all pinned to `v4.30.0`, matching the toolchain): `mathlib`,
  `doc-gen4`, `verso`.
- `lakefile.toml` targets: `Book` (lean_lib, root `Book.lean`) and `generate-book`
  (lean_exe, root `Main.lean`). `defaultTargets = ["Book", "generate-book"]`.

Commands:
- Build one chapter: `lake build Book.<Chapter>` (e.g. `Book.Dioids`).
- Build everything: `lake build`.
- Render the book to HTML: **`./render.sh`** (or `./render.sh --watch` to
  re-render on changes to `Book/`, `Book.lean`, `Main.lean`). Writes
  `_out/html-multi/`; `_out/` is gitignored. It renders to a staging dir
  (`lake exe generate-book --output _out/.staging`) and then **atomically
  swaps** the result into `_out/html-multi` with `mv` — so a running
  `python3 -m http.server` keeps serving and picks up the new files on its
  next request; nothing is killed. It also sweeps any stray `html-multi N`
  from past bad runs and fails loudly if the staged render lacks
  `index.html`.
- **Do not** run the raw `rm -rf _out && lake exe generate-book`: the
  renderer writes *alongside* any locked output (an `http.server`, or a
  shell whose cwd is inside `_out/html-multi`, pins it), producing a
  duplicate `html-multi 2/` — and `index.html` ends up inside *that*, so
  the main dir looks broken. Rendering to a separate staging dir avoids
  the lock entirely; that's the whole point of `render.sh`.
- Serve for viewing (Verso needs HTTP, not `file://`, for code hovers):
  `cd _out/html-multi && python3 -m http.server 8000`. With `render.sh`'s
  atomic swap you can leave this running across renders.

## Chapter structure (`Book/`)

Chapters are `import`ed and `{include 1 ...}`d in dependency order from `Book.lean`;
each chapter `import`s the previous one so the global ` ```lean `-block elaboration
order resolves. Order: `Introduction`, `Signatures`, `Dioids`, `Order`,
`CompleteDioids`, `ScalarDioids`, `DioidFunctions`, `FunctionDioids`,
`Subadditivity`, `SubadditiveClosure`, `LeftContinuity`,
`PiecewiseContinuous`, `ConvolutionMinimum`, `Servers`, `RealConvolution`,
`Shapers` (the live list is `Book.lean`).

All declarations live in `namespace VerifiedWiki`.

## The mathematics (orientation — get this right or proofs invert)

- A **dioid** is `IdemCommSemiring`; the dioid sum `⊕ = +` is the lattice join
  `⊔`/`⨆`, the product `⊗ = *`, zero `𝟘 = 0`, unit `𝟙 = 1`, canonical order `≼ = ≤`.
- `CompleteDioid` adds a `CompleteLattice` + lower semi-continuity
  `mul_sSup : a * sSup s = ⨆ b ∈ s, a * b`.
- **Carriers are order-duals.** For (min,plus), the dioid order is the *reverse* of
  the numeric order (so `⊕ = min`, `𝟘 = +∞ = ⊥`). The carrier is a **newtype**
  `MinPlus.D M` wrapping `M`, NOT a transparent `Mᵒᵈ` synonym — see gotcha below.
  A value `v : RbarMin` has underlying numeric value `v.toDual`.
- The **natural (numeric) order is the reverse of the dioid order.** "Non-negative",
  "non-decreasing", "sub-additive `f(s+t) ≤ f(s)+f(t)`" are *natural*-order notions,
  stated on `.toDual` values with numeric `+`. The *dioid* order (`≤` on the
  newtype) is what isotony / Kleene-star / convolution-as-product use.
- Carriers: `Rmin = (WithTop ℝ)` dual (dioid, `R∪{+∞}`); `RplusMin = ℝ≥0∞` dual
  (complete dioid); `RbarMin = WithTop (WithBot ℝ)` dual (complete dioid, `R∪{±∞}`).
- The convolution `conv` (notation `∗`) is generic over `CompleteDioid`; the
  function dioid `FunDioid` and the function classes `FPlus`/`FNondecr` are newtypes
  / subtypes built by `MinPlus.SubCompleteDioid`.

## Hard-won gotchas (read before editing)

1. **Newtype, not `OrderDual`.** `Mᵒᵈ` is a transparent type synonym, so it inherits
   *all* of `M`'s instances — including a stray `Mul` from carriers like `ℝ≥0∞` /
   `WithTop (WithBot ℝ)` that have native numeric multiplication. That stray `*` is
   NOT the dioid product and silently wins instance resolution. The fix throughout is
   to wrap carriers in a one-field **`structure`** (`MinPlus.D`, `FunDioid`, ...) that
   inherits nothing, transport the lattice from `Mᵒᵈ` via `Equiv.completeLattice`, and
   attach the dioid algebra explicitly. Same for the function space (`Pi.commSemiring`
   has the wrong, pointwise `*`).

2. **`R̄min` needs `WithTop (WithBot ℝ)`, NOT `EReal`.** They are defeq types but have
   *different* addition: the book's convention is `(+∞)+(−∞) = +∞` (so `𝟘 = +∞` stays
   absorbing), which is exactly `WithTop`'s top-absorbing addition. `EReal` uses
   `(+∞)+(−∞) = −∞`, which breaks `mul_zero` — it isn't even a dioid under min-plus.

3. **`nsmul`/`natCast` defaults don't reduce** through the `min`-on-the-dual addition.
   The builder supplies them in closed form (idempotent: `n • a = a` for `n ≥ 1`)
   rather than via `nsmulRec`/`Nat.unaryCast`.

## Verso authoring rules (the renderer is picky)

- Section numbering is automatic — do NOT add `number := false` metadata blocks
  (they were all removed deliberately).
- Prose math is **LaTeX via KaTeX**: inline `` $`...` `` and display `` $$`...` ``
  — a `$`, then a backtick, the LaTeX, a closing backtick, and NO trailing `$`
  (the backtick closes the math). A trailing `$` renders as literal text.
- **Inline math must stay on ONE physical line.** Verso's inline-math parser stops at
  a newline; a `` $`...` `` split across a line break renders as raw LaTeX. Put long
  formulas on their own line (prose lines have no length limit).
- **Math does NOT render in headings** — keep headings plain text / inline `` `code` ``.
- Lean lines inside ` ```lean ` blocks must be **≤ 60 columns** (a Verso linter; treat
  as an error). Prose lines are unconstrained.
- Markup is `_italic_` and `*bold*` — never Markdown `**double**`. Bare `{`/`[` in
  prose are Verso directive/link syntax; keep them inside backtick-math or escape.
- Lean identifiers naming real declarations stay as inline `` `code` ``; use math only
  for genuine notation. The document is **self-contained**: no references to external
  source texts/authors or external numbering (e.g. "Definition 2.5", "§2.1").
- Each declaration is introduced by an italic label line — `*Definition:*`, `*Theorem:*`,
  or `*Example:*` — immediately before its ` ```lean ` block. The label carries a **brief
  inline-LaTeX visual of the statement** (`` $`...` ``), not a prose paraphrase, whenever
  one reads naturally — e.g. `` *Theorem:* $`f \ast g = g \ast f` ``. Fall back to a short
  prose label only when the statement has no clean formula (a predicate like "is
  piecewise continuous"). The label states *what* is proved; surrounding prose explains
  *why*/*how*.
- **One declaration per labelled block** — present theorems one at a time, interleaved
  with their LaTeX, rather than bundling several in a single ` ```lean ` block under one
  label. A two-sided law (`δ₀ ∗ f = f` *and* `f ∗ δ₀ = f`) becomes two labels/blocks, not
  one `X and Y` label. Exceptions: a long `instance`/`def` whose fields are the theorems,
  and a `section`/`variable`/`end` whose helper lemmas may each get their own block within
  the section (Verso elaborates all blocks of a chapter in one continuous Lean context, so
  `variable`/`open` persist across the prose between blocks).
- Treat ALL linter warnings (line-length, markup-emph, multi-line-math) as errors;
  the build must be warning-free and `sorry`-free.

## Workflow conventions

- Verify before claiming done: build the affected chapter, then `lake build`, and for
  theorems re-state each with its expected type (an `example`) to confirm signatures
  match the math — don't trust that "it compiled" means "it says the right thing".
- Work happens on a feature branch (currently `minplus-chapter2`), not `main`.
- The repo is on macOS (`darwin`); `nm` shows Mach-O symbols. doc-gen4 needs
  `DOCGEN_SRC=file lake build Book:docs` (no git remote → its GitHub source-link facet
  fails otherwise), and a clean native `MD4Lean` build (cross-platform `.lake`
  contamination caused a link failure once).
