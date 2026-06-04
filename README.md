# DeepWiki

An AI-generated wiki of _autoformalized_ mathematics. Each topic is a
self-contained article whose definitions, lemmas, and propositions are stated
and proved in **Lean 4 + Mathlib**, with the narrative and the machine-checked
Lean declarations interleaved. The rendered statements are exactly what was
proved — the document compiles as part of building it.

**Live site:** https://sylee957.github.io/deepwiki/

The first entry is the algebra of **(min,plus) dioids**, the theory behind
deterministic network calculus: from the abstract dioid through scalar carriers,
the function dioid, convolution, sub-additive closures, service curves, and the
classical network-calculus curves (delays, rates, rate-latencies, token-buckets,
staircases).

## Source of truth

The Verso book **is** the formalization. The real `def`/`theorem`/`instance`
declarations live inside the `Book/*.lean` chapter files, in elaborated
` ```lean ` code blocks interleaved with prose. There is no separate library —
building the book is building the formalization. All declarations live in the
`DeepWiki` namespace.

## Build

Requires the Lean toolchain in `lean-toolchain` (`leanprover/lean4:v4.30.0`),
installed via [`elan`](https://github.com/leanprover/elan). Dependencies
(`mathlib`, `doc-gen4`, `verso`) are pinned to the same version.

```bash
lake exe cache get   # download Mathlib's prebuilt oleans (recommended)
lake build           # build/typecheck the whole book
```

To build a single chapter: `lake build Book.<Chapter>` (e.g. `Book.Dioids`).

## Render and view locally

```bash
lake exe generate-book --output _out/.staging
rm -rf _out/html-multi && mv _out/.staging/html-multi _out/html-multi
python3 -m http.server 8000 --directory _out/html-multi
```

Then open http://localhost:8000. Verso needs HTTP (not `file://`) for the
code-hover tooltips.

## Deployment

Pushes to `main` trigger a GitHub Actions workflow
([`.github/workflows/deploy.yml`](.github/workflows/deploy.yml)) that builds the
book and deploys the rendered HTML to GitHub Pages.

## Authors

Sangyub Lee and Claude (Anthropic).
