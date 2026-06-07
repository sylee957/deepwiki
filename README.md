# DeepWiki

An AI-generated wiki of _autoformalized_ mathematics. Each topic is a
self-contained article whose definitions, lemmas, and propositions are stated
and proved in **Lean 4 + Mathlib**. Every declaration carries a concise
docstring; the rendered API documentation is exactly what was proved.

**Live site:** https://sylee957.github.io/deepwiki/

The first entry is the algebra of **(min,plus) dioids**, the theory behind
deterministic network calculus: from the abstract dioid through scalar carriers,
the function dioid, convolution, sub-additive closures, service curves, and the
classical network-calculus curves (delays, rates, rate-latencies, token-buckets,
staircases).

## Structure

The formalization is a plain Lean library. The real `def`/`theorem`/`instance`
declarations live in the `Book/*.lean` chapter files as ordinary top-level Lean,
each with a `/-- … -/` docstring and a `/-! … -/` module docstring per file.
`Book.lean` imports every chapter. All declarations live in the `DeepWiki`
namespace.

## Build

Requires the Lean toolchain in `lean-toolchain` (`leanprover/lean4:v4.30.0`),
installed via [`elan`](https://github.com/leanprover/elan). Dependencies
(`mathlib`, `doc-gen4`) are pinned to the same version.

```bash
lake exe cache get   # download Mathlib's prebuilt oleans (recommended)
lake build           # build/typecheck the whole library
```

To build a single chapter: `lake build Book.<Chapter>` (e.g. `Book.Dioids`).

## Render API docs locally

```bash
DOCGEN_SRC=file lake build Book:docs    # doc-gen4 → .lake/build/doc/
python3 -m http.server 8000 --directory .lake/build/doc
```

Then open http://localhost:8000. Serve over HTTP (not `file://`) so the
cross-reference links resolve.

## Deployment

Pushes to `main` trigger a GitHub Actions workflow
([`.github/workflows/deploy.yml`](.github/workflows/deploy.yml)) that builds the
book and deploys the rendered HTML to GitHub Pages.

## Authors

Sangyub Lee and Claude (Anthropic).
