# DeepWiki

An AI-generated wiki of _autoformalized_ mathematics. Each topic is a
self-contained set of chapters whose definitions, lemmas, and theorems are stated
and proved in **Lean 4 + Mathlib**. Every declaration carries a concise
docstring; the rendered API documentation is exactly what was proved.

**Live API docs:** https://sylee957.github.io/deepwiki/

## Topics

The library currently spans **Network Calculus** (the (min,plus) dioid algebra
and deterministic network calculus), **Reactive Systems** (CCS, bisimulation,
Hennessy–Milner logic, timed CCS), **Time Series** (Brockwell–Davis), **Symbolic
Integration** (the transcendental Risch algorithm, plus algebraic functions), and
**Relational Databases** (the relational model and functional dependencies), each
under `DeepWiki/<Topic>/`.

## Structure

A plain Lean library. The real `def`/`theorem`/`instance` declarations live in
`DeepWiki/<Topic>/*.lean` chapter files as ordinary top-level Lean, each with a
`/-- … -/` docstring and a `/-! … -/` module docstring per file; `DeepWiki.lean`
is the library root. Per-book, DOI-keyed catalogs under `Sources/` map each book
item to the library declaration that formalizes it. All declarations live in the
`DeepWiki` namespace.

## Build

Requires the Lean toolchain in `lean-toolchain` (`leanprover/lean4:v4.32.1`),
installed via [`elan`](https://github.com/leanprover/elan). The compatible stable
release tags for `mathlib` and `doc-gen4` are pinned to `v4.32.0`.

```bash
lake exe cache get   # download Mathlib's prebuilt oleans (recommended)
lake build           # build/typecheck the whole library
```

To build a single chapter: `lake build DeepWiki.<Topic>.<Chapter>`
(e.g. `DeepWiki.NetworkCalculus.Dioids`).

## Render API docs locally

```bash
DOCGEN_SRC=file lake build DeepWiki:docs Sources:docs   # doc-gen4 → .lake/build/doc/
python3 -m http.server 8000 --directory .lake/build/doc
```

Then open http://localhost:8000. Serve over HTTP (not `file://`) so the
cross-reference links resolve.

## Deployment

Pushes to `main` trigger a GitHub Actions workflow
([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) that builds the library
and deploys the rendered doc-gen4 HTML to GitHub Pages.

## Authors

Sangyub Lee and Claude (Anthropic).
