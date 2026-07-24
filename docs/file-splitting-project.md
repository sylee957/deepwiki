# Project: split oversized SymbolicIntegration files into concept subdirectories

**Status:** in progress · **Owner:** Codex-executable · **Repo:** `deepwiki` (Lean 4, v4.32.1)

Self-contained; assumes no conversation context. Read top to bottom before editing.

## The problem & the precedent

A handful of files carry several sub-theories at once and are too large to navigate. Split each into a
**concept subdirectory** with an aggregator, following the existing `SymbolicIntegration/` layout
precedent (`Compute/`, `Computable/{RischDE,Hyperexp,CoupledDE,Tower,Algebraic}/`). Per CLAUDE.md this is
done as **`git mv`-only commits with zero declaration changes** (imports + aggregators only) — never mix
a split with content edits.

## Targets (largest first)

| File | Lines | Likely split axis (confirm from the `/-! ### … -/` section headers) |
|---|---|---|
| `GroebnerBasis.lean` | 4245 | Buchberger / S-poly / reduction / correctness — one concept per section |
| `HermiteCorrectness.lean` | 3032 | reduction / valuation / correctness |
| `LaurentCoefficients.lean` | 1981 | coefficient defs / identities |
| `Computable/OneShotAssembly.lean` | 1957 | per-stage assembly |
| `LiouvilleLog.lean` | 1632 | log-extension pieces |
| `Computable/LrtSoundness.lean` | 1567 | normal / reduced / genuine-data |
| `SubresultantCorrectness.lean` | 1402 | PRS / subresultant identities |
| `Computable/NormalPartSoundness.lean` | 1111 | normal-part stages |

Do the top 2–3 first; re-measure before continuing
(`find DeepWiki/SymbolicIntegration -name '*.lean' -exec wc -l {} + | sort -rn | head`).

## The loop (per file → subdirectory)

Prepend `export PATH="$HOME/.elan/bin:$PATH"` to every shell call.

1. **Find the split axis:** `grep -nE "^/-! #{2,3} " <file>` — the `### …` section headers are the natural
   concept boundaries. Group declarations into 2–5 concepts. Respect the internal dependency order
   (a concept may only depend on earlier ones).
2. **Create the subdirectory** `<Foo>/` next to `<Foo>.lean` and, **for each concept**, `git mv` the
   relevant declaration block into a new leaf `<Foo>/<Concept>.lean`. Practically: create the leaf files
   with `import`s (each imports the earlier leaves it depends on + the same external imports the original
   had), move the declaration blocks verbatim, and delete the moved blocks from the original.
   **Zero declaration edits** — only imports, `namespace`, and the module `/-! … -/` docstring per leaf.
   Leaf names encode the concept (concept-named, not book-numbered); kind suffixes `Sound`/`Spec`/`Bench`
   where they apply (CLAUDE.md placement grammar).
3. **Make `<Foo>.lean` the aggregator**: it now only `import`s the leaves (`import ….<Foo>.<Concept>` for
   each), preserving the original module name so **no downstream import changes** are needed.
4. **Gate:** `scripts/check.sh <Foo>` then, before committing, a full `scripts/check.sh` (splits touch the
   build graph broadly). Confirm `GATE: PASS`.
5. **Commit, git-mv-only:** `refactor(split): <Foo> into concept subdirectory`, body noting "imports +
   aggregator only, zero declaration changes", ending with
   `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`. One file's split per commit.

## Guardrails (load-bearing)

- **Zero declaration changes** in a split commit — if you change a proof, that is a *different* commit.
  Verify: `git show --stat` should show moves; `git diff` of declaration bodies should be empty.
- Preserve the aggregator module name so all existing `import`s keep working (no downstream churn).
- Leaf modules are **concept-named** (CLAUDE.md: no book numbers in `DeepWiki/` module names); the leaf
  module docstring title matches the concept.
- Respect the dependency DAG: leaves import earlier leaves; no cycles. If a concept truly interleaves
  with another (mutual dependency), keep them in one leaf rather than forcing a split.
- doc-gen4 URLs change when a module path changes; that is expected and fine (CI rebuilds docs).
- No change to executable/`native_decide` code; warnings are errors; commit per gate-green split.
- If a file's declarations are genuinely one tightly-coupled theory (no clean section boundaries), **do
  not split it** — note that in the worklist and move on.

## Sequencing vs. the other projects

Run **after** (or independently of) `docs/hypothesis-bundling-project.md` and
`docs/transfer-rewrite-project.md`, but never in the same commit — content passes (bundling, transfer
rewrite) and pure `git mv` splits must stay separate so each split commit is verifiably move-only.
