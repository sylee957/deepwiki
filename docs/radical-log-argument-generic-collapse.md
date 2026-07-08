# Collapse the concrete `RadicalLogArgument` into the generic `RadicalLogArgGeneric`

**Goal (objective 2 — unify parallel abstractions).** The simple-radical log-argument solver exists
twice: a concrete `QFunNZG ℚ` copy (`Computable/Algebraic/RadicalLogArgument.lean`) and a `β`-generic
copy (`Computable/Algebraic/RadicalLogArgGeneric.lean`). Drive them to one canonical (generic) path,
keeping the concrete *names* as thin `def foo … := fooG (β := ℚ) …` wrappers so consumers and the DOI
catalogs stay untouched.

## Feasibility — VERIFIED by spike (2026-07-08)

Despite different-named helpers (`qxOfNum`/`qOfNumG`, `CField.one`/`1`), the concrete and generic defs are
**definitionally equal** at `β = ℚ`. A temp `example`-spike in `RadicalLogArgGeneric` (which transitively
sees both) compiled `rfl`:

```
example (k : ℕ) : qMonomialG (β := ℚ) k = qxMonomial k := rfl
example (d : ℕ) : radLogBasisG (β := ℚ) d = radLogBasis d := rfl
```

So each concrete def can become a `rfl`-wrapper over its generic twin — no equality lemmas needed. This is
the same base+abbrev unification already landed for `AlgIntegralResult`/`AlgIntegralResultG`
(commit `fe548ef1`; see [[leanproofs-symbolic-integration-reorg]]).

## The obstacle — a transitive import cycle

Currently the **generic is downstream of the concrete**: `RadicalLogArgGeneric` transitively imports
`RadicalLogArgument` via `RadicalLogIntegral` / `RadicalOverTower`. So the concrete cannot simply
`import RadicalLogArgGeneric` and wrap — that closes a cycle. The generic file itself uses **no** concrete
name (all `qx*`/`ratRref` mentions are docstring "generic analogue of …" notes), so the two files are
code-independent; the cycle is purely through the shared downstream deps.

## Pair inventory (concrete → generic)

Algorithmic core (the defeq wrappers to build):
- `ratRref` → `gaussElimG`
- `ratKernelVector` → `kernelVectorG`
- `qxOfNum` → `qOfNumG`, `qxMonomial` → `qMonomialG`, `qxNum` → `qNumG`, `qxDen` → `qDenG`
- `ratPadTo` → (generic pad inside `radLogMatrixG`; extract if needed)
- `radLogResidual` → `radLogResidualG`
- `radLogBasis` → `radLogBasisG`
- `radLogMatrix` → `radLogMatrixG`
- `radLogArgSolve` → `radLogArgSolveG`

Stays concrete (worked-example data + `native_decide` checks at ℚ, keep in `RadicalLogArgument`):
`radArgRhoArcsinh`/`…Arccosh`/`…XRho`/`…X2Rho`, the `radArgSolved*`, and the `radArg_*_compute_verify`
/`…_matches_closed_form`/`…_none` theorems.

Consumers to keep compiling (names unchanged, so no edits expected):
- library: `RadicalWellFounded`, `AlgebraicDecide`, `RadicalRationalDriver` (`radIntegrateCase3`),
  `RadicalIntegralSoundness`, `RadicalLogArgGenericExamples`
- catalogs: `Sources/Doi_10_1016_S0747_7171_08_80027_2/ElementaryIntegrationFull`,
  `Sources/Hdl_1721_1_15391/Chapter5`/`Chapter6`/`IntegrateFull`

## Phased plan (each phase its own gate-green commit)

1. **Break the cycle by relocating the generic core upstream.** Create
   `Computable/Algebraic/RadicalLogArgCore.lean` holding the generic `gaussElimG`/`kernelVectorG`/
   `qOfNumG`/`qMonomialG`/`qNumG`/`qDenG`/`radLogResidualG`/`radLogBasisG`/`radLogMatrixG`/`radLogArgSolveG`
   — importing only what those need (NOT `RadicalLogIntegral`/`RadicalOverTower`). Verify with
   `wiki deps` that the generic core's real dependencies sit **upstream of `RadicalLogArgument`**; if a
   dep is downstream, that dep is the true blocker — resolve before proceeding. `RadicalLogArgGeneric`
   then re-exports the core (keeps its current name/API for existing importers).
2. **Wrap the concrete defs.** In `RadicalLogArgument`, `import …RadicalLogArgCore` and replace each
   algorithmic body with `:= <generic> (β := ℚ) …`; add a `rfl` `example` per wrapper as the faithfulness
   witness. Gate.
3. **Collapse the tiny helpers** (`qx*`, `rat*`) the same way; drop any now-unused private helper.
4. **Sweep consumers** only if a defeq wrinkle surfaces (none expected — the spike is `rfl`). Restate one
   touched theorem per file as an `example`.

## Discipline

- Per-def: confirm `rfl` before wrapping; if any pair is NOT `rfl` (e.g. a helper that genuinely differs),
  STOP and record — do not force it (the spike only proved `qMonomialG`/`radLogBasisG`; re-spike each).
- Do not touch the `radArg_*` native_decide worked examples or any `Sources/` alias.
- Keep the three genuine LRT frontiers out of scope — unrelated.
