# Recursive Risch solver architecture

Goal: solvers assembled **closed-form** (materialize fields → algorithm + soundness + completeness), and a
**recursive** solver buildable level-by-level up the differential tower `k(t₁)…(tₙ)`.

## The layering

1. **`RischSolver α`** (`RischSolver.lean`) — the closed-form *per-level* bundle. Computable data
   (`case` + `candidates`); the soundness laws (`specialSound` carrying the special value existentially,
   `reducedSound`) and the completeness contract (`SpecElem`/`NrmElem`/`descend`) are `Prop`. Derived:
   `.integrate` / `.sound` / `.isElementaryIntegrable_of_run` / `.not_isElementaryIntegrable`.

2. **`SubSolver α case`** (`RischSolverRec.lean`) — the **recursion interface**: the special-part
   (polynomial + RDE) capability that level *n* consumes from level *n−1*. One field, `special`, exactly
   the shape of `RischSolver.specialSound` for a given `case`.

3. **`RischSolver.ofSub`** (`RischSolverRec.lean`) — the **recursive step**. A `SubSolver` for `case` +
   this level's reduced-part soundness + completeness contract assemble a full `RischSolver`. Soundness and
   completeness fall out of the derived API.

4. **`SubSolver.primitive`** (`RischSolverPrimitive.lean`) — the **base case**. The special part is the
   poly-RDE output `qₚ` (as `qₚ/1`); discharged from the poly-RDE identity (canonical `Dt=1` regime, via
   `cPolyRischDEGWf_nil_field_identity`) and `canonicalReconstruction`. Bottom of the recursion.

## Why the recursion point is the RDE, not the integrator

Integrating the special part `fₚ + b/dₛ` at level *n* does **not** reduce to a lower-level *integration of a
rational function* — that has the same problem shape and would loop. The genuine descent lives in the
**polynomial Risch DE**: solving `D(q) + f·q = c` at level *n* reduces to integrating/solving RDEs whose
*coefficients* live in `k(t₁)…(tₙ₋₁)`. So the recursion payload is the special-part field identity, and the
cross-level bridge is engine-internal (`cPolyRischDEGWf`'s coefficient recursion).

## What recursion buys — and what it doesn't

| | recursion | still frontier |
|---|---|---|
| tower depth (n → n−1) | ✅ factored via `SubSolver`/`ofSub` | — |
| per-level compute-correctness (Hermite / residue / split) | — | ❌ `native_decide`-only, **shared** across levels (generic over `CField`) |
| completeness descent (Liouville) | — | ❌ Mathlib lacks the transcendental instance |

The per-level primitives are generic over the `CField`, so proving them abstractly **once** discharges every
level. Thus: **recursive assembly + abstract compute-correctness + closed base = fully closed recursive Risch
soundness.** Recursion reorganizes the tower; it does not remove the leaves.

## Phases

- **P1 (this commit)** — the skeleton: `SubSolver`, `RischSolver.ofSub`, `SubSolver.primitive`, and
  `RischSolverPrimitive` rebuilt as `ofSub (SubSolver.primitive …)`. Gate-green; the engine bridge and the
  per-level frontiers stay as named hypotheses.
- **P2** — the engine bridge `SubSolver.ofLower : RischSolver <coeff field> → SubSolver α case`, deriving
  the special identity from the lower solver's soundness through the poly-RDE. Requires exposing
  `cPolyRischDEGWf`'s coefficient recursion abstractly (the tower keystone, `QFunNZG`).
- **P3** — discharge the shared per-level compute-correctness abstractly (Hermite / RT residue / split),
  collapsing `reducedSound` and `recon` from hypotheses to theorems at every level at once.
- **P4** — the base `RischSolver` over `ℚ(x)` fully closed; assemble a genuine 2-level tower instance.
- **P5** — completeness: realize `descend` against Mathlib `IsLiouville` (the transcendental instance).
