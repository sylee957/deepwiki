# Recursive Risch solver architecture

Goal: solvers assembled **closed-form** (materialize fields → algorithm + soundness + completeness), and a
**recursive** solver buildable level-by-level up the differential tower `k(t₁)…(tₙ)`.

## Assembly by typeclass resolution (no threaded hypotheses)

The obligations are **not** threaded through `def`s. They are the fields of a **class** `LawfulRischLevel α`
(`RischTower.lean`) — the `X`/`LawfulX` idiom. Materialize **one** instance and the whole solver assembles
by resolution, parameter-free: `LawfulRischLevel.integrate` / `.sound` / `.isElementaryIntegrable_of_run` /
`.not_isElementaryIntegrable`, wherever `[LawfulRischLevel α]` is in scope. The engine frontier facts are
localized to a companion class per case (e.g. `PrimitiveFrontier α`, `RischSolverPrimitive.lean`); the
`instance [PrimitiveFrontier α] : LawfulRischLevel α` is written **once**, and everything downstream — and,
once the tower step is an instance, everything *up the tower* — resolves automatically. This is the answer
to "write the structure once, without threaded parameters, and it is assembled."

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

4. **`SubSolver.ofLower`** (`RischSolverRec.lean`) — the **recursion step**. Builds a `SubSolver` from a
   sub-`RischSolver`: the special part is *computed by another solver* `sub`, and the special-part field
   identity is **derived from `sub.sound`** (not assumed). Only `hrun` — the engine bridge relating this
   level's `integrateSpecial` hook to a `sub.integrate` run on the special subproblem — remains. This is how
   recursive integration is encoded in `RischSolver`, displacing the ad-hoc `cIntegrate…`: the special part
   delegates *downward to another `RischSolver`*, bottoming out at `SubSolver.primitive`.

5. **`SubSolver.primitive`** (`RischSolverPrimitive.lean`) — the **base case**. The special part is the
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
- **P2** — the engine bridge `SubSolver.ofLower : RischSolver <coeff field> → SubSolver α case`. **Found
  2026-07-04 (an ALGORITHM task, not just a proof):** the engine's primitive-polynomial integration is
  **constant-coefficient-only**. `cPolyRischDEGWf …[]… = cIntegratePolyG` is term-by-term
  `∫cᵢtⁱ = cᵢtⁱ⁺¹/(i+1)` (correct only when `D cᵢ = 0`); `cPrimitivePolyIntegrate`'s own docstring says
  "constant-coefficient sub-case"; `cLimitedIntegrate` exists only over the base `k = ℚ`. For non-constant
  coefficients the algorithm returns a genuinely *wrong* `some`, so `specialSound` is *false* off-regime —
  a hypothesis-free primitive `RischSolver α` is impossible with today's engine. P2 must first **implement**
  the general primitive-polynomial integrator: the top-down recursion `qⱼ′ = cⱼ − (j+1)·qⱼ₊₁` solved by a
  **tower** `cLimitedIntegrate`/`cRischDEGWf` recursing into the coefficient field (Bronstein
  `IntegratePrimitivePolynomial`), then prove its soundness — which *is* `SubSolver.ofLower`. See the memory
  note `leanproofs-primitive-poly-constant-coeff-only`.
- **P3** — discharge the shared per-level compute-correctness abstractly (Hermite / RT residue / split),
  collapsing `reducedSound` and `recon` from hypotheses to theorems at every level at once.
- **P4** — the base `RischSolver` over `ℚ(x)` fully closed; assemble a genuine 2-level tower instance.
- **P5** — completeness: realize `descend` against Mathlib `IsLiouville` (the transcendental instance).
