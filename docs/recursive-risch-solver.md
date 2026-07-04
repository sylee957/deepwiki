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

## The layering (one abstraction)

1. **`LawfulRischLevel α`** (`RischTower.lean`) — **the** Risch-solver abstraction (a class). Computable data
   (`case` + `candidates`); the soundness laws (`specialSound` carrying the special value existentially,
   `reducedSound`) and the completeness contract (`SpecElem`/`NrmElem`/`descend`) as `Prop` fields. The
   derived API lives directly on it: `LawfulRischLevel.integrate` / `.sound` / `.isElementaryIntegrable_of_run`
   / `.not_isElementaryIntegrable`. (The earlier duplicates — a `RischSolver` *structure* with identical
   fields, and a `SubSolver`/`ofSub`/`ofLower` def-combinator layer — were removed; the class subsumes both.)

2. **`PrimitiveFrontier α`** (`RischSolverPrimitive.lean`) — the **base**: the primitive-case engine frontier
   facts as a companion class, with `instance [PrimitiveFrontier α] : LawfulRischLevel α` (the `specialSound`
   law proven inside from the poly-RDE identity + `canonicalReconstruction`). Written once → the whole solver
   resolves.

3. **The tower step** (to build) — `instance [LawfulRischLevel α] : LawfulRischLevel (QFunNZG α)`. Its
   `specialSound` is *derived from the lower instance's `sound`* (the special part is computed by the
   level below), displacing the ad-hoc `cIntegrate…`. This is where the recursion becomes automatic.

## Why the recursion point is the RDE, not the integrator

Integrating the special part `fₚ + b/dₛ` at level *n* does **not** reduce to a lower-level *integration of a
rational function* — that has the same problem shape and would loop. The genuine descent lives in the
**polynomial Risch DE**: solving `D(q) + f·q = c` at level *n* reduces to integrating/solving RDEs whose
*coefficients* live in `k(t₁)…(tₙ₋₁)`. So the recursion payload is the special-part field identity, and the
cross-level bridge is engine-internal (`cPolyRischDEGWf`'s coefficient recursion). In the class world this
bridge is the one `sorry`-free frontier field of the tower-step instance.

## What recursion buys — and what it doesn't

| | recursion | still frontier |
|---|---|---|
| tower depth (n → n−1) | ✅ factored via the recursive `LawfulRischLevel` instance | — |
| per-level compute-correctness (Hermite / residue / split) | — | ❌ `native_decide`-only, **shared** across levels (generic over `CField`) |
| completeness descent (Liouville) | — | ❌ Mathlib lacks the transcendental instance |

The per-level primitives are generic over the `CField`, so proving them abstractly **once** discharges every
level. Thus: **recursive assembly + abstract compute-correctness + closed base = fully closed recursive Risch
soundness.** Recursion reorganizes the tower; it does not remove the leaves.

## Phases

- **P1 (done)** — the one abstraction: the `LawfulRischLevel α` class with the derived
  `integrate`/`sound`/completeness API, and the primitive base `instance [PrimitiveFrontier α] :
  LawfulRischLevel α`. Gate-green; the engine frontiers stay as `PrimitiveFrontier` fields. (The interim
  `RischSolver` structure and `SubSolver`/`ofSub`/`ofLower` combinators were folded into the class and
  removed.)
- **P2** — the tower-step `instance [LawfulRischLevel α] : LawfulRischLevel (QFunNZG α)`, deriving
  `specialSound` from the lower instance's `sound`. **Found
  2026-07-04 (an ALGORITHM task, not just a proof):** the engine's primitive-polynomial integration is
  **constant-coefficient-only**. `cPolyRischDEGWf …[]… = cIntegratePolyG` is term-by-term
  `∫cᵢtⁱ = cᵢtⁱ⁺¹/(i+1)` (correct only when `D cᵢ = 0`); `cPrimitivePolyIntegrate`'s own docstring says
  "constant-coefficient sub-case"; `cLimitedIntegrate` exists only over the base `k = ℚ`. For non-constant
  coefficients the algorithm returns a genuinely *wrong* `some`, so `specialSound` is *false* off-regime —
  a hypothesis-free primitive `RischSolver α` is impossible with today's engine. P2 must first **implement**
  the general primitive-polynomial integrator: the top-down recursion `qⱼ′ = cⱼ − (j+1)·qⱼ₊₁` solved by a
  **tower** `cLimitedIntegrate`/`cRischDEGWf` recursing into the coefficient field (Bronstein
  `IntegratePrimitivePolynomial`), then prove its soundness — which *is* the tower-step instance. See the
  memory note `leanproofs-primitive-poly-constant-coeff-only`.
- **P3** — discharge the shared per-level compute-correctness abstractly (Hermite / RT residue / split),
  collapsing `reducedSound` from a `PrimitiveFrontier` field to a theorem at every level at once.
- **P4** — the base `LawfulRischLevel` over `ℚ(x)` fully closed; assemble a genuine 2-level tower instance.
- **P5** — completeness: realize `descend` against Mathlib `IsLiouville` (the transcendental instance).
