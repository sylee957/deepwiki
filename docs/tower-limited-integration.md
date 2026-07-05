# Tower limited integration — closing the recursive primitive case

## The gap (faithfulness, Bronstein §5.8 / §5.12)

Our recursive primitive-polynomial integrator `cLimitedIntegratePolyRatG` (`RischSolverTower.lean`) solves the
coefficient system `D(bᵢ) = aᵢ − (i+1)·η·bᵢ₊₁` with a **log-free in-field** discharge
(`towerCoeffIntegrateLrt` → `integrateRationalLrt`, i.e. it only finds `b` with `Db = a`, the `c = 0` slice).

Bronstein's `IntegratePrimitivePolynomial` (Thm 5.8.1, book p.158) instead discharges each leading coefficient
with **`LimitedIntegrate(a, Dt)`** (§5.12): find `b ∈ k`, `c ∈ Const(k)` with

```
a = Db + c·Dt              (Dt = η, the primitive's derivative)
```

and emits the **degree-raising** term `c·tᵐ⁺¹/(m+1)` — so the antiderivative `q` can have degree `deg p + 1`.
Without the `c`, we decline every primitive-polynomial integral whose antiderivative genuinely gains a degree
(e.g. Bronstein's Li(x) example: `LimitedIntegrate(t₀+1/t₀, 1/t₀) = (x·log x − x, 1)`).

**Scope clarification (verified 2026-07-05):** the `bᵢ` stay **in-field** — `LimitedIntegrate` returns `b ∈ k`,
no *free* logs — so there is **no log-threading and no result-type change** (`towerPolyIntegrateLrt` keeps
returning a polynomial `q`, just one degree taller with a constant leading term). The *entire* gap is the
single-`w` limited integration above. The generator is the **raw** `η = Dt` (giving a `c·t` term), **not** a
logarithmic derivative `Dw/w` — so the vehicle is `cParamRischDE [a, η]` directly, not the log-variant
`cLimitedIntegrate`.

## What we already have

- **Base ℚ constant-field linear solver** (`Parametric.lean`): `crref`, `cNullspaceBasisQ`, `cConstSolveUniqueQ`.
  **Reusable verbatim at every tower level** — `Const(k(t)) = Const(k) = ℚ` for a monomial `t`, so the linear
  algebra is always over ℚ. (Widely reused already: `cConstSolveUniqueQ` in 6 files, `cNullspaceBasisQ` in 4.)
- **Base parametric RDE** `cParamRischDE (gnums gdens : List (CPolyG ℚ))` — solves `Dp = Σ cᵢ gᵢ` for a
  **polynomial** `p ∈ ℚ[t]`, returning the ℚ-kernel of admissible `(c₁,…,cₘ)`. It clears denominators
  (`cLinearConstraintsQ`) and reads the ℚ-matrix `Mᵢⱼ = coeff(rⱼ, tⁱ)`.
- **Base limited integration** `cLimitedIntegrate` — the §7.2 *log* variant (generators `Dwᵢ/wᵢ`), **polynomial
  `v` only** (the rational refinement is documented-but-unbuilt). Not directly what the coefficient recursion
  needs (raw `η`, not `Dw/w`), and incomplete for rational `b`.

## Subtleties that make this a real (bounded) development, not a wire

1. **Base is polynomial-only.** `cParamRischDE`/`cLimitedIntegrate` solve for *polynomial* `p`. A complete base
   `LimitedIntegrate` over `ℚ(x)` needs a **Hermite reduction** first (rational part), then the polynomial part
   via the kernel solve. So even the base case is more than the existing code.
2. **Higher levels recurse.** For a primitive `t` over `k`, §5.12: `a = Dv + c·Dt` "is reduced to a limited
   integration problem in `k`" — i.e. `LimitedIntegrate` over `QFunNZG β` calls `LimitedIntegrate` over `β`.
   Structurally parallel to the main tower integrator (`RischSolverTowerLrt`), base case = the ℚ solver.
3. **Degree-raising soundness.** `cLimitedIntegratePolyRatG_poly_sound` currently proves `D_tower(q) = p` for
   `deg q = deg p`; it must extend to `deg q = deg p + 1` with the constant leading coefficient `c`.

## Phased plan

Each phase is its own gate-green commit.

- **Phase 1 — base single-`w` limited integration. ✅ DONE (`LimitedIntegrateSingle.lean`).**
  `cLimitedIntegrateSingleBase (a η : QFunNZG ℚ) : Option (QFunNZG ℚ × ℚ)` returning `(b, c)` with
  `a = D(b) + c·η`, built from `cLinearConstraintsQ [a,η]` + `cNullspaceBasisQ` (find the `c₀ ≠ 0` kernel vector,
  normalize `c₀ = 1`, `c = −c₁`) + base polynomial integration of the cleared residual for `b`. Native-`decide`
  validated: `LimitedIntegrate(1+1/x, 1/x) = (x, 1)`. Scope: the **polynomial-`b`** regime; rational-`b` is 1b.
- **Phase 3-core — degree-raising recursion. ✅ DONE (`LimitedIntegrateSingle.lean`).**
  `cIntegratePrimPolyDegRaiseG η limInt fuel p` = Bronstein's `IntegratePrimitivePolynomial` (Thm 5.8.1):
  peel `a·tᵐ`, `limInt(a) = (b,c)`, `q₀ = c/(m+1)·t^(m+1) + b·tᵐ`, recurse on `p − D_tower(q₀)`. Native-`decide`
  validated end-to-end at **2 levels** (`k = ℚ(x)(log x)`, `Dt = 1/x`): `∫((1+1/x)·t + 1) = t²/2 + x·t`, with
  `D_tower(q) = p` and `deg q = deg p + 1` (the degree-raising the log-free discharge declines). A 2-level tower
  needs only Phase 1 + this (coefficients live at the base `ℚ(x)`); higher towers need Phase 2.
- **Phase 1b — base rational `b`.** Hermite-reduce the rational part before the kernel solve, so `b ∈ ℚ(x)`
  (not just `ℚ[x]`). Extends `cLimitedIntegrate` past its polynomial-only limitation.
- **Phase 2 — tower recursion (3+ levels).** `cLimitedIntegrateSingleG` over `QFunNZG β` (base case = Phase 1/1b;
  recursive case = Hermite + residue at level `β` + recurse), the single-`w` analogue of `cIntegrateReducedLrtG`.
- **Phase 3-wire — wire into the LRT solver.** Replace `towerCoeffIntegrateLrt`'s log-free discharge +
  `cLimitedIntegratePolyRatG` (fixed-degree) with the `(b,c)` single-`w` version + `cIntegratePrimPolyDegRaiseG`.
- **Phase 4 — soundness.** Prove `D_tower(q) = p` for `cIntegratePrimPolyDegRaiseG` (abstract, the degree-raising
  analogue of `cLimitedIntegratePolyRatG_poly_sound`); per-level base-change soundness for the tower recursion.

## Retirements (subsumable/dead)

- **`cLimitedIntegratePolyRatG` (fixed-degree coefficient recursion) → subsumed by `cIntegratePrimPolyDegRaiseG`.**
  The new recursion generalizes it (`limInt` returning `(b, 0)` recovers the fixed-degree case). Retire once
  Phase 3-wire replaces the solver's use of it and Phase 4 ports its soundness. Not retireable yet — it is
  load-bearing in `towerPolyIntegrateLrt` with a proven `_poly_sound`.
- **Already retired (prior LRT rebase):** the rational tower solver `towerPolyIntegrate`/`towerPrimitiveCase`
  (`RischTower.lean` deleted) — 0 uses.
- `cLimitedIntegrate` (log variant) is **not** on the fix path (needs raw `η`, polynomial-only), but it is a
  **cataloged §7.2 book item** (`Sources/Doi_10_1007_b138171/Chapter7.lean`) — keep for coverage.
- `cParamLogDerivCandidate`, `cBaseIsProper` — 0 external uses but live internal deps of the cataloged
  `cParamLogDeriv`/`cParametricLogDeriv`; not dead. Not redundant.
