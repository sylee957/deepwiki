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

- **Phase 1 — base single-`w` limited integration (this file's first deliverable).**
  `cLimitedIntegrateSingleBase (a η : QFunNZG ℚ) : Option (QFunNZG ℚ × ℚ)` returning `(b, c)` with
  `a = D(b) + c·η`, built from `cLinearConstraintsQ [a,η]` + `cNullspaceBasisQ` (find the `c₀ ≠ 0` kernel vector,
  normalize `c₀ = 1`, `c = −c₁`) + base polynomial integration of the cleared (polynomial) residual for `b`.
  Native-`decide` validated on a degree-raising example (`a = 1 + 1/x`, `η = 1/x` ⟹ `(b,c) = (x, 1)`). Scope:
  the **polynomial-`b`** regime (matches `cParamRischDE`); rational-`b` (Hermite pre-pass) is Phase 1b.
- **Phase 1b — base rational `b`.** Hermite-reduce the rational part before the kernel solve, so `b ∈ ℚ(x)`
  (not just `ℚ[x]`). Extends `cLimitedIntegrate` past its polynomial-only limitation.
- **Phase 2 — tower recursion.** `cLimitedIntegrateSingleG` over `QFunNZG β` (base case = Phase 1/1b; recursive
  case = Hermite + residue at level `β` + recurse), the single-`w` analogue of `cIntegrateReducedLrtG`.
- **Phase 3 — wire into the coefficient recursion.** Replace `towerCoeffIntegrateLrt`'s log-free discharge with
  the single-`w` version; thread the returned `c` into a degree-`(deg p + 1)` `q` in `towerPolyIntegrateLrt`.
- **Phase 4 — soundness.** Extend `cLimitedIntegratePolyRatG_poly_sound` to the degree-raising form; per-level
  base-change soundness for the tower recursion.

## Retirements (subsumable/dead)

- `cLimitedIntegrate` (log variant) is **not** on the fix path (needs raw `η`, and it is polynomial-only);
  keep only if a catalog item cites §7.2, else fold into the generic parametric solver.
- `cParamLogDerivCandidate`, `cBaseIsProper` — internal helpers, 0 external uses; retire if the generic
  parametric path subsumes them.
- Audit for ℚ-specific utilities that a `CPolyG α` base+abbrev would subsume (`qnormPairG`, `cLcmQ`, `cCoeffQ`).
