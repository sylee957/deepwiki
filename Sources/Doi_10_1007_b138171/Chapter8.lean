import DeepWiki.SymbolicIntegration.Computable.CoupledDE.Basic
import DeepWiki.SymbolicIntegration.Computable.CoupledDE.Assembly
import DeepWiki.SymbolicIntegration.Computable.CoupledDE.TangentReconstruct
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 8: The Coupled Differential System
Solving the coupled system `Dy₁ + f·y₁ − g·y₂ = h₁`, `Dy₂ + g·y₁ + f·y₂ = h₂` (the real/imaginary
split of a complex Risch DE `Dy + f·y = g` over `K(√a)`) — the engine that finishes the RDE oracle's
last gap, the **tangent cancellation case** `PolyRischDECancelTan` that the §6.6 dispatcher deferred.
The §8.4 hypertangent case is now rendered as a **computable** solver over `k = ℚ(x)`, `t = tan(x)`
(`DeepWiki.SymbolicIntegration.Computable.CoupledDE.Basic`): the base coupled system `cCoupledDESystem`
(eq. 8.2/8.10, polynomial ansatz over ℚ(x)) and the degree-recursive tangent box `cCoupledDECancelTan`
(book p.265), validated end-to-end on Example 8.4.1.

**Computable-vs-abstract.** Each algorithm below is a computable function over `CPolyG ℚ` (= ℚ(x), the
base the §8.4 tangent recursion reaches) validated by `native_decide` on Example 8.4.1. Both the **base**
coupled system AND the §8.4 **tangent** box now have abstract soundness **PROVED unconditionally**
(`native_decide`-free): `cCoupledDESystem_sound` (`ComputableCoupledDEAssembly`) for the base solve
(via `cConstSolveUniqueQ_sound` + matrix-assembly faithfulness), and `cCoupledDECancelTan_sound`
(`ComputableCoupledDETangentReconstruct`) for the tangent box — its degree-by-degree telescoping
(`evalAtI` projection mod `t²+1` + `divByTminusI` synthetic division by `t − √−1`) is proven correct in
the Gaussian extension `AdjoinRoot (X²+1)` over `ℚ[x]` (`reconstruct`), discharging the engine's own
`cancelTanClearedCheck`. Still deferred: the §8.1–8.3 denominator/pole bounds on the 2-vector, the §8.2
hyperexponential coupled case (`CoupledDECancelExp`), and the §8.3 general nonlinear case.

## NOT YET FORMALIZED (audit 2026-06-24)
§8.1 The Primitive Case — coupled solver, primitive monomial (the §8.1–8.3 `WeakNormalizer` /
  `RdeNormalDenominator` / `RdeBoundDegree` analogues for the 2-vector — the denominator / pole bounds
  on the pair, book p.257–264 — are documented but not run; `cCoupledDESystem` takes the ansatz degree
  bound from the caller, which suffices on the worked tangent example).
§8.2 The Hyperexponential Case — the `CoupledDECancelExp` coupled solver (book p.261), the symmetric
  continuation of the realized §8.4 tangent box.
§8.3 The Nonlinear Case — coupled solver for general `δ ≥ 2` monomials other than the hypertangent
  `t²+1` (no general algorithm in the book itself, book p.263; only the hypertangent specialization,
  where `√−1` generates a usable irreducible, is realized).
(The chapter is algorithm-driven with few separately-numbered results; it reduces the coupled system to
the parametric problems of Chapter 7. The §8.4 **hypertangent** case — `cCoupledDESystem`/
`cCoupledDECancelTan`, the `PolyRischDECancelTan` that finished the RDE oracle — is now computable +
native_decide-validated on Example 8.4.1, see `alg_8_1_coupledDESystem`/`alg_8_4_cancelTan`/
`ex_8_4_1_base`/`ex_8_4_1`.)

## Book misprints recorded (found while validating Example 8.4.1)
* **Example 8.4.1, the `CoupledDESystem` call (book p.266 step 4).** The book writes the base call as
  `CoupledDESystem(0, 4x−2, −8x²+1, 4−4x)`, but the system it then *displays* has right-hand side
  `(2(1−4x²); 4(1−x))`; the third argument `−8x²+1` is a misprint for `2−8x²`, the value
  `c₁(√−1) + c₂(√−1)√−1` actually produces — and the value that makes the book's solution `(−1, 2x+1)`
  solve the displayed system.
* **The `CoupledDECancelTan(b₀, b₂, c₁, c₂, D, n)` box, the (2,2) matrix entry (book p.265).** The box
  prints the (2,2) entry as `b₀ + nηt`; the worked Example 8.4.1's system (8.15) `[[−2t, −4x], [4x, −2t]]`
  — and the eq-8.2 real form `[[f₁, af₂], [f₂, f₁]]` of `Dy + b·y = c`, where `f₁ = b₀ − nηt` sits on
  **both** diagonals — has `b₀ − nηt` there, so the box's `+` is a misprint for `−`. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.CPolyG

namespace DeepWiki.Si

/-! ## §8.1/§8.4 The base coupled differential system over ℚ(x) — computable + validated -/

/-- **The base coupled differential system `CoupledDESystem`** (§8.1/§8.4, eq. 8.2/8.10, the recursion
target, book p.257/265): the computable `cCoupledDESystem a b1 b2 z1 z2 d` over `k = ℚ(x)`
(`D = d/dx`), solving `(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]] · (y₁; y₂) = (z₁; z₂)` for `y₁, y₂ ∈ ℚ[x]` of
degree `≤ d` by a polynomial ansatz reduced to a single ℚ-linear system (`cConstSolveUniqueQ`/`crref`).
Returns `some (y₁, y₂)` or `none`. Computable + `native_decide`-validated; abstract correctness (the
eq. 8.3 equivalence) deferred. -/
def alg_8_1_coupledDESystem := @cCoupledDESystem

/-- **Example 8.4.1, the base coupled solve** (§8.4, book p.266 step 4): `cCoupledDESystem` on
`(a, b₁, b₂, z₁, z₂) = (−1, 0, 4x−2, 2−8x², 4−4x)` returns the book's `(s₁, s₂) = (−1, 2x+1)`, verified
to **actually solve** the system `(Dy₁; Dy₂) + [[0, −(4x−2)], [4x−2, 0]] · (y₁; y₂) = (2−8x²; 4−4x)` over
ℚ(x) by `coupledClearedCheck` (both cleared row residuals vanish), `native_decide`. *(The book's
third argument `−8x²+1` is a misprint for `2−8x²` — see the chapter misprint note.)* -/
abbrev ex_8_4_1_base := @coupledDESystem_example

/-- **Base coupled-system soundness — unconditional** (§8.1/§8.4, eq. 8.2/8.3, `native_decide`-free): a
returned `cCoupledDESystem` solve `(y₁, y₂)` solves the two `ℚ[x]` row identities
`D(y₁) + b₁y₁ + a·b₂y₂ = z₁`, `D(y₂) + b₂y₁ + b₁y₂ = z₂`. No cleared-check hypothesis: the engine's check
is discharged from the proven ℚ-Gaussian-elimination correctness (`cConstSolveUniqueQ_sound`) via the
matrix-assembly faithfulness bridge (`coupledClearedCheck_of_cCoupledDESystem`). The abstract soundness of
the §8 base coupled system. -/
abbrev alg_8_1_coupledDESystem_sound := @cCoupledDESystem_sound

/-! ## §8.4 The Hypertangent Case — the tangent RDE cancellation, computable + validated -/

/-- **The tangent RDE cancellation `CoupledDECancelTan`** (§8.4, the `CoupledDECancelTan(b₀, b₂, c₁, c₂,
D, n)` box, book p.265), `t = tan(x)`, `Dt = t²+1`, `η = 1`, `a = −1`: the computable
`cCoupledDECancelTan dbound b0 b2 c1 c2 n` over `k = ℚ(x)`, solving the `t`-polynomial coupled system
`(Dq₁; Dq₂) + [[b₀ − nηt, −b₂], [b₂, b₀ − nηt]] · (q₁; q₂) = (c₁; c₂)` for `q₁, q₂ ∈ k[t]` of `t`-degree
`≤ n`, degree-by-degree from the top (project mod `t²+1`, base-solve over ℚ(x) via `cCoupledDESystem`,
divide by `t − √−1`). This **is** the `PolyRischDECancelTan` that `ComputableRischDE`'s §6.6 dispatcher
deferred. Computable + `native_decide`-validated; abstract correctness now **PROVED unconditionally**
(`alg_8_4_cancelTan_sound`). *(The book's box prints the (2,2) entry as `b₀ + nηt` — a misprint for
`b₀ − nηt`; see the chapter misprint note.)* -/
def alg_8_4_cancelTan := @cCoupledDECancelTan

/-- **Tangent RDE cancellation soundness — unconditional** (§8.4, book p.265, `native_decide`-free): a
returned `cCoupledDECancelTan … 2` solve `(q₁, q₂)` solves the §8.4 tangent coupled `t`-polynomial system
(8.15) at the `ℚ[x][t]` level (`D = ∂x + (t²+1)∂t`, diagonal shift `−2t`). No cleared-check hypothesis:
the §8.4 degree-by-degree telescoping (`evalAtI` projection mod `t²+1` + `divByTminusI` synthetic division
by `t − √−1`) is proven correct (`reconstruct`, in `AdjoinRoot (X²+1)` over `ℚ[x]`), discharging the
engine's own `cancelTanClearedCheck`. The §8.4 tangent box's abstract soundness. -/
abbrev alg_8_4_cancelTan_sound := @cCoupledDECancelTan_sound

/-- **Example 8.4.1 — the tangent RDE cancellation runs end-to-end** (§8.4, book p.265–267): the case
`ComputableRischDE`'s §6.6 dispatcher deferred. For the system (8.15) over `t = tan(x)` — `b₀ = 0`,
`b₂ = 4x`, diagonal `−2t = −nηt` (`n = 2`, `η = 1`), `c₁ = −t²+2t−8x²+1`, `c₂ = 2(1−2x) = 2−4x`, degree
bound `n = 2` — `cCoupledDECancelTan` returns the book's solution `q₁ = t − 1`, `q₂ = 2x` (hence
`y₁ = (t−1)/(t²+1)`, `y₂ = 2x/(t²+1)`, book p.267), verified to **actually solve** the coupled
`t`-polynomial system (8.15) by `cancelTanClearedCheck` (both cleared row identities vanish),
`native_decide`. -/
abbrev ex_8_4_1 := @rischDE_cancelTan_example

end DeepWiki.Si
