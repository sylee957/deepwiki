import DeepWiki.SymbolicIntegration.ComputableRischDE
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 6: The Risch Differential Equation
Solving `Dy + f·y = g` for `y` in a monomial extension — the engine of the exponential case of the
integration algorithm. The **whole RDE pipeline** is now rendered as a **computable** solver over the
monomial tower ℚ(x)[t] (`DeepWiki.SymbolicIntegration.ComputableRischDE`): weak normalizer + normal
denominator (§6.1/§6.2), special denominator (§6.2), degree bound (§6.3), SPDE (§6.4), the
non-cancellation case (§6.5) and the primitive + hyperexponential cancellation cases (§6.6), assembled
into the full `cRischDE` and validated end-to-end on Examples 6.5.1 / 6.4.1.

**Computable-vs-abstract.** Each stage below is a computable function over `CPolyG QFunNZ` (= ℚ(x)[t])
validated by `native_decide` on the book's worked example (matching the book's intermediate values, or
checking that the returned `y` *actually solves* the equation via the cleared polynomial identity); the
*abstract* correctness theorems (the `Dy + fy = g ↔ a·Dq + b·q = c` equivalence, Thm 6.4.1, etc.) are
**NOT** proved. The §6.6 hypertangent cancellation case (`PolyRischDECancelTan`, needs the Ch. 8
coupled system) and the full §5.12/§7.3 parametric-logarithmic-derivative recognizer remain deferred.

## NOT YET FORMALIZED (audit 2026-06-24)
§6.1 The Normal Part of the Denominator: Def 6.1.1; Thm 6.1.2; Cor 6.1.1; Lemma 6.1.1; Ex 6.1.1
  (abstract correctness; the algorithms `WeakNormalizer` + `RdeNormalDenominator` are now computable +
  native_decide-validated on Ex 6.1.2, see `alg_6_1_weakNormalizer`/`alg_6_2_normalDenominator`/
  `ex_6_1_2`).
§6.2 The Special Part of the Denominator: Lemma 6.2.1, Lemma 6.2.2, Lemma 6.2.4; Ex 6.2.1 (abstract
  correctness; `RdeSpecialDenominator` is now computable + native_decide-validated on Ex 6.2.2, see
  `alg_6_2_specialDenominator`/`ex_6_2_2`).
§6.3 Degree Bounds: Cor 6.3.1; Lemma 6.3.1, Lemma 6.3.2, Lemma 6.3.3, Lemma 6.3.4, Lemma 6.3.5;
  Ex 6.3.1, Ex 6.3.2, Ex 6.3.3 (abstract correctness; `RdeBoundDegree` is now computable +
  native_decide-validated on Ex 6.3.4, see `alg_6_3_boundDegree`/`ex_6_3_4`).
§6.4 The SPDE Algorithm: Thm 6.4.1 (abstract correctness; the algorithm `SPDE` is now computable, see
  `alg_6_4_spde`, and exercised through the full-solver no-solution run `ex_6_4_1`).
§6.5 The Non-Cancellation Cases: Lemma 6.5.1; Ex 6.5.2, Ex 6.5.3 (abstract correctness; the algorithm
  `PolyDESolve`/`PolyRischDENoCancel` is now computable + native_decide-validated end-to-end on Ex
  6.5.1, see `alg_6_5_polyRischDENoCancel`/`ex_6_5_1`).
§6.6 The Cancellation Cases: Ex 6.6.1; the **hypertangent** cancellation solver `PolyRischDECancelTan`
  (`δ = 2`, recurses to a base RDE over `k(√−1)` / a Ch. 8 `CoupledDESystem`) — the **primitive**
  (`PolyRischDECancelPrim`) and **hyperexponential** (`PolyRischDECancelExp`) cancellation solvers are
  now computable + native_decide-validated (see `alg_6_6_cancelPrim`/`alg_6_6_cancelExp`/
  `ex_6_6_cancelPrim`/`ex_6_6_cancelExp`).
Exercise 6.1.

The remaining gaps are the **abstract correctness theorems** (the pipeline is computationally rendered
and example-validated but not proved correct), the §6.6 hypertangent cancellation case (the Ch. 8
coupled-system layer), the full §5.12/§7.3 logarithmic-derivative-of-a-radical recognizer (the
`cParametricLogDeriv` constant stub decides only the reachable obstruction), and the cancellation
refinements of `RdeSpecialDenominator`/`RdeBoundDegree` (which only *raise* the bound in that case). -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.CPolyG

namespace DeepWiki.Si

/-! ## §6.1 The Normal Part of the Denominator — computable + validated -/

/-- **Algorithm `WeakNormalizer`** (§6.1, p.183): the computable
`cWeakNormalizer Dt fuel fnum fden = q ∈ k[t]` over the tower, returning `q` such that `f − Dq/q` is
weakly normalized (via the residue resultant and its positive integer roots). Computable +
`native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_6_1_weakNormalizer := @cWeakNormalizer

/-- **Algorithm `RdeNormalDenominator`** (§6.2 eq. 6.2 / Cor 6.1.1, p.185): the computable
`cRdeNormalDenominator Dt fuel fnum fden gnum gden` over the tower, returning `none` (no solution) or
the reduction quadruplet `(a, b, c, h)` reducing `Dy + f·y = g` to the simple-part equation
`a·Dq + b·q = c` with `q = y·h`. Computable + `native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_6_2_normalDenominator := @cRdeNormalDenominator

/-- **Example 6.1.2** (§6.1/§6.2, p.183/185/186): for `Dy + (t²+1)y = 1/t²` (`t = tan x`, `Dt = 1+t²`),
`cWeakNormalizer` returns `q = 1` (already weakly normalized) and `cRdeNormalDenominator` returns the
book's quadruplet `(a, b, c, h) = (t, (t−1)(t²+1), 1, t)`, pinned componentwise over ℚ(x)[t]
(`native_decide`). -/
abbrev ex_6_1_2 := @rischDE_normalDenominator_example

/-! ## §6.2 The Special Part of the Denominator — computable + validated -/

/-- **Algorithm `RdeSpecialDenominator`** (§6.2, the `RdeSpecialDenom{Exp,Tan}` boxes, p.190/192): the
computable `cRdeSpecialDenominator Dt fuel a b c` over the tower, reducing the simple-part equation
`a·Dq + b·q = c` to a polynomial equation over `k[t]` by clearing the special factor `p` (the
substitution `q = h·pⁿ`). Computable + `native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_6_2_specialDenominator := @cRdeSpecialDenominator

/-- **Example 6.2.2** (§6.2, the `RdeSpecialDenomTan` box, p.192): continuing Ex 6.1.2,
`cRdeSpecialDenominator` on `(a, b, c) = (t, (t−1)(t²+1), 1)` (special irreducible `p = t²+1`,
`n_b = 1`, `n_c = 0`, `n = N = 0`) returns the *unchanged* `(t, (t−1)(t²+1), 1, 1)` over ℚ(x)[t]
(`native_decide`). -/
abbrev ex_6_2_2 := @rischDE_specialDenominator_example

/-! ## §6.3 Degree Bounds — computable + validated -/

/-- **Algorithm `RdeBoundDegree`** (§6.3, the `RdeBoundDegree{Base,Prim,Exp,NonLinear}` boxes,
p.198–201): the computable `cRdeBoundDegree Dt fuel a b c = n ∈ ℕ` over the tower, an explicit upper
bound on `deg_t(q)` for any polynomial solution `q` of `a·Dq + b·q = c`, case-split by `δ = deg(Dt)`.
Computable + `native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_6_3_boundDegree := @cRdeBoundDegree

/-- **Example 6.3.4** (§6.3, the `RdeBoundDegreeNonLinear` box, p.202): continuing Ex 6.1.2/6.2.2,
`cRdeBoundDegree` on `(a, b, c) = (t, (t−1)(t²+1), 1)` with `δ = 2` returns the degree bound `0`
(any polynomial solution lies in ℚ(x)), `native_decide`. -/
abbrev ex_6_3_4 := @rischDE_boundDegree_example

/-! ## §6.4 The SPDE Algorithm — computable -/

/-- **Algorithm `SPDE`** (§6.4, Rothstein's `SPDE(a, b, c, D, n)` box, p.203): the computable
`cSPDE Dt fuel a b c n` over the tower — the recursive `gcd(a, b)`-peeling reduction of the
degree-bounded `a·Dq + b·q = c` to one with `a = 1`. Returns `none` ("no solution of degree ≤ n") or
`(b̄, c̄, m, α, β)`. Computable (exercised through the full-solver no-solution run `ex_6_4_1`); abstract
correctness (Thm 6.4.1) deferred. -/
noncomputable abbrev alg_6_4_spde := @cSPDE

/-! ## §6.5 The Non-Cancellation Cases — computable + validated -/

/-- **Algorithm `PolyRischDENoCancel`** (§6.5, the `PolyRischDENoCancel1(b, c, D, n)` box, p.208): the
computable `cPolyRischDENoCancel Dt fuel b c n` over the tower — the non-cancellation case solving
`Dq + b·q = c` degree-by-degree from the top down (`lc(c) = lc(b)·lc(q)`). Returns
`Option (CPolyG QFunNZ)`. Computable + `native_decide`-validated end-to-end; abstract correctness
deferred. -/
noncomputable abbrev alg_6_5_polyRischDENoCancel := @cPolyRischDENoCancel

/-- **Algorithm `PolyRischDE`** (§6.5/§6.6 dispatcher): the computable `cPolyRischDE Dt fuel b c n`
routing `Dq + b·q = c` to the non-cancellation solver or the primitive/hyperexponential cancellation
solvers by monomial type and `deg(b)` (Lemma 6.5.1). -/
noncomputable abbrev alg_6_5_polyRischDE := @cPolyRischDE

/-- **The full Risch DE solver**: the computable `cRischDE Dt fuel fnum fden gnum gden` over the tower,
chaining normal denominator (§6.2) → special denominator (§6.2) → degree bound (§6.3) → SPDE (§6.4) →
PolyRischDE (§6.5/§6.6), reconstructing `y` solving `Dy + f·y = g`, or `none`. Validated end-to-end on
Ex 6.5.1 / 6.4.1; abstract correctness deferred. -/
noncomputable abbrev alg_6_rischDE := @cRischDE

/-- **Example 6.5.1** (§6.5, p.208): the full `cRischDE` solves `Dy + (t²+1)y = t³+(x+1)t²+t+(x+2)`
(`t = tan x`) end-to-end, returning `y = t + x`, verified to *actually solve* the equation by the
cleared polynomial identity over ℚ(x)[t] (`native_decide`). -/
abbrev ex_6_5_1 := @rischDE_solve_example

/-- **Example 6.4.1** (§6.4, p.204): the full `cRischDE` on `Dy + (t²+1)y = 1/t²` (`t = tan x`) returns
`none` — `SPDE` reaches `n = −1 < 0` with `c ≠ 0`, so `∫ e^{tan x}/tan²x dx` is not elementary
(`native_decide`). -/
abbrev ex_6_4_1 := @rischDE_noSolution_example

/-! ## §6.6 The Cancellation Cases — primitive + hyperexponential computable + validated -/

/-- **Algorithm `PolyRischDECancelPrim`** (§6.6, p.212): the computable
`cPolyRischDECancelPrim Dt fuel b c n` over the tower — the primitive cancellation case (`Dt ∈ k`,
`b ∈ k*`, where `cPolyRischDENoCancel` cannot proceed), recursing degree-by-degree into the eq. 6.23
base Risch DE over `k = ℚ(x)` after the §5.12 `b = Dz/z` test. Returns `Option (CPolyG QFunNZ)`.
Computable + `native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_6_6_cancelPrim := @cPolyRischDECancelPrim

/-- **Algorithm `PolyRischDECancelExp`** (§6.6, p.213): the computable
`cPolyRischDECancelExp Dt fuel b c n` over the tower — the hyperexponential cancellation case
(`Dt/t = η ∈ k`, `δ = 1`, `b ∈ k*`), recursing degree-by-degree into the eq. 6.24 base RDE
`RischDE(b + m·η, lc(c))` over ℚ(x). Returns `Option (CPolyG QFunNZ)`. Computable +
`native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_6_6_cancelExp := @cPolyRischDECancelExp

/-- **The base Risch DE over ℚ(x)** (§6.6 eq. 6.23): the computable `cRischDEBase fuel b c =
Option QFunNZ` solving `Ds + b·s = c` over `k = ℚ(x)` — the leading-coefficient recursion target of the
cancellation cases (the `k`-constant fast path plus the general non-constant solve via
`cRationalRDE`). -/
noncomputable abbrev alg_6_6_rischDEBase := @cRischDEBase

/-- **The rational Risch DE over ℚ(x)** (§6.6 eq. 6.23 base solve): the computable
`cRationalRDE fuel bnum bden cnum cden` solving `Ds + b·s = c` over `k = ℚ(x)` self-contained over
`CPolyG ℚ` — the whole Ch. 6 pipeline re-run with the trivial primitive monomial `t = x` over ℚ.
Computable + `native_decide`-validated (`ex_6_6_rationalRDE`). -/
def alg_6_6_rationalRDE := @cRationalRDE

/-- **Example (§6.6, p.212)**, primitive cancellation: `cPolyRischDECancelPrim` on
`Dq + 1·q = log(x) + 1/x` (`t = log x`, `b = 1 ∈ ℚ*`) solves to `q = log(x) = t`, verified to *actually
solve* `Dq + b·q = c` by the cleared difference over ℚ(x)[t] (`native_decide`); the dispatcher
`cPolyRischDE` routes the same input to the cancellation solver. -/
abbrev ex_6_6_cancelPrim := @rischDE_cancel_example

/-- **Example (§6.6, p.213)**, hyperexponential cancellation: `cPolyRischDECancelExp` on
`Dq + (1/x)·q = (2+x)·exp(x)` (`t = exp x`, `η = 1`, `b = 1/x`) solves to `q = x·exp(x) = x·t`, verified
to *actually solve* `Dq + b·q = c` by the cleared difference over ℚ(x)[t] (`native_decide`); the
dispatcher `cPolyRischDE` routes the same input to the hyperexponential cancellation solver. -/
abbrev ex_6_6_cancelExp := @rischDE_cancelExp_example

/-- **Example (§6.6 eq. 6.23)**, general non-constant base recursion: `cRischDE` on
`Dy + (1/x)y = 2·log(x) + 1` (`t = log x`) drives the primitive cancellation case through the
non-constant base RDE `RischDE(1/x, 2) = x` over ℚ(x) to `y = x·log(x)`, verified by the cleared
identity (`native_decide`). -/
abbrev ex_6_6_baseRecursion := @rischDE_baseRecursion_example

/-- **Example (§6.6 eq. 6.23)**, standalone rational base solve: `cRationalRDE` on `Ds + (1/x)s = 2`
returns `s = x` (the whole Ch. 6 pipeline at the base level over ℚ), verified to actually solve the
equation by the cleared quotient-rule identity (`native_decide`). -/
abbrev ex_6_6_rationalRDE := @rischDE_rationalRDE_example

end DeepWiki.Si
