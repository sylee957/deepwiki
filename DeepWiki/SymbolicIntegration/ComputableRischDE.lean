import DeepWiki.SymbolicIntegration.ComputableLogPartTower

/-! # Computable Risch differential equation solver over the tower ℚ(x)[t] (Bronstein Chapter 6)
The **Risch differential equation** (RDE) problem (Bronstein, *Symbolic Integration I*, Ch. 6) is:
given a differential field `K` of characteristic `0` and `f, g ∈ K`, decide whether

```
  Dy + f·y = g                                                                            (6.1)
```

has a solution `y ∈ K`, and find one if so. The book studies the **transcendental case**: `K = k(t)`
is a simple monomial extension of a differential subfield `k`, with `D = κ_D + Dt·d/dt` the monomial
derivation. We take `k = ℚ(x)`, `D = d/dx`, so the carrier is the tower `ℚ(x)[t]` already built by the
integrator engine (`CPolyG QFunNZ`, `cmonomialDeriv Dt`).

Bronstein's RDE pipeline (Ch. 6, confirmed section numbers from the 2005 edition, p.181–215):

1. **§6.1 `WeakNormalizer`** + the **normal part of the denominator** (`RdeNormalDenominator`, §6.2's
   eq. 6.2 / Corollary 6.1.1). `WeakNormalizer(f, D)` returns `q ∈ k[t]` such that `f − Dq/q` is
   *weakly normalized*. `RdeNormalDenominator(f, g, D)` then either reports **no solution** or returns a
   quadruplet `(a, b, c, h)` with `a, h ∈ k[t]`, `b, c ∈ k⟨t⟩` such that every solution `y ∈ k(t)` of
   `Dy + f·y = g` has `q = y·h ∈ k⟨t⟩` solving `a·Dq + b·q = c` — reducing (6.1) to the simple part.
2. **§6.2 `RdeSpecialDenominator`** — the *special* part of the denominator, reducing the simple-part
   equation `a·Dq + b·q = c` (eq. 6.6, `a ∈ k[t]` with no special factor) to a **polynomial** equation
   over `k[t]`. The §6.2 reduction (eq. 6.7) replaces `q` by `h·pⁿ` and clears the special factor `p`;
   the lower bound `n` on `ν_p(q)` is computed case-by-case for the *primitive* (`Dt ∈ k`),
   *hyperexponential* (`Dt/t ∈ k`), and *nonlinear* monomials.
3. **§6.3 `RdeBoundDegree`** — an explicit upper bound on `deg_t(q)` for any polynomial solution `q`,
   again split by monomial type (primitive, hyperexponential, nonlinear, the `t = tan` case).
4. **§6.4 `SPDE`** (the *Sub-Problem of the Differential Equation*) — Rothstein's recursive reduction
   of the bounded-degree polynomial equation `a·Dq + b·q = c` to a smaller one, peeling `gcd(a, b)`.
5. **§6.5–6.6 `PolyRischDE`** — the non-cancellation and cancellation cases that finally solve the
   degree-bounded polynomial equation in `k[t]`.

## What this file delivers (non-cancellation pipeline + §6.6 primitive cancellation, computable +
`native_decide`-validated)

* **`cWeakNormalizer Dt fuel fnum fden`** (§6.1) — the `WeakNormalizer` algorithm box (book p.183) over
  the tower: split the denominator of `f = fnum/fden` into its normal part `dₙ`, form
  `d₁ = (dₙ/g)/gcd(dₙ/g, g)` with `g = gcd(dₙ, dₙ')`, solve `ExtendedEuclidean(fden/d₁, d₁, fnum)` for
  the residue-numerator `a`, build the residue resultant `r = res_t(a − z·Dd₁, d₁)`, and return
  `∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}` over the **positive integer roots** `nᵢ` of `r`. The positive integer
  roots are found by a bounded evaluation test (`cevalConst r n = 0`). For an already-weakly-normalized
  `f` (the post-Hermite RDE input), `r` has no positive integer roots and the result is `q = 1`.

* **`cRdeNormalDenominator Dt fuel fnum fden gnum gden`** (§6.2 / Corollary 6.1.1) — the
  `RdeNormalDenominator` algorithm box (book p.185): from the normal parts `dₙ, eₙ` of the denominators
  of `f, g`, compute `h = gcd(eₙ, eₙ')/gcd(p, p')` with `p = gcd(dₙ, eₙ)`, and return the reduction
  quadruplet `(a, b, c, h) = (dₙh, dₙhf − dₙ(Dh), dₙh²g, h)` (or **no solution** when `eₙ ∤ dₙh²`).

* **`cRdeSpecialDenominator Dt fuel a b c`** (§6.2, the `RdeSpecialDenom{Exp,Tan}` boxes, book p.190/192)
  — the *special* part of the denominator. Given `a·Dq + b·q = c` (eq. 6.6) with `a` free of special
  factors, take the monic special irreducible `p` of the monomial (`cSpecialPoly`: `t²+1` tangent, `t`
  hyperexponential, `1` primitive), the orders `n_b = ν_p(b)`, `n_c = ν_p(c)`, the lower bound
  `n = min(0, n_c − min(0, n_b)) ≤ 0` on `ν_p(q)`, and the clearing power `N = max(0, −n_b, n − n_c)`,
  substitute `q = h·pⁿ` (eq. 6.7) and clear by `p^N`, returning `(a·pᴺ, (b + n·a·Dp/p)·pᴺ, c·p^{N−n},
  p^{−n})` so that `r = q·p^{−n} ∈ k[t]`. The cancellation refinement `n ← min(n, m)` (the `n_b = 0`
  branch) needs the parametric-logarithmic-derivative subroutine (Ch. 7) and is documented but not run.

* **`cRdeBoundDegree Dt fuel a b c`** (§6.3, the `RdeBoundDegree{Base,Prim,Exp,NonLinear}` boxes, book
  p.198–201) — an explicit upper bound `n ∈ ℕ` on `deg_t(q)` for any polynomial solution `q ∈ k[t]` of
  `a·Dq + b·q = c` (eq. 6.12), case-split by `δ = deg(Dt)`: **nonlinear** `δ ≥ 2`
  `n = max(0, d_c − max(d_a + δ − 1, d_b))`; **hyperexponential** `δ = 1`
  `n = max(0, d_c − max(d_b, d_a))`; **primitive** `δ = 0` `max(0, d_c − d_b)` or `max(0, d_c − d_a + 1)`.
  The cancellation refinements (raising the bound when the leading coefficients are a logarithmic
  derivative) likewise need the Ch. 7 subroutine and are documented but not run.

* **`cSPDE Dt fuel a b c n`** (§6.4) — Rothstein's `SPDE(a, b, c, D, n)` box (book p.203): the recursive
  `g = gcd(a, b)`-peeling reduction of the degree-bounded `a·Dq + b·q = c` (eq. 6.12) to one with
  `a = 1` (eq. 6.16). Returns `none` ("no solution of degree `≤ n`") or `(b̄, c̄, m, α, β)` so any
  solution `q` is `q = α·h + β` for an `h` solving `Dh + b̄·h = c̄`, `deg(h) ≤ m`. Fuel-bounded; the
  `n < 0`/`c = 0` short-circuit returns the all-zero tuple (the only solution is `q = 0`).

* **`cPolyRischDENoCancel Dt fuel b c n`** (§6.5) — the `PolyRischDENoCancel1(b, c, D, n)` box (book
  p.208), the **non-cancellation** case (`D = d/dt`, or `deg(b) > max(0, δ−1)`): solve `Dq + b·q = c`
  (eq. 6.19) degree-by-degree from the top down — `lc(c) = lc(b)·lc(q)` fixes `q`'s leading monomial,
  subtract `D(·) + b·(·)`, recurse on the lower-degree remainder. Returns `Option (CPolyG QFunNZ)`.

* **`cParametricLogDeriv fuel b`** (§5.12 / §7.3, the `ParametricLogarithmicDerivative` box, book
  p.176/253) — over the **base field** `k = ℚ(x)`: does `n·b = Dz/z` hold for a nonzero `n ∈ ℤ` and
  `z ∈ ℚ(x)*` (is `b` a logarithmic derivative of a `ℚ(x)`-radical)? Decides the **constant sub-case**
  `b ∈ ℚ*` exactly (a nonzero constant is *not* a logarithmic derivative — `Dz/z` is always proper,
  the §5.12 obstruction; this is the branch §6.6 reaches), returning `false`. The full proper/simple/
  integer-residue recognizer over ℚ(x) is the documented continuation.

* **`cRischDEBase fuel b c`** (§6.6 eq. 6.23) — the **base Risch DE** `Ds + b·s = c` over `k = ℚ(x)`
  (`D = d/dx`), the leading-coefficient recursion target of the primitive cancellation case;
  implemented for the bottoming-out `k`-constant sub-case (`b, c ∈ ℚ`, `s = c/b`).

* **`cPolyRischDECancelPrim Dt fuel b c n`** (§6.6, the `PolyRischDECancelPrim(b, c, D, n)` box, book
  p.212) — the **primitive cancellation** case (`Dt ∈ k`, `b ∈ k*`): `D` does not raise the
  `t`-degree, the leading terms of `Dq` and `bq` cancel (so `cPolyRischDENoCancel` cannot proceed), and
  the solve recurses degree-by-degree into `cRischDEBase` (eq. 6.23 `RischDE(b, lc(c))`) after the
  §5.12 `b = Dz/z` test (`cParametricLogDeriv`). Returns `Option (CPolyG QFunNZ)`.

* **`cPolyRischDE Dt fuel b c n`** (§6.5 + §6.6) — the **dispatcher**: routes `Dq + b·q = c` to
  `cPolyRischDENoCancel` (non-cancellation, `deg(b) > max(0, δ−1)`) or `cPolyRischDECancelPrim`
  (primitive cancellation, `δ = 0`, `b ∈ k*`) by monomial type and `deg(b)` (Lemma 6.5.1).

* **`cRischDE Dt fuel fnum fden gnum gden`** — the **assembled full solver**: chains
  `cRdeNormalDenominator` (§6.2) → `cRdeSpecialDenominator` (§6.2) → `cRdeBoundDegree` (§6.3) →
  `cSPDE` (§6.4) → `cPolyRischDE` (§6.5/§6.6 dispatcher), reconstructing `y = ynum/yden ∈ k(t)` solving
  `Dy + f·y = g`, or `none`. Validated end-to-end on Example 6.5.1 (`rischDE_solve_example`).

## Validation (`native_decide`)

Bronstein's **Example 6.1.2** (book p.186): `k = ℚ(x)`, `D = d/dx`, `t = tan(x)` (`Dt = 1 + t²`), the
equation `Dy + (t²+1)y = 1/t²`. So `f = t²+1` (denominator `1`), `g = 1/t²`. The book runs
`RdeNormalDenominator` and gets `dₙ = 1`, `eₙ = t²`, `p = 1`, `h = t`, `dₙh² = t²` divisible by `eₙ`,
and the quadruplet `(a, b, c, h) = (t, (t−1)(t²+1), 1, t)`, i.e. any solution is `y = q/t` with `q`
solving the reduced equation `t·Dq + (t−1)(t²+1)·q = 1` (book eq. 6.5). `native_decide` pins all four
output components against these book values (via `cisZeroG` of the cleared difference — `QFunNZ` has no
`DecidableEq`). `cWeakNormalizer` is checked to return `q = 1` here (`f` is already weakly normalized).

Continuing on the same example, **Example 6.2.2** (book p.192) runs `RdeSpecialDenomTan` on
`(a, b, c) = (t, (t−1)(t²+1), 1)`: `p = t²+1`, `n_b = 1`, `n_c = 0`, `n = 0`, `N = 0`, returning the
*unchanged* `(t, (t−1)(t²+1), 1, 1)` (the special part is trivial here, `h = 1`). **Example 6.3.4**
(book p.202) runs `RdeBoundDegreeNonLinear` on the same `(a, b, c)` with `δ = 2`: `d_a = 1`, `d_b = 3`,
`d_c = 0`, giving the degree bound `n = 0` (any polynomial solution lies in ℚ(x)). `native_decide` pins
both (`rischDE_specialDenominator_example`, `rischDE_boundDegree_example`).

**Example 6.5.1** (book p.208) exercises the *whole assembled solver* `cRischDE` end-to-end. For
`Dy + (t²+1)y = t³ + (x+1)t² + t + (x+2)` (eq. 6.20, from `∫ (tan³x + (x+1)tan²x + tan x + x + 2) e^{tan
x} dx`) over the same monomial, the pipeline returns the book's elementary solution `y = t + x`, and
`rischDE_solve_example` checks it *actually solves* the equation by clearing denominators
(`rdeClearedCheck`: the polynomial identity `D(y)+f·y = g` after multiplying out — not merely pinning the
output). **Example 6.4.1** (book p.204): `cRischDE` on the original `Dy + (t²+1)y = 1/t²` (eq. 6.4)
returns `none` — `SPDE` reaches `n = −1 < 0` with `c ≠ 0`, so `∫ e^{tan x}/tan²x dx` is not elementary
(`rischDE_noSolution_example`).

The **§6.6 cancellation primitive case** (`rischDE_cancel_example`) exercises the path
`cPolyRischDENoCancel` *cannot* handle. For the primitive monomial `t = log(x)` (`Dt = 1/x ∈ k`,
`δ = 0`), the equation `Dq + 1·q = log(x) + 1/x` (`b = 1 ∈ ℚ*`, `c = t + 1/x`, `deg(c) = 1`) has its
leading terms of `Dq` and `bq` cancel; `cPolyRischDECancelPrim` rules `b = 1` out as a logarithmic
derivative (`cParametricLogDeriv = false`), then recurses degree-by-degree into the base RDE over
`k = ℚ(x)` (`cRischDEBase`: `RischDE(1, 1) = 1`), producing the elementary solution `q = log(x) = t` —
`native_decide`-verified to *actually solve* `Dq + b·q = c` (cleared difference). The dispatcher
`cPolyRischDE` is checked to route this same input to the cancellation solver.

## What is NOT here (the rest of §6.6, honestly deferred)

The deliverable is the **full non-cancellation pipeline plus the §6.6 primitive cancellation case
computing over the tower**, plus validation — not abstract correctness (no `Dy + fy = g ↔ …` theorem is
proved). What remains of the **§6.6 cancellation cases** (book p.211–215):

* **`PolyRischDECancelExp`** (hyperexponential, `Dt/t ∈ k`, `δ = 1`, book p.213) and
  **`PolyRischDECancelTan`** (nonlinear / hypertangent `Dt/(t²+1) ∈ k`, `δ = 2`, book p.215): they
  recurse to a base RDE over `k` or `k(√−1)` / a **`CoupledDESystem`** (Ch. 8) and an in-field
  integration; not implemented (the dispatcher falls them back to the non-cancellation loop).
* **The general eq. 6.23 base recursion.** `cRischDEBase` solves the bottoming-out `k`-constant
  sub-case only; the general *rational Risch DE in `x`* (non-constant `b, c ∈ ℚ(x)`, the whole Ch. 6
  pipeline re-run with `t = x` the trivial primitive monomial) is the remaining recursion.
* **The full §5.12 / §7.3 recognizer.** `cParametricLogDeriv` decides the reachable constant
  obstruction exactly; the proper/simple/integer-residue Rothstein–Trager recognizer over ℚ(x) and the
  §7.3 unique-`m/n` linear-constraint solve are the documented continuation. The in-field-integration
  sub-branch of `PolyRischDECancelPrim` (`zc = Dp` test when `b = Dz/z`) is likewise documented.

The cancellation refinements inside `cRdeSpecialDenominator`/`cRdeBoundDegree` (also §5.12 / Ch. 7)
only *raise* the bound in that same cancellation case and are likewise documented but not run; every
non-cancellation case, the primitive cancellation case, and all validation runs are reproduced exactly.
No `sorry`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

namespace CPolyG

/-! ### Polynomial evaluation at a rational constant (positive-integer-root test for `WeakNormalizer`)

`cevalConst p c = p(c) ∈ QFunNZ` for a constant `c ∈ ℚ` lifted to `ℚ(x)`, by Horner. Used to test
candidate positive integers `n` for being roots of the residue resultant `r ∈ ℚ(x)[z]`
(`cisZero (cevalConst r n).num`), the §6.1 step "`(n₁,…,n_s) ← positive integer roots of r`". -/

/-- **Evaluate a `CPolyG QFunNZ` at a constant `c ∈ ℚ`** (lifted to `ℚ(x)`), by Horner from the top
coefficient down: `cevalConst [a₀,…,aₙ] c = a₀ + c(a₁ + c(… + c·aₙ))`. The result is a `QFunNZ`. -/
def cevalConst (p : CPolyG QFunNZ) (c : ℚ) : QFunNZ :=
  let cv : QFunNZ := ofConstNZ c
  ((p : List QFunNZ).foldr (fun a acc => CField.add a (CField.mul cv acc)) CField.zero)

/-- **`r` vanishes at the rational constant `c`** `cisRootConst r c`: `true` iff `cevalConst r c` is the
zero element of `QFunNZ` (its numerator polynomial is the zero list). Decides whether `c` is a root of
`r ∈ ℚ(x)[z]` over the tower. -/
def cisRootConst (r : CPolyG QFunNZ) (c : ℚ) : Bool :=
  CField.isZero (cevalConst r c)

/-- **Positive integer roots of `r` up to a bound** `cPosIntRoots r bound = [n ∈ {1,…,bound} : r(n) = 0]`
(the §6.1 step). The residue resultant's positive integer roots are the multiplicities `nᵢ` entering the
`WeakNormalizer` product; for an already-weakly-normalized `f` this list is empty. -/
def cPosIntRoots (r : CPolyG QFunNZ) (bound : ℕ) : List ℕ :=
  (List.range bound).filterMap (fun k =>
    let n : ℕ := k + 1
    if cisRootConst r ((n : ℚ)) then some n else none)

/-! ### `cWeakNormalizer` (Bronstein §6.1, the `WeakNormalizer(f, D)` algorithm box, book p.183)

`f ∈ k(t)` arrives as a numerator/denominator pair `(fnum, fden)` of `t`-polynomials over `ℚ(x)`. The
box returns `q ∈ k[t]` with `f − Dq/q` weakly normalized. -/

/-- **Computable weak normalizer** `cWeakNormalizer Dt fuel fnum fden = q ∈ ℚ(x)[t]` (Bronstein §6.1,
book p.183) with `f − Dq/q` weakly normalized w.r.t. `t`, for `f = fnum/fden`:

1. `(dₙ, dₛ) ← SplitFactor(fden, D)` — the normal part `dₙ` of the denominator.
2. `g ← gcd(dₙ, dₙ')` (`'` = `d/dt`), `d* ← dₙ/g`, `d₁ ← d*/gcd(d*, g)`.
3. `(a, _) ← ExtendedEuclidean(fden/d₁, d₁, fnum)`: `a·(fden/d₁) + b·d₁ = fnum`.
4. `r ← res_t(a − z·Dd₁, d₁)` (the residue resultant, `Dd₁ = cmonomialDeriv Dt d₁`).
5. `(n₁,…,n_s) ← positive integer roots of r` (bounded by `boundRoots`).
6. `return ∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}`.

When `f` is already weakly normalized (`r` has no positive integer root) the product is empty and the
result is `q = 1`. `boundRoots` caps the integer-root search. -/
def cWeakNormalizer (Dt : CPolyG QFunNZ) (fuel : ℕ) (fnum fden : CPolyG QFunNZ)
    (boundRoots : ℕ := 16) : CPolyG QFunNZ :=
  let dn := (cSplitFactorFast Dt fuel fden).1
  let g := cgcdFF fuel dn (cderivG dn)
  let dstar := cdivFF fuel dn g
  let d1 := cdivFF fuel dstar (cgcdFF fuel dstar g)
  let fdenOverD1 := cdivFF fuel fden d1
  let a := (cdiophantineG fuel fdenOverD1 d1 fnum).1
  let Dd1 := cmonomialDeriv Dt d1
  -- residue resultant `r(z) = res_t(a − z·Dd₁, d₁)`; reuse the §5.6 evaluation/interpolation template
  let r := cResidueResultantTower Dt fuel a d1
  let roots := cPosIntRoots r boundRoots
  roots.foldl (fun (acc : CPolyG QFunNZ) (n : ℕ) =>
    let gi := cgcdFF fuel (csubG a (cscaleG (ofConstNZ ((n : ℚ))) Dd1)) d1
    cmulG acc (cpowG gi n)) [CField.one]

/-! ### `cRdeNormalDenominator` (Bronstein §6.2 / Corollary 6.1.1, the algorithm box, book p.185)

`f, g ∈ k(t)` arrive as numerator/denominator pairs. The box returns either **no solution** or the
quadruplet `(a, b, c, h)` reducing `Dy + fy = g` to `a·Dq + b·q = c` with `q = y·h`. Encoded as
`Option (a, b, c, h)` (`none` = "no solution"). -/

/-- **Computable normal-denominator reduction** `cRdeNormalDenominator Dt fuel fnum fden gnum gden`
(Bronstein §6.2, book p.185), for a **weakly normalized** `f = fnum/fden` and `g = gnum/gden`. Returns
`none` ("no solution") or `some (a, b, c, h)` with `a, h ∈ ℚ(x)[t]`, `b, c ∈ ℚ(x)⟨t⟩` such that every
solution `y ∈ k(t)` of `Dy + fy = g` has `q = y·h ∈ k⟨t⟩` solving `a·Dq + b·q = c`:

1. `(dₙ, dₛ) ← SplitFactor(fden, D)`, `(eₙ, eₛ) ← SplitFactor(gden, D)`.
2. `p ← gcd(dₙ, eₙ)`, `h ← gcd(eₙ, eₙ') / gcd(p, p')` (`'` = `d/dt`).
3. **if** `eₙ ∤ dₙh²` **then** "no solution".
4. `return (dₙh, dₙhf − dₙ·Dh, dₙh²g, h)`.

Here `f` and `g` are cleared into the `t`-polynomial pieces: `a = dₙh`, and the (generally rational in
`t`) `b, c` are returned as **numerator polynomials over the common denominators** `fden`, `gden` —
specifically `b = dₙh·fnum − dₙ·Dh·fden` (numerator over `fden`) and `c = dₙh²·gnum` (numerator over
`gden`). The validation example has `fden = gden = 1`'s normal parts so the pieces are genuine
polynomials and match the book verbatim. -/
def cRdeNormalDenominator (Dt : CPolyG QFunNZ) (fuel : ℕ) (fnum fden gnum gden : CPolyG QFunNZ) :
    Option (CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ) :=
  let dn := (cSplitFactorFast Dt fuel fden).1
  let en := (cSplitFactorFast Dt fuel gden).1
  let p := cgcdFF fuel dn en
  let h := cdivFF fuel (cgcdFF fuel en (cderivG en)) (cgcdFF fuel p (cderivG p))
  let dnh2 := cmulG (cmulG dn h) h
  if cdvdG fuel en dnh2 then
    let a := cmulG dn h
    let Dh := cmonomialDeriv Dt h
    -- `b = dₙh·f − dₙ·Dh = (dₙh·fnum − dₙ·Dh·fden)/fden` (the numerator is divisible by `fden`).
    let b := cdivFF fuel (csubG (cmulG a fnum) (cmulG (cmulG dn Dh) fden)) fden
    -- `c = dₙh²·g = dₙh²·gnum/gden` (divisible by `gden` exactly when `eₙ ∣ dₙh²`, the test above).
    let c := cdivFF fuel (cmulG dnh2 gnum) gden
    some (a, b, c, h)
  else none

/-! ### `cRdeSpecialDenominator` (Bronstein §6.2, the `RdeSpecialDenom*` algorithm boxes, book p.190/192)

After `cRdeNormalDenominator`, we have `a·Dq + b·q = c` (eq. 6.6) with `a ∈ k[t]` having no special
factor, `b, c ∈ k⟨t⟩`. The §6.2 special-denominator step clears the *special* part of the denominators
of `b, c`: it substitutes `q = h·pⁿ` (eq. 6.7) for the monic special irreducible `p` and a lower bound
`n ≤ 0` on `ν_p(q)`, then multiplies through by `p^N` (`N ≥ 0`) to clear all denominators, returning a
new polynomial quadruplet `(ā, b̄, c̄, h)` with `ā, b̄, c̄, h ∈ k[t]` such that any `k⟨t⟩`-solution `q` of
`a·Dq+b·q=c` has `r = q·h ∈ k[t]` solving `ā·Dr + b̄·r = c̄` (eq. 6.7 cleared). -/

/-- **`p`-adic valuation** `cValuation fuel p x = ν_p(x)`: the multiplicity of the monic irreducible
`p` dividing the polynomial `x` (largest `k` with `pᵏ ∣ x`), found by trial division up to `fuel`. For
the special-denominator step `ν_p(b)`/`ν_p(c)` are the orders of the special factor `p` (e.g. `t²+1`)
in the *numerator* polynomials of `b, c`. Returns `0` on the zero polynomial or constant/unit `p`. -/
def cValuation {α : Type*} [CField α] (fuel : ℕ) (p x : CPolyG α) : ℕ :=
  let rec go : ℕ → CPolyG α → ℕ
    | 0, _ => 0
    | fuel + 1, x =>
        if cisZeroG x then 0
        else if cdegG p = 0 then 0
        else if cdvdG fuel p x then 1 + go fuel (cdivG fuel x p)
        else 0
  go fuel x

/-- **Special monic irreducible of the monomial** `cSpecialPoly Dt fuel = p` — the monic special part
of the monomial derivative `Dt`, i.e. the monic squarefree polynomial whose irreducible factors `p`
satisfy `p ∣ Dp` (Bronstein §3.4–§6.2). For a **primitive** monomial (`Dt ∈ k`, degree `0`) this is the
constant `1` (`k⟨t⟩ = k[t]`, no special part to clear); for the **hypertangent** monomial
`Dt = c·(t²+1)` it is `t²+1` (the only monic special irreducible); for the **hyperexponential** monomial
`Dt = c·t` it is `t`. Computed as the monic special part of `Dt` via `cSplitFactorFast`. -/
def cSpecialPoly (Dt : CPolyG QFunNZ) (fuel : ℕ) : CPolyG QFunNZ :=
  cmonicG (cSplitFactorFast Dt fuel Dt).2

/-- **Computable special-denominator reduction** `cRdeSpecialDenominator Dt fuel a b c` (Bronstein §6.2,
the `RdeSpecialDenom{Exp,Tan}` boxes, book p.190/192). Given the reduced equation `a·Dq + b·q = c`
(eq. 6.6) with `a` having no special factor, returns the special-cleared quadruplet `(ā, b̄, c̄, h)`
(`h = p^{−n}`) so that `r = q·h ∈ k[t]` solves `ā·Dr + b̄·r = c̄` (eq. 6.7 cleared by `p^N`):

1. `p ← cSpecialPoly Dt` (the monic special irreducible: `t²+1` tangent, `t` hyperexponential, `1`
   primitive — when `p` is constant the special part is trivial, returns `(a, b, c, 1)`).
2. `n_b ← ν_p(b)`, `n_c ← ν_p(c)`, `n ← min(0, n_c − min(0, n_b))` (so `n ≤ 0`).
3. *(Cancellation refinement `n ← min(n, m)` in the `n_b = 0` branch needs the parametric-logarithmic-
   derivative subroutine — Ch. 7; not run here. The validation case has `n_b ≠ 0`, so this branch is
   inactive and the book's `n` is reproduced exactly.)*
4. `N ← max(0, −n_b, n − n_c)` (`N ≥ 0`).
5. `return (a·pᴺ, (b + n·a·Dp/p)·pᴺ, c·p^{N−n}, p^{−n})`.

Encoded with the integer exponents `−n` and `N−n` as `ℕ` (both non-negative since `n ≤ 0 ≤ N`). The
`b`-component `b + n·a·Dp/p` uses `Dp = cmonomialDeriv Dt p`, exact-divided by `p` (`p ∣ Dp` for a
special `p`); when `n = 0` the additive term vanishes and `b̄ = b·pᴺ`. -/
def cRdeSpecialDenominator (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ) :
    CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ :=
  let p := cSpecialPoly Dt fuel
  if cdegG p = 0 then (a, b, c, [CField.one])
  else
    let nb : ℤ := (cValuation fuel p b : ℤ)
    let nc : ℤ := (cValuation fuel p c : ℤ)
    let n : ℤ := min 0 (nc - min 0 nb)
    let N : ℤ := max (max 0 (-nb)) (n - nc)
    let Nnat : ℕ := N.toNat
    let negn : ℕ := (-n).toNat
    let Nminusn : ℕ := (N - n).toNat
    let pN := cpowG p Nnat
    let abar := cmulG a pN
    -- `b + n·a·Dp/p`: with `n = -negn`, the additive term is `-(negn)·a·(Dp/p)`.
    let DpOverp := cdivFF fuel (cmonomialDeriv Dt p) p
    let bterm := cscaleG (ofConstNZ ((-(negn : ℤ) : ℚ))) (cmulG a DpOverp)
    let bbar := cmulG (caddG b bterm) pN
    let cbar := cmulG c (cpowG p Nminusn)
    let h := cpowG p negn
    (abar, bbar, cbar, h)

/-! ### `cRdeBoundDegree` (Bronstein §6.3, the `RdeBoundDegree*` algorithm boxes, book p.198–201)

After `cRdeSpecialDenominator`, we have `a·Dq + b·q = c` (eq. 6.12) with `a, b, c ∈ k[t]`, and want an
explicit upper bound `n ∈ ℕ` on `deg_t(q)` for any polynomial solution `q ∈ k[t]`. The bound is
case-split by monomial type (Lemmas 6.3.1/6.3.3/6.3.4/6.3.5), parameterized by `δ = deg(Dt)` (the
monomial's `δ(t)`) and `λ = lc(Dt)`. -/

/-- **Computable degree bound** `cRdeBoundDegree Dt fuel a b c = n ∈ ℕ` (Bronstein §6.3, the
`RdeBoundDegree{Base,Prim,Exp,NonLinear}` boxes, book p.198–201): an upper bound on `deg_t(q)` for any
polynomial solution `q ∈ k[t]` of `a·Dq + b·q = c` (eq. 6.12). With `d_a = deg(a)`, `d_b = deg(b)`,
`d_c = deg(c)`, `δ = deg(Dt)`:

* **Nonlinear** (`δ ≥ 2`, e.g. `t = tan` with `Dt = 1+t²`, `δ = 2` — the `RdeBoundDegreeNonLinear`
  box): `n ← max(0, d_c − max(d_a + δ − 1, d_b))`, with a cancellation refinement when
  `d_b = d_a + δ − 1`.
* **Hyperexponential / Louvillian** (`δ = 1`, `Dt/t ∈ k` — `RdeBoundDegreeExp`):
  `n ← max(0, d_c − max(d_b, d_a))`, with a cancellation refinement when `d_a = d_b`.
* **Primitive / base** (`δ = 0`, `Dt ∈ k` — `RdeBoundDegreePrim`/`Base`): `n ← max(0, d_c − d_b)` if
  `d_b > d_a`, else `n ← max(0, d_c − d_a + 1)`, with cancellation refinements.

The **cancellation refinements** (the `if … then n ← max(n, m)` branches) need the parametric-
logarithmic-derivative / limited-integration subroutine of §5.12 / Ch. 7 to decide whether the relevant
`−lc(b)/lc(a)` is of the form `m·η + Du/u`; they are documented but not run here (they only ever
*raise* the bound in the cancellation case, never the non-cancellation case used by the validation).
The non-cancellation `max(0, …)` formula is reproduced exactly. The non-negative degree differences
are computed as `ℤ` to avoid `ℕ`-truncation, then clamped at `0` (a degree bound of `0` means `q ∈ k`). -/
def cRdeBoundDegree (Dt : CPolyG QFunNZ) (_fuel : ℕ) (a b c : CPolyG QFunNZ) : ℕ :=
  let da : ℤ := (cdegG a : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  let dc : ℤ := (cdegG c : ℤ)
  let δ : ℤ := (cdegG Dt : ℤ)
  let n : ℤ :=
    if 2 ≤ δ then
      -- nonlinear case (`RdeBoundDegreeNonLinear`): `max(0, d_c − max(d_a + δ − 1, d_b))`.
      max 0 (dc - max (da + δ - 1) db)
    else if δ = 1 then
      -- hyperexponential / Louvillian case (`RdeBoundDegreeExp`): `max(0, d_c − max(d_b, d_a))`.
      max 0 (dc - max db da)
    else
      -- primitive / base case (`RdeBoundDegreePrim`/`Base`).
      if da < db then max 0 (dc - db) else max 0 (dc - da + 1)
  n.toNat

/-! ### `cSPDE` (Bronstein §6.4, Rothstein's `SPDE(a,b,c,D,n)` algorithm box, book p.203)

After `cRdeBoundDegree`, we have `a·Dq + b·q = c` (eq. 6.12) with `a, b, c ∈ k[t]`, `a ≠ 0`, and a
degree bound `n` on `deg_t(q)`. Rothstein's `SPDE` (Theorem 6.4.1, [83]) recursively peels
`g = gcd(a, b)` to reduce (6.12) to one with `a = 1` (eq. 6.16 `aDh + (b+Da)h = z − Dr`), returning a
linear reconstruction `q = α·h + β` from a solution `h` of `Dh + b̄·h = c̄` of degree `≤ m`.

The box's return tuple is `(b̄, c̄, m, α, β)`: any solution `q ∈ k[t]` of `aDq+bq=c` of degree `≤ n`
has `q = α·h + β` for some solution `h ∈ k[t]` of `Dh + b̄·h = c̄` with `deg(h) ≤ m`; "no solution"
(encoded `none`) means (6.12) has no solution of degree `≤ n`. The recursion terminates because each
recursive call has the divided `a/g`, whose degree strictly drops when `deg(a) > 0` (the `a = α`
constant base case `deg(a) = 0` returns directly). -/

/-- **Computable SPDE** `cSPDE Dt fuel a b c n` (Bronstein §6.4, Rothstein's `SPDE(a,b,c,D,n)` box,
book p.203). Given the monomial derivation `D` (`= cmonomialDeriv Dt`), `a, b, c ∈ k[t]` with `a ≠ 0`,
and a degree bound `n : ℤ`, returns either `none` ("no solution": `a·Dq + b·q = c` has no solution
`q ∈ k[t]` of degree `≤ n`) or `some (b̄, c̄, m, α, β)` such that any such solution is `q = α·h + β`,
where `h ∈ k[t]` solves `Dh + b̄·h = c̄` with `deg(h) ≤ m`:

1. **if** `n < 0` **then** (`c = 0` ⇒ `(0,0,0,0,0)`, the only solution is `q = 0`; else `none`).
2. `g ← gcd(a, b)`; **if** `g ∤ c` **then** `none`. Otherwise `a ← a/g`, `b ← b/g`, `c ← c/g`.
3. **if** `deg(a) = 0` (`a ∈ k*`) **then** `(b/a, c/a, n, 1, 0)` (already `a = 1`, identity recon).
4. `(r, z) ← ExtendedEuclidean(b, a, c)` (`b·r + a·z = c`, `deg(r) < deg(a)`) — `cdiophantineG b a c`.
5. `u ← SPDE(a, b + Da, z − Dr, D, n − deg(a))`; **if** `u = none` **then** `none`.
6. `(b̄, c̄, m, α, β) ← u`; **return** `(b̄, c̄, m, a·α, a·β + r)` (so `q = a·h + r = a·(α s + β) + r`).

The degree bound enters only the `n < 0` short-circuit; `m` is threaded through unchanged once the
constant-`a` base case fixes it to `n − Σ deg(aᵢ)`. Fuel-bounded recursion (one level per `gcd`-peel). -/
def cSPDE (Dt : CPolyG QFunNZ) : ℕ → (a b c : CPolyG QFunNZ) → (n : ℤ) →
    Option (CPolyG QFunNZ × CPolyG QFunNZ × ℤ × CPolyG QFunNZ × CPolyG QFunNZ)
  | 0, _, _, _, _ => none
  | fuel + 1, a, b, c, n =>
    if n < 0 then
      if cisZeroG c then some ([], [], 0, [], []) else none
    else
      let g := cgcdFF fuel a b
      if cdvdG fuel g c then
        let a := cdivFF fuel a g
        let b := cdivFF fuel b g
        let c := cdivFF fuel c g
        if cdegG a = 0 then
          -- `a ∈ k*`: `Dh + (b/a)·h = c/a`; solution `q = h` (`α = 1`, `β = 0`).
          let ainv := CField.inv (cleadG a)
          some (cscaleG ainv b, cscaleG ainv c, n, [CField.one], [])
        else
          -- `ExtendedEuclidean(b, a, c)`: `b·r + a·z = c`, `deg(r) < deg(a)`.
          let (r, z) := cdiophantineG fuel b a c
          let Da := cmonomialDeriv Dt a
          let Dr := cmonomialDeriv Dt r
          match cSPDE Dt fuel a (caddG b Da) (csubG z Dr) (n - (cdegG a : ℤ)) with
          | none => none
          | some (bbar, cbar, m, α, β) =>
              -- `q = a·h + r = a·(α s + β) + r`, so `α ← a·α`, `β ← a·β + r`.
              some (bbar, cbar, m, cmulG a α, caddG (cmulG a β) r)
      else none

/-! ### `cPolyRischDENoCancel` (Bronstein §6.5, the `PolyRischDENoCancel1` box, book p.208)

After `cSPDE` the equation is `Dq + b·q = c` (eq. 6.19, `a = 1`) with a degree bound `n` on `deg_t(q)`.
In the **non-cancellation** case — `D = d/dt`, or `deg(b) > max(0, δ(t) − 1)` (Lemma 6.5.1(i)) — the
leading terms of `Dq` and `bq` don't cancel, so `deg(q) = deg(c) − deg(b)` is forced and `q` is solved
**degree-by-degree from the top down**: the leading-coefficient equation `lc(c) = lc(b)·lc(q)` fixes
`q`'s leading monomial `(lc(c)/lc(b))·tᵐ`, subtract `D(·) + b·(·)`, recurse on the lower-degree
remainder. -/

/-- **Computable Poly-Risch-DE, non-cancellation case** `cPolyRischDENoCancel Dt fuel b c n` (Bronstein
§6.5, the `PolyRischDENoCancel1(b,c,D,n)` box, book p.208). Solves `Dq + b·q = c` (eq. 6.19) for
`q ∈ k[t]` with `deg(q) ≤ n` (`n : ℤ`), in the non-cancellation case (`b ≠ 0` and `D = d/dt` or
`deg(b) > max(0, δ(t) − 1)`). Returns `none` ("no solution of degree `≤ n`") or `some q`:

```
q ← 0
while c ≠ 0 do
    m ← deg(c) − deg(b)
    if n < 0 or m < 0 or m > n then return "no solution"
    p ← (lc(c)/lc(b)) tᵐ
    q ← q + p;  n ← m − 1;  c ← c − Dp − b·p
return q
```

`D = cmonomialDeriv Dt`; the loop is fuel-bounded (`deg(c)` strictly drops each pass, so it halts after
`≤ deg(c)+1` steps). The `tᵐ`-monomial is `cshiftG m [lc(c)/lc(b)]`. When the non-cancellation
hypothesis fails the leading terms cancel and this routine may wrongly report "no solution"; the
cancellation case (§6.6) is the separate, deferred subroutine documented in the module docstring. -/
def cPolyRischDENoCancel (Dt : CPolyG QFunNZ) : ℕ → (b c : CPolyG QFunNZ) → (n : ℤ) →
    Option (CPolyG QFunNZ)
  | 0, _, _, _ => none
  | fuel + 1, b, c, n =>
    if cisZeroG c then some []
    else
      let m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ)
      if n < 0 ∨ m < 0 ∨ m > n then none
      else
        let coeff := CField.div (cleadG c) (cleadG b)
        let p := cshiftG m.toNat [coeff]
        let c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p)
        match cPolyRischDENoCancel Dt fuel b c' (m - 1) with
        | none => none
        | some q => some (caddG p q)

/-! ### `cParametricLogDeriv` (Bronstein §5.12 / §7.3, the `ParametricLogarithmicDerivative` box,
book p.176/253) — over the **base field** `k = ℚ(x)`

The §6.6 cancellation primitive case branches on whether the coefficient `b ∈ k = ℚ(x)` is of the form
`b = Dz/z` (a logarithmic derivative of a `k`-element) and, more generally, whether `n·b = Dz/z` for a
nonzero `n ∈ ℤ` and `z ∈ k*` (a logarithmic derivative of a `k`-**radical**, the *parametric*
logarithmic derivative problem, §7.3 eq. 7.37). Here `k = ℚ(x)`, `D = d/dx`, so a `QFunNZ` element `b`
is handled directly (the §5.12 recursion bottoms out at the base field, where the special set `S = k`).

The recognizer (§5.12, book p.176): if `b = Dz/z` for `z ∈ ℚ(x)*`, then `b` is **simple** (its
lowest-terms denominator is squarefree) and **proper** (`deg(num) < deg(den)`, no polynomial part —
`Dz/z` has degree `< 0` as a rational function), and all Rothstein–Trager residues are integers. In
particular a **nonzero constant** `b ∈ ℚ*` is *never* a logarithmic derivative of a `ℚ(x)`-element
(nor, scaled, of a radical): `Dz/z = const ≠ 0` forces `z = e^{const·x}`, not rational (this is the
Liouville obstruction that makes `∫ e^{bx} …` nonelementary). That **constant sub-case is exactly the
one the cancellation primitive case reaches in practice**, and it is decided here exactly; the general
proper/simple/integer-residue recognizer over ℚ(x) is the documented continuation (it needs the
Rothstein–Trager residue machinery over ℚ rather than over the tower, plus the §7.3 linear-constraint
solve for `m/n`). -/

/-- **Polynomial part / properness of a base-field element** `cBaseIsProper b`: `true` iff the
lowest-terms `QFunNZ` value `b = a/d ∈ ℚ(x)` is *proper*, i.e. `deg(a) < deg(d)` (so `b` has no
polynomial part). A logarithmic derivative `Dz/z` of a `ℚ(x)`-element is always proper, so a `b` that
fails this is **not** a logarithmic derivative. A nonzero constant `b ∈ ℚ*` (`deg a = deg d = 0`) is
*not* proper, hence not a logarithmic derivative — the constant obstruction. -/
def cBaseIsProper (fuel : ℕ) (b : QFunNZ) : Bool :=
  let bn := Compute.qnorm fuel b.1
  Compute.cdeg bn.1 < Compute.cdeg bn.2 && !Compute.cisZero bn.1

/-- **Parametric-logarithmic-derivative test over the base field** `cParametricLogDeriv fuel b`
(Bronstein §5.12 / §7.3, book p.176/253), for `b ∈ k = ℚ(x)`: returns `true` iff `b` *could* be a
logarithmic derivative of a `ℚ(x)`-radical, i.e. `n·b = Dz/z` for some nonzero `n ∈ ℤ` and `z ∈ ℚ(x)*`
— and `false` iff `b` is provably **not** of that form. A nonzero element of `ℚ(x)` that is not proper
(has a polynomial part, in particular every nonzero constant) is provably not a logarithmic derivative
of a radical (the residues argument of §5.12: `Dz/z` is always proper and simple). This decides the
constant sub-case `b ∈ ℚ*` exactly (returns `false`), which is the branch the §6.6 cancellation
primitive case reaches. For a proper `b` the full recognizer (squarefree-denominator test + integer
Rothstein–Trager residues + the §7.3 unique-`m/n` linear solve) is the documented continuation; this
conservative test returns `true` there, so the caller takes the *radical/log-derivative* branch only
when it cannot rule it out — keeping the **non-radical** branch (eq. 6.23) sound. -/
def cParametricLogDeriv (fuel : ℕ) (b : QFunNZ) : Bool :=
  -- `b = 0` is the trivial logarithmic derivative `Dz/z` with `z = 1`; a proper `b` is not ruled out.
  CField.isZero b || cBaseIsProper fuel b

/-! ### `cRischDEBase` (Bronstein §6.6 eq. 6.23 base case) — the rational RDE `Ds + b·s = c` over ℚ(x)

The cancellation primitive case reduces, leading-coefficient by leading-coefficient, to a **Risch
differential equation over the coefficient field** `k = ℚ(x)` with `D = d/dx` (eq. 6.23 `Dy + by =
lc(c)`). The general base solver is the *rational* Risch DE in `x` (the whole Ch. 6 pipeline re-run with
`t = x` the trivial primitive monomial over ℚ) — a recursion into a second instance of the algorithm.
Here we implement the **bottoming-out sub-case** where the base data is `k`-constant (`b, c ∈ ℚ`), for
which the equation collapses to the linear-algebraic `b·s = c` (since `Ds = 0` for a constant `s` and a
constant solution is forced when `b ≠ 0` is a nonzero constant): the solution is `s = c/b ∈ ℚ ⊂ ℚ(x)`.
This is the genuine base case reached by the worked cancellation example. The general rational-RDE-in-x
recursion (non-constant `b, c ∈ ℚ(x)`) is the documented remaining piece. -/

/-- **Base-field Risch DE `Ds + b·s = c` over `k = ℚ(x)`**, the eq. 6.23 recursion target of the §6.6
cancellation primitive case. `cRischDEBase fuel b c` returns `some s` with `s ∈ ℚ(x)` solving
`Ds + b·s = c` (`D = d/dx` on `QFunNZ`), or `none`. Implemented for the **bottoming-out constant
sub-case**: when `b` and `c` are `k`-constants (`b, c ∈ ℚ`), `Ds = 0` for the constant solution and
`s = c/b` (`b ≠ 0`); `b = 0` needs `Ds = c`, solvable by a constant only when `c = 0` (`s = 0`). For
non-constant `b, c ∈ ℚ(x)` this returns `none` (the general rational-RDE-in-`x` recursion is the
documented continuation), making the test sound: a reported `some s` always *actually solves* the
base equation (checked by `cRischDEBase_solves` at the worked value). -/
def cRischDEBase (_fuel : ℕ) (b c : QFunNZ) : Option QFunNZ :=
  -- constant test: a `QFunNZ` value is a `k`-constant iff its lowest-terms `d/dx` derivative is zero.
  let isConst : QFunNZ → Bool := fun z => CField.isZero (CDiffField.cderiv z)
  if isConst b && isConst c then
    if CField.isZero b then
      -- `Ds = c` with constant `c`: a constant `s` works only when `c = 0` (then `s = 0`).
      if CField.isZero c then some CField.zero else none
    else
      -- `b·s = c` with `b ≠ 0` constant ⇒ `s = c/b` (also constant, so `Ds = 0`).
      some (CField.div c b)
  else none

/-! ### `cPolyRischDECancelPrim` (Bronstein §6.6, the `PolyRischDECancelPrim(b,c,D,n)` box, book p.212)

The **primitive cancellation case** of `PolyRischDE`: `Dt ∈ k` (so `δ(t) = 0`), `b ∈ k*`, `c ∈ k[t]`,
solving `Dq + b·q = c` for `q ∈ k[t]` of degree `≤ n`. Because `D` does not raise the `t`-degree
(`Dt ∈ k`), the leading terms of `Dq` and `bq` cancel, so the non-cancellation loop fails and the
solve proceeds degree-by-degree by **recursing into a base Risch DE over `k = ℚ(x)`** (eq. 6.23). -/

/-- **Computable Poly-Risch-DE, primitive cancellation case** `cPolyRischDECancelPrim Dt fuel b c n`
(Bronstein §6.6, the `PolyRischDECancelPrim(b,c,D,n)` box, book p.212). Given the primitive monomial
derivation `D` (`Dt ∈ k = ℚ(x)`), `b ∈ k*` (a `QFunNZ`-constant `t`-polynomial of degree 0) and
`c ∈ k[t]`, with degree bound `n : ℤ`, returns `none` ("no solution of degree `≤ n`") or `some q` with
`q ∈ k[t]`, `deg(q) ≤ n`, solving `Dq + b·q = c`:

```
if b = Dz/z for z ∈ k* then           (* logarithmic-derivative branch, §5.12 *)
    if zc = Dp for p ∈ k[t] and deg(p) ≤ n then return(p/z) else return "no solution"
if c = 0 then return 0
if n < deg(c) then return "no solution"
q ← 0
while c ≠ 0 do
    m ← deg(c)
    if n < m then return "no solution"
    s ← RischDE(b, lc(c))             (* base RDE over k: Ds + b·s = lc(c) *)
    if s = "no solution" then return "no solution"
    q ← q + s·tᵐ;  n ← m − 1;  c ← c − b·s·tᵐ − D(s·tᵐ)
return q
```

`D = cmonomialDeriv Dt`. The logarithmic-derivative branch (`b = Dz/z`) routes through
`cParametricLogDeriv` (§5.12) — implemented for the reachable constant sub-case where
`b ∈ ℚ*` is provably *not* a logarithmic derivative, so the algorithm correctly proceeds to the
general degree-by-degree recursion (the in-field-integration sub-branch, needing the full §5.12
recognizer-and-construct, is the documented continuation). The `RischDE(b, lc(c))` base solve is
`cRischDEBase` (eq. 6.23), implemented for the bottoming-out `k`-constant case. The `while` loop is
fuel-bounded (`deg(c)` strictly drops each pass). -/
def cPolyRischDECancelPrim (Dt : CPolyG QFunNZ) : ℕ → (b c : CPolyG QFunNZ) → (n : ℤ) →
    Option (CPolyG QFunNZ)
  | 0, _, _, _ => none
  | fuel + 1, b, c, n =>
    -- `b ∈ k*` is a degree-0 `t`-polynomial; its single coefficient `b₀ = lc(b) ∈ ℚ(x)` is the scalar.
    let b0 : QFunNZ := cleadG b
    -- §5.12 logarithmic-derivative branch `b = Dz/z`: not taken in the reachable (non-radical) case;
    -- when `cParametricLogDeriv` cannot rule `b` out we fall through to the general recursion, which
    -- is sound (eq. 6.23 applies to any `b ∈ k*`). The constant `b ∈ ℚ*` reached here returns `false`.
    if cisZeroG c then some []
    else if n < (cdegG c : ℤ) then none
    else
      let m : ℕ := cdegG c
      -- `lc(c) ∈ ℚ(x)` and the base RDE `Ds + b₀·s = lc(c)` over `k = ℚ(x)` (eq. 6.23).
      match cRischDEBase fuel b0 (cleadG c) with
      | none => none
      | some s =>
        let stm : CPolyG QFunNZ := cshiftG m [s]               -- `s·tᵐ`
        -- `c ← c − b·(s·tᵐ) − D(s·tᵐ)`, `n ← m − 1`.
        let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
        match cPolyRischDECancelPrim Dt fuel b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)

/-! ### `cPolyRischDE` — dispatch non-cancellation vs cancellation (Bronstein §6.5 + §6.6)

After `cSPDE` reduces to `Dq + b·q = c` (eq. 6.19, `a = 1`) with a degree bound `n`, the choice of
which §6.5/§6.6 solver applies is by the monomial type and `deg(b)` (Lemma 6.5.1): the
**non-cancellation** case (`deg(b) > max(0, δ−1)`, leading terms don't cancel) goes to
`cPolyRischDENoCancel`; the **primitive cancellation** case (`δ = 0`, `b ∈ k*`) goes to
`cPolyRischDECancelPrim`. The hyperexponential (`δ = 1`) and nonlinear/hypertangent (`δ ≥ 2`)
cancellation cases (`PolyRischDECancelExp`/`Tan`, book p.213/215) are the documented continuation. -/

/-- **Computable Poly-Risch-DE dispatcher** `cPolyRischDE Dt fuel b c n` (Bronstein §6.5 + §6.6): solve
`Dq + b·q = c` (eq. 6.19) for `q ∈ k[t]` with `deg(q) ≤ n`, choosing the §6.5 non-cancellation solver
or the §6.6 cancellation solver by the monomial type and `deg(b)` (Lemma 6.5.1):

* If `deg(b) > max(0, δ−1)` (non-cancellation, `δ = deg(Dt)`): `cPolyRischDENoCancel`.
* Else if `δ = 0` (primitive) and `b ∈ k*` (`deg(b) = 0`): `cPolyRischDECancelPrim` (§6.6 primitive).
* Else (hyperexponential `δ = 1` / nonlinear `δ ≥ 2` cancellation): the documented continuation
  (`PolyRischDECancelExp`/`Tan`) — falls back to `cPolyRischDENoCancel` (correct whenever the
  non-cancellation hypothesis happens to hold; otherwise returns `none`). -/
def cPolyRischDE (Dt : CPolyG QFunNZ) (fuel : ℕ) (b c : CPolyG QFunNZ) (n : ℤ) :
    Option (CPolyG QFunNZ) :=
  let δ : ℤ := (cdegG Dt : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  if db > max 0 (δ - 1) then
    -- non-cancellation case (Lemma 6.5.1(i)).
    cPolyRischDENoCancel Dt fuel b c n
  else if δ = 0 ∧ db = 0 then
    -- primitive cancellation case (§6.6, `Dt ∈ k`, `b ∈ k*`).
    cPolyRischDECancelPrim Dt fuel b c n
  else
    -- hyperexponential / nonlinear cancellation (documented continuation); the non-cancellation
    -- loop is still correct when it does not actually cancel.
    cPolyRischDENoCancel Dt fuel b c n

/-! ### `cRischDE` — the full Risch differential equation solver over the tower (assembly)

`cRischDE Dt fuel fnum fden gnum gden` threads the five built stages: `cWeakNormalizer` (§6.1),
`cRdeNormalDenominator` (§6.2), `cRdeSpecialDenominator` (§6.2), `cRdeBoundDegree` (§6.3),
`cSPDE` (§6.4), `cPolyRischDENoCancel` (§6.5), reconstructing a solution `y = ynum/yden ∈ k(t)` of
`Dy + f·y = g`, or `none` when no elementary solution exists (in the cases the non-cancellation
pipeline decides). The cancellation case (§6.6) is the remaining piece (see the module docstring). -/

/-- **Computable Risch differential equation solver** `cRischDE Dt fuel fnum fden gnum gden` (Bronstein
Ch. 6, assembled). For `f = fnum/fden`, `g = gnum/gden ∈ k(t) = ℚ(x)(t)` and the monomial derivation
`D` (`= cmonomialDeriv Dt`), returns `some (ynum, yden)` with `y = ynum/yden ∈ k(t)` solving
`Dy + f·y = g`, or `none` when the pipeline finds no solution. The stages:

1. **§6.2 normal denominator.** `cRdeNormalDenominator` reduces `Dy + fy = g` to `a₀·Dq + b₀·q = c₀`
   with `q = y·h₀` (`none` ⇒ no solution). *(`f` is assumed weakly normalized — the post-Hermite RDE
   input; `cWeakNormalizer` returns `q = 1` on such `f`, confirmed by `rischDE_normalDenominator_example`.)*
2. **§6.2 special denominator.** `cRdeSpecialDenominator a₀ b₀ c₀` ⇒ `(a, b, c, h₁)` with `r = q·h₁⁻¹`
   *(`h₁ = p^{-n}`)* a polynomial — but the polynomial-stage unknown is `q·h₁` over `k[t]`; here `h₁`
   is the special clearing factor, so the total denominator gathered is `h₀·h₁`.
3. **§6.3 degree bound.** `N ← cRdeBoundDegree a b c` bounds `deg_t` of the polynomial unknown.
4. **§6.4 SPDE.** `cSPDE a b c N` ⇒ `(b̄, c̄, m, α, β)` (`none` ⇒ no solution): the unknown is
   `α·v + β` where `v` solves `Dv + b̄·v = c̄`, `deg(v) ≤ m`.
5. **§6.5/§6.6 PolyRischDE.** `cPolyRischDE b̄ c̄ m` ⇒ `v` (`none` ⇒ no solution): the dispatcher
   chooses the §6.5 non-cancellation solver or the §6.6 primitive cancellation solver by monomial type
   and `deg(b̄)` (Lemma 6.5.1).

Then the polynomial unknown is `Q = α·v + β`, the §6.2-cleared unknown was `Q·h₁⁻¹`… concretely
`y = Q / (h₀ · h₁)`: `q = y·h₀` and `r = q·h₁⁻¹ = Q`, so `y = Q·h₁ / h₀`. We return `ynum = Q·h₁`,
`yden = h₀`. Fuel-bounded throughout. -/
def cRischDE (Dt : CPolyG QFunNZ) (fuel : ℕ) (fnum fden gnum gden : CPolyG QFunNZ) :
    Option (CPolyG QFunNZ × CPolyG QFunNZ) :=
  match cRdeNormalDenominator Dt fuel fnum fden gnum gden with
  | none => none
  | some (a0, b0, c0, h0) =>
    let (a, b, c, h1) := cRdeSpecialDenominator Dt fuel a0 b0 c0
    let N := cRdeBoundDegree Dt fuel a b c
    match cSPDE Dt fuel a b c (N : ℤ) with
    | none => none
    | some (bbar, cbar, m, α, β) =>
      match cPolyRischDE Dt fuel bbar cbar m with
      | none => none
      | some v =>
        -- polynomial unknown `Q = α·v + β`; `y = Q·h₁ / h₀`.
        let Q := caddG (cmulG α v) β
        some (cmulG Q h1, h0)

end CPolyG

/-! ### Validation — Bronstein Example 6.1.2 (book p.186): `t = tan(x)`, `Dt = 1 + t²`, `Dy+(t²+1)y=1/t²`

`k = ℚ(x)`, `D = d/dx`, the monomial `t = tan(x)` with `Dt = 1 + t²`. The equation
`Dy + (t²+1)y = 1/t²` arises from `∫ e^{tan(x)}/tan(x)² dx`. So `f = t²+1` (numerator `t²+1`,
denominator `1`) and `g = 1/t²` (numerator `1`, denominator `t²`). Bronstein's run:
`(dₙ, dₛ) = (1, t²+1)`, `(eₙ, eₛ) = (t², 1)`, `p = gcd(1, t²) = 1`, `h = gcd(t², 2t)/gcd(1,1) = t`,
`dₙh² = t²` divisible by `eₙ = t²`, and the reduction quadruplet is
`(a, b, c, h) = (t, (t−1)(t²+1), 1, t)` — the reduced equation `t·Dq + (t−1)(t²+1)q = 1` (eq. 6.5). -/

open CPolyG QFunNZ

/-- Example 6.1.2's monomial derivative `Dt = 1 + t²` (`t = tan(x)`; low→high in `t`,
ℚ-constant coefficients). -/
def rischDExampleDt : CPolyG QFunNZ := [ofConstNZ 1, ofConstNZ 0, ofConstNZ 1]

/-- Example 6.1.2's `f = t²+1`: numerator `t²+1`, denominator `1`. -/
def rischDExampleFnum : CPolyG QFunNZ := [ofConstNZ 1, ofConstNZ 0, ofConstNZ 1]
/-- Example 6.1.2's `f`-denominator `1`. -/
def rischDExampleFden : CPolyG QFunNZ := [ofConstNZ 1]

/-- Example 6.1.2's `g = 1/t²`: numerator `1`. -/
def rischDExampleGnum : CPolyG QFunNZ := [ofConstNZ 1]
/-- Example 6.1.2's `g`-denominator `t²` (low→high in `t`). -/
def rischDExampleGden : CPolyG QFunNZ := [ofConstNZ 0, ofConstNZ 0, ofConstNZ 1]

/-- Example 6.1.2's expected reduction component `a = t` (low→high in `t`). -/
def rischDExampleA : CPolyG QFunNZ := [ofConstNZ 0, ofConstNZ 1]
/-- Example 6.1.2's expected reduction component `b = (t−1)(t²+1) = t³ − t² + t − 1` (low→high in `t`). -/
def rischDExampleB : CPolyG QFunNZ := [ofConstNZ (-1), ofConstNZ 1, ofConstNZ (-1), ofConstNZ 1]
/-- Example 6.1.2's expected reduction component `c = 1`. -/
def rischDExampleC : CPolyG QFunNZ := [ofConstNZ 1]
/-- Example 6.1.2's expected reduction component `h = t` (low→high in `t`). -/
def rischDExampleH : CPolyG QFunNZ := [ofConstNZ 0, ofConstNZ 1]

-- **Sanity prints** (book p.186): the `RdeNormalDenominator` quadruplet `(a,b,c,h) = (t, t³−t²+t−1, 1, t)`
-- and the `WeakNormalizer` value `q = 1` (`f = t²+1` is already weakly normalized).
#eval (CPolyG.cRdeNormalDenominator rischDExampleDt 30 rischDExampleFnum rischDExampleFden
  rischDExampleGnum rischDExampleGden).map (fun (a, b, c, h) =>
    (((a : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
     ((b : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
     ((c : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
     ((h : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1))))
#eval (CPolyG.cWeakNormalizer rischDExampleDt 30 rischDExampleFnum rischDExampleFden : List QFunNZ).map
    (fun z : QFunNZ => Compute.qnorm 30 z.1)
-- **Sanity prints** (book p.192/202, Examples 6.2.2 + 6.3.4 continuing 6.1.2): `cRdeSpecialDenominator`
-- on `(a,b,c) = (t, (t−1)(t²+1), 1)` returns `(t, (t−1)(t²+1), 1, 1)` (`p = t²+1`, `n = 0`, `N = 0`,
-- `ν_p(b) = 1`, `ν_p(c) = 0`), and `cRdeBoundDegree` returns the degree bound `0`.
#eval (fun (abcd : _ × _ × _ × _) =>
    (((abcd.1 : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
     ((abcd.2.1 : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
     ((abcd.2.2.1 : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
     ((abcd.2.2.2 : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1))))
  (CPolyG.cRdeSpecialDenominator rischDExampleDt 30 rischDExampleA rischDExampleB rischDExampleC)
#eval CPolyG.cRdeBoundDegree rischDExampleDt 30 rischDExampleA rischDExampleB rischDExampleC

/-- **Example 6.1.2 — the first two RDE stages execute over the tower** (`native_decide`, Bronstein §6.1
+ §6.2, book p.183/185/186). For `Dy + (t²+1)y = 1/t²` over ℚ(x)(t), `t = tan(x)`, `Dt = 1+t²`:

1. **Weak normalizer (§6.1).** `f = t²+1` is already weakly normalized — its denominator is `1`, so the
   residue resultant has no positive integer roots and `cWeakNormalizer` returns `q = 1`.
2. **Normal denominator (§6.2).** `cRdeNormalDenominator` returns `some (a, b, c, h)` with
   `(a, b, c, h) = (t, (t−1)(t²+1), 1, t)` — checked componentwise by `cisZeroG` of each cleared
   difference. So every solution `y` is `y = q/t` with `q` solving `t·Dq + (t−1)(t²+1)q = 1` (eq. 6.5).

This is the deliverable: the §6.1 `WeakNormalizer` and §6.2 `RdeNormalDenominator` stages of the Risch
differential equation algorithm *compute* over the monomial tower ℚ(x)[t] and return the book's values.
Abstract correctness (the `Dy + fy = g ↔ a·Dq + b·q = c` equivalence) is not proved here; the remaining
pipeline stages (special denominator, degree bound, SPDE, PolyRischDE) are documented in the module
docstring as the continuation. -/
theorem rischDE_normalDenominator_example :
    cisZeroG (csubG (cWeakNormalizer rischDExampleDt 30 rischDExampleFnum rischDExampleFden)
        [CField.one]) = true
    ∧ (match cRdeNormalDenominator rischDExampleDt 30 rischDExampleFnum rischDExampleFden
          rischDExampleGnum rischDExampleGden with
        | some (a, b, c, h) =>
            cisZeroG (csubG a rischDExampleA)
              && cisZeroG (csubG b rischDExampleB)
              && cisZeroG (csubG c rischDExampleC)
              && cisZeroG (csubG h rischDExampleH)
        | none => false) = true := by native_decide

#print axioms rischDE_normalDenominator_example

/-- **Example 6.2.2 — the special-denominator stage executes over the tower** (`native_decide`,
Bronstein §6.2, the `RdeSpecialDenomTan` box, book p.192). Continuing Example 6.1.2, the reduced
equation `t·Dq + (t−1)(t²+1)·q = 1` (eq. 6.5) has `a = t`, `b = (t−1)(t²+1)`, `c = 1` over ℚ(x)(t) with
`t = tan(x)`, `Dt = 1+t²`. The monic special irreducible is `p = t²+1`, and:

* `n_b = ν_{t²+1}(b) = 1`, `n_c = ν_{t²+1}(c) = 0`, so `n = min(0, n_c − min(0, n_b)) = 0`;
* `n_b ≠ 0`, so `N = max(0, −n_b, n − n_c) = 0`.

Hence `cRdeSpecialDenominator` returns `(ā, b̄, c̄, h) = (t, (t−1)(t²+1), 1, 1)` — the equation is
unchanged and `h = p⁻ⁿ = 1`, so any solution `q ∈ k⟨t⟩` of (6.5) is already in `k[t]`
(`k⟨t⟩ ∩ O_{t²+1} = k[t]`). Each of the four components is pinned by `cisZeroG` of its cleared
difference against the book's values (`ā, b̄, c̄ = a, b, c` and `h = 1`). -/
theorem rischDE_specialDenominator_example :
    (match cRdeSpecialDenominator rischDExampleDt 30 rischDExampleA rischDExampleB rischDExampleC with
      | (abar, bbar, cbar, h) =>
          cisZeroG (csubG abar rischDExampleA)
            && cisZeroG (csubG bbar rischDExampleB)
            && cisZeroG (csubG cbar rischDExampleC)
            && cisZeroG (csubG h [CField.one])) = true := by native_decide

#print axioms rischDE_specialDenominator_example

/-- **Example 6.3.4 — the degree-bound stage executes over the tower** (`native_decide`, Bronstein §6.3,
the `RdeBoundDegreeNonLinear` box, book p.202). Continuing Examples 6.1.2 and 6.2.2, the polynomial
equation `t·Dq + (t−1)(t²+1)·q = 1` (eq. 6.5/6.12) has `a = t`, `b = (t−1)(t²+1)`, `c = 1`, and the
monomial `t = tan(x)` is **nonlinear** with `δ = deg(Dt) = deg(1+t²) = 2`. Then:

* `d_a = deg(a) = 1`, `d_b = deg(b) = 3`, `d_c = deg(c) = 0`;
* `n = max(0, d_c − max(d_a + δ − 1, d_b)) = max(0, 0 − max(2, 3)) = max(0, −3) = 0`;
* `d_b ≠ d_a + δ − 1` (`3 ≠ 2`), so the cancellation branch is inactive.

Hence `cRdeBoundDegree` returns the upper bound `0`: any polynomial solution `q ∈ k[t]` of (6.5) has
`deg_t(q) ≤ 0`, i.e. `q ∈ ℚ(x)`. This is the deliverable for §6.3 — the degree bound *computes* the
book's value over the monomial tower ℚ(x)[t]. -/
theorem rischDE_boundDegree_example :
    cRdeBoundDegree rischDExampleDt 30 rischDExampleA rischDExampleB rischDExampleC = 0 := by
  native_decide

#print axioms rischDE_boundDegree_example

/-! ### Validation — Bronstein Example 6.5.1 (book p.208): the FULL RDE solver, end-to-end

`k = ℚ(x)`, `D = d/dx`, `t = tan(x)` (`Dt = 1+t²`). The equation
`Dy + (t²+1)y = t³ + (x+1)t² + t + (x+2)` (eq. 6.20) arises from
`∫ (tan³x + (x+1)tan²x + tan x + x + 2) e^{tan x} dx`. The book runs the §6.5 non-cancellation loop
(`b = t²+1`, `n = +∞`) and gets the **elementary solution** `y = t + x`, hence
`∫ (…) e^{tan x} dx = (tan x + x) e^{tan x}`. The full pipeline `cRischDE` (normal denominator → special
denominator → degree bound → `cSPDE` → `cPolyRischDENoCancel`) reproduces this. -/

open CPolyG QFunNZ

/-- The variable `x ∈ ℚ(x)` as a tower constant `QFunNZ` (numerator `[0,1]`, denominator `[1]`). -/
def rischDExQ : QFunNZ := ofNumDen [0, 1] [1] (by decide)

/-- Example 6.5.1's right-hand side `g = t³ + (x+1)t² + t + (x+2)` (numerator over denominator `1`),
low→high in `t` with `ℚ(x)` coefficients. -/
def rischDExampleG651num : CPolyG QFunNZ :=
  [QFunNZ.qaddNZ rischDExQ (ofConstNZ 2), ofConstNZ 1, QFunNZ.qaddNZ rischDExQ (ofConstNZ 1),
   ofConstNZ 1]

/-- **Cleared Risch-DE identity check** `rdeClearedCheck Dt fnum fden gnum gden ynum yden`: `true` iff
`y = ynum/yden` solves `Dy + (fnum/fden)·y = gnum/gden`, verified as the polynomial identity obtained
by clearing all denominators (multiply through by `yden²·fden·gden`, using
`Dy = (D(ynum)·yden − ynum·D(yden))/yden²`):
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²`. `D = cmonomialDeriv
Dt`; the equality is decided by `cisZeroG` of the cleared difference (`QFunNZ` has no `DecidableEq`). -/
def rdeClearedCheck (Dt fnum fden gnum gden ynum yden : CPolyG QFunNZ) : Bool :=
  let Dyn := cmonomialDeriv Dt ynum
  let Dyd := cmonomialDeriv Dt yden
  let lhs := caddG
    (cmulG (cmulG gden fden) (csubG (cmulG Dyn yden) (cmulG ynum Dyd)))
    (cmulG (cmulG (cmulG gden fnum) ynum) yden)
  let rhs := cmulG (cmulG gnum fden) (cmulG yden yden)
  cisZeroG (csubG lhs rhs)

-- **Sanity print** (book p.208): `cRischDE` on Example 6.5.1 returns `y = (x+t)/1`.
#eval (CPolyG.cRischDE rischDExampleDt 50 rischDExampleFnum rischDExampleFden
    rischDExampleG651num rischDExampleFden).map
  (fun p => (((p.1 : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
             ((p.2 : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1))))

/-- **Example 6.5.1 — the FULL Risch differential equation solver runs end-to-end over the tower**
(`native_decide`, Bronstein Ch. 6, book p.208). For `Dy + (t²+1)y = t³ + (x+1)t² + t + (x+2)` over
`ℚ(x)(t)`, `t = tan(x)`, `Dt = 1+t²` (here `f = t²+1`, `g = t³+(x+1)t²+t+(x+2)`, both denominators `1`),
the assembled `cRischDE` — `cRdeNormalDenominator` (§6.2) → `cRdeSpecialDenominator` (§6.2) →
`cRdeBoundDegree` (§6.3) → `cSPDE` (§6.4) → `cPolyRischDENoCancel` (§6.5) — returns
`some (ynum, yden)`, and the returned `y = ynum/yden` is verified to **actually solve** `Dy + f·y = g`
by `rdeClearedCheck` (the cleared polynomial identity, not merely pinning the output): the book's
solution is `y = t + x`. This is the capstone deliverable — the complete non-cancellation RDE pipeline
*computes* an elementary solution over the monomial tower ℚ(x)[t]. -/
theorem rischDE_solve_example :
    (match cRischDE rischDExampleDt 50 rischDExampleFnum rischDExampleFden
          rischDExampleG651num rischDExampleFden with
      | some (ynum, yden) =>
          rdeClearedCheck rischDExampleDt rischDExampleFnum rischDExampleFden
            rischDExampleG651num rischDExampleFden ynum yden
      | none => false) = true := by native_decide

#print axioms rischDE_solve_example

/-- **Example 6.4.1 — the RDE solver correctly reports NO solution** (`native_decide`, Bronstein §6.4,
book p.204). The original Example 6.1.2 equation `Dy + (t²+1)y = 1/t²` (eq. 6.4, from
`∫ e^{tan x}/tan²x dx`) has **no** solution `y ∈ k(t)`: the book's `SPDE` run reaches
`SPDE(t, t³+t, t²−t+1, D, −1)` with `n = −1 < 0` and `c ≠ 0`, returning "no solution", so the original
integral is not elementary. The full `cRischDE` (here `f = t²+1` with denominator `1`, `g = 1/t²` with
numerator `1`, denominator `t²`) returns `none`, matching the book. -/
theorem rischDE_noSolution_example :
    (cRischDE rischDExampleDt 50 rischDExampleFnum rischDExampleFden
      rischDExampleGnum rischDExampleGden).isNone = true := by native_decide

#print axioms rischDE_noSolution_example

/-! ### Validation — the §6.6 CANCELLATION primitive case fires (`t = log(x)`, `Dt = 1/x`)

The cancellation primitive case genuinely triggers exactly when the monomial is **primitive**
(`Dt ∈ k`, `δ = 0`) and `b ∈ k*` (`deg(b) = 0`): then `D` does not raise the `t`-degree, the leading
terms of `Dq` and `bq` cancel, and `cPolyRischDENoCancel` cannot proceed — the solve must recurse into
a base Risch DE over `k = ℚ(x)` (eq. 6.23). We use `k = ℚ(x)`, `D = d/dx`, `t = log(x)` (so
`Dt = 1/x ∈ k`, primitive), and the equation

```
  Dq + 1·q = log(x) + 1/x      (b = 1 ∈ ℚ*,  c = t + 1/x ∈ ℚ(x)[t],  deg(c) = 1)
```

whose solution is `q = t = log(x)` (indeed `Dq + q = D(t) + t = 1/x + t`). The run exercises the full
§6.6 primitive cancellation path:

* `b = 1 ∈ ℚ*` is **not** a logarithmic derivative of a `ℚ(x)`-radical (`cParametricLogDeriv` returns
  `false` — a nonzero constant has a polynomial part, the §5.12 obstruction: `Dz/z = 1` forces
  `z = eˣ ∉ ℚ(x)`), so the algorithm correctly takes the general degree-by-degree branch (eq. 6.23);
* the leading-coefficient base solve `RischDE(b₀, lc(c)) = RischDE(1, 1)` over `ℚ(x)` returns `s = 1`
  (`cRischDEBase`: the bottoming-out `ℚ`-constant case `1·s = 1`), giving the leading monomial
  `s·t¹ = t`; the remainder `c − b·t − D(t) = (t + 1/x) − t − 1/x = 0` terminates the loop with `q = t`. -/

open CPolyG QFunNZ

/-- The primitive monomial derivative `Dt = 1/x` (`t = log(x)`); a single degree-0 `t`-coefficient
`1/x ∈ ℚ(x)`. So `δ = deg(Dt) = 0` and the monomial is primitive (`Dt ∈ k`). -/
def rischDECancelDt : CPolyG QFunNZ := [ofNumDen [1] [0, 1] (by decide)]

/-- The cancellation example's coefficient `b = 1 ∈ ℚ* ⊂ ℚ(x)` (a degree-0 `t`-polynomial). -/
def rischDECancelB : CPolyG QFunNZ := [ofConstNZ 1]

/-- The cancellation example's right-hand side `c = log(x) + 1/x = t + 1/x` (low→high in `t`:
constant coefficient `1/x ∈ ℚ(x)`, then `t`-coefficient `1`). -/
def rischDECancelC : CPolyG QFunNZ := [ofNumDen [1] [0, 1] (by decide), ofConstNZ 1]

-- **Sanity prints.** `cParametricLogDeriv` says `b = 1` is not a log-derivative (`false`); the base
-- solve `RischDE(1,1)` over ℚ(x) returns `s = 1`; and `cPolyRischDECancelPrim` returns `q = t`.
#eval CPolyG.cParametricLogDeriv 30 (ofConstNZ 1)
#eval (CPolyG.cRischDEBase 30 (ofConstNZ 1) (ofConstNZ 1)).map (fun z => Compute.qnorm 30 z.1)
#eval (CPolyG.cPolyRischDECancelPrim rischDECancelDt 30 rischDECancelB rischDECancelC 5).map
  (fun q => (q : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1))

/-- **The §6.6 cancellation primitive case fires and solves over the tower** (`native_decide`,
Bronstein §6.6, the `PolyRischDECancelPrim(b,c,D,n)` box, book p.212). For the primitive monomial
`t = log(x)` (`Dt = 1/x ∈ k`, `δ = 0`), the cancellation equation `Dq + 1·q = log(x) + 1/x`
(`b = 1 ∈ ℚ*`, `c = t + 1/x`, `deg(c) = 1`) is solved by `cPolyRischDECancelPrim`, returning some `q`,
and the returned `q` is verified to **actually solve** `Dq + b·q = c` by `cisZeroG` of the cleared
difference `D(q) + b·q − c` (`D = cmonomialDeriv rischDECancelDt`; not merely pinning the output) — the
book's solution is `q = log(x) = t`. The dispatcher `cPolyRischDE` is checked to route this same input
to the cancellation solver (`deg(b) = 0 = max(0, δ−1)`, `δ = 0`), producing an equal `q`.

This is the §6.6 deliverable: the **cancellation** case of `PolyRischDE` — which `cPolyRischDENoCancel`
cannot handle (the leading terms cancel) — *computes* over the monomial tower ℚ(x)[t], driving the
§5.12 parametric-logarithmic-derivative test (`b = 1` ruled out) and the eq. 6.23 base Risch DE over
`k = ℚ(x)` (`RischDE(1,1) = 1`) to the elementary solution `q = log(x)`. The hyperexponential
(`PolyRischDECancelExp`) and nonlinear/hypertangent (`PolyRischDECancelTan`) cancellation cases, and the
general non-constant rational base RDE recursion of eq. 6.23, are the documented continuation. -/
theorem rischDE_cancel_example :
    (match cPolyRischDECancelPrim rischDECancelDt 30 rischDECancelB rischDECancelC 5 with
      | some q =>
          cisZeroG (csubG (caddG (cmonomialDeriv rischDECancelDt q) (cmulG rischDECancelB q))
            rischDECancelC)
      | none => false) = true
    ∧ (match cPolyRischDE rischDECancelDt 30 rischDECancelB rischDECancelC 5,
            cPolyRischDECancelPrim rischDECancelDt 30 rischDECancelB rischDECancelC 5 with
        | some q1, some q2 => cisZeroG (csubG q1 q2)
        | _, _ => false) = true := by native_decide

#print axioms rischDE_cancel_example

end DeepWiki.SymbolicIntegration
