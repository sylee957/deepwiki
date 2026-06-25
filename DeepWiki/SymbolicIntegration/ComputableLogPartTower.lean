import DeepWiki.SymbolicIntegration.ComputableHermiteTower
import DeepWiki.SymbolicIntegration.ComputableGenericBezout

/-! # Computable logarithmic part over the tower ℚ(x)[t] (Bronstein §5.6, the Residue Criterion)
After `cHermiteReduceTower` (§5.3) reduces `f` to a **simple** element `a/d` with `d` squarefree
(`normal`) and `gcd(a, d) = 1`, the *logarithmic* part of `∫ f` is the Rothstein–Trager–Lazard
construction of §5.6 (Theorem 5.6.1, the `ResidueReduce` algorithm). For the monomial derivation
`D = cmonomialDeriv Dt` on `k(t)` with `k = ℚ(x)`, it is

```
  ∫ a/d  =  ∑_{R(c)=0}  c · log( gcd_t(d, a − c·Dd) )
```

where `R(z) = res_t(d, a − z·Dd) ∈ k[z]` is the **residue resultant** (Bronstein writes
`resultant_t(d, a − zDd)`), whose roots `c` are the residues, and each log argument is the per-residue
gcd `gcd_t(d, a − c·Dd)` — Bronstein's `g_i` (`pp_t(R_m)(α, t)` from the subresultant PRS).

This file gives the **computable** rendering over the generic tower carrier `CPolyG QFunNZ` (= ℚ(x)[t]):

* **`cResidueResultantTower Dt fuel a d`** = `R(z)` *without introducing `z` symbolically*, mirroring
  the Chapter-2 `rtResultantCompute`'s **interpolation** template: evaluate `z` at rational points
  `zₖ ∈ ℚ` (lifted to ℚ(x)), take the fraction-free univariate resultant in `t` over ℚ(x)
  (`cresultantG`), and Lagrange-interpolate (`cinterpolateG`) the points `(zₖ, R(zₖ))` back into a
  `CPolyG QFunNZ` whose *variable is `z`*. `Dd = cmonomialDeriv Dt d`.
* **`cLogArgTower Dt fuel a d c`** = `gcd_t(d, a − c·Dd)` for a residue `c ∈ ℚ` (lifted to ℚ(x)), the
  fraction-free monic-in-`t` gcd (`cgcdFF`) — the polynomial that goes inside `log`.

Validation is Bronstein's **Example 5.6.2** (`∫ (2log(x)² − log(x) − x²)/(log(x)³ − x²log(x)) dx`),
`k = ℚ(x)`, `t = log(x)`, `Dt = 1/x`, `a = 2t² − t − x²`, `d = t³ − x²t`. Its residue resultant is
`r = 4x³(1−x²)(z³ − xz² − z/4 + x/4)` (book p.151); the rational residues are `c = ±1/2`, with log
arguments `gcd_t(d, a − cDd) = t ± x` (book p.152, `g₁ = t + 2αx`, `α² = 1/4`). `native_decide` pins
both `cResidueResultantTower` (against the book's `r` up to a ℚ(x) scalar, via `cmonicG`) and the two
log-argument gcds `cLogArgTower … (±1/2) = t ± x`.

Full root-finding of `R(z)` is *not* implemented — the example uses the known rational residues `±1/2`
so the log arguments check directly. The deliverable is the **computable** algorithm + `native_decide`
evidence, not abstract correctness. -/

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ### The residue resultant `R(z) = res_t(d, a − z·Dd)` and the log argument `gcd_t(d, a − c·Dd)` -/

namespace CPolyG

open QFunNZ

/-- **The monomial derivative `Dd` of the (squarefree) denominator** `cDd Dt d = cmonomialDeriv Dt d`
(`D = κ_D + Dt·d/dt`), the second-operand seed of the residue construction. -/
def cDd (Dt d : CPolyG QFunNZ) : CPolyG QFunNZ := cmonomialDeriv Dt d

/-- **`a − c·Dd`** `cAmcDd Dt a d c` for a residue value `c ∈ QFunNZ`: the polynomial in `t` whose
`t`-gcd with `d` is the log argument at `c`. Used both by the interpolation (`c = zₖ`) and the
log-argument gcd (`c` a residue). -/
def cAmcDd (Dt a d : CPolyG QFunNZ) (c : QFunNZ) : CPolyG QFunNZ :=
  csubG a (cscaleG c (cDd Dt d))

/-- **Computable residue resultant** `cResidueResultantTower Dt fuel a d = R(z) = res_t(d, a − z·Dd)
∈ ℚ(x)[z]`, returned as a `CPolyG QFunNZ` whose variable is the residue indeterminate `z` (Bronstein
§5.6, `resultant_t(d, a − zDd)`). Computed by the §2.4 **evaluation + interpolation** template
(`rtResultantCompute`): for `zₖ = 0, 1, …, deg_t d`, sample `R(zₖ) = res_t(d, a − zₖ·Dd)` via the
generic Euclidean-PRS resultant `cresultantG`, then Lagrange-interpolate the points `(zₖ, R(zₖ))`
over ℚ(x). Stays in `CPolyG QFunNZ`; `deg_z R ≤ deg_t d` makes `deg_t d + 1` nodes exact. -/
def cResidueResultantTower (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) : CPolyG QFunNZ :=
  let n := cdegG d                                    -- `deg_z R ≤ deg_t d = n`
  let pts : List (QFunNZ × QFunNZ) := (List.range (n + 1)).map (fun k =>
    let zk : QFunNZ := ofConstNZ (k : ℚ)
    (zk, cresultantG fuel d (cAmcDd Dt a d zk)))
  cinterpolateG pts

/-- **Computable log argument** `cLogArgTower Dt fuel a d c = gcd_t(d, a − c·Dd) ∈ ℚ(x)[t]` for a
residue `c ∈ ℚ` (Bronstein §5.6, the `g_i` inside `log`): the fraction-free monic-in-`t` gcd of `d`
and `a − c·Dd` over ℚ(x)[t] (`cgcdFF`). Together with the residues `c` (roots of
`cResidueResultantTower`), `∑_c c·log(cLogArgTower … c)` is the logarithmic part of `∫ a/d`. -/
def cLogArgTower (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (c : ℚ) : CPolyG QFunNZ :=
  cgcdFF fuel d (cAmcDd Dt a d (ofConstNZ c))

end CPolyG

/-! ### Example 5.6.2 (Bronstein §5.6, p.151–152): `∫ (2t²−t−x²)/(t³−x²t) dx`, `t = log(x)`, `Dt = 1/x`

`k = ℚ(x)`, `D = d/dx`, monomial `t = log(x)` (`Dt = 1/x`). The simple integrand `f = a/d` with
`d = t³ − x²t` (squarefree), `a = 2t² − t − x²`. Bronstein: `Dd = (3/x)t² − 2xt − x`, the residue
resultant is `r = res_t(d, a − zDd) = 4x³(1−x²)(z³ − xz² − z/4 + x/4)`, the rational residues are
`c = ±1/2`, and `gcd_t(d, a − cDd) = t + 2cx` (so `t + x` at `c = 1/2`, `t − x` at `c = −1/2`). -/

open CPolyG QFunNZ

/-- Example 5.6.2's monomial derivative `Dt = 1/x` (`t = log(x)`): a single `t⁰` coefficient equal to
the rational function `1/x` (numerator `1`, denominator `x = [0,1]`). -/
def logPartExampleDt : CPolyG QFunNZ := [ofNumDen [1] [0, 1] (by decide)]

/-- Example 5.6.2's numerator `a = 2t² − t − x²` (low→high in `t`; coefficients are ℚ(x), here ℚ[x]). -/
def logPartExampleA : CPolyG QFunNZ :=
  [ofNumDen [0, 0, -1] [1] (by decide), ofConstNZ (-1), ofConstNZ 2]

/-- Example 5.6.2's denominator `d = t³ − x²t = −x²·t + t³` (squarefree; low→high in `t`). -/
def logPartExampleD : CPolyG QFunNZ :=
  [ofConstNZ 0, ofNumDen [0, 0, -1] [1] (by decide), ofConstNZ 0, ofConstNZ 1]

/-- Example 5.6.2's expected **monic residue resultant** `z³ − xz² − z/4 + x/4 = (z − x)(z² − 1/4)`
(low→high in `z`; coefficients in ℚ(x)): the monic part of the book's `r = 4x³(1−x²)(z³−xz²−z/4+x/4)`.
Its roots are the residues `z = x` (the nonelementary part `r_n`) and `z = ±1/2` (the rational
residues `r_s`, where the log arguments live). -/
def logPartExampleResMonic : CPolyG QFunNZ :=
  [ofNumDen [0, 1] [4] (by decide), ofConstNZ (-1/4),
   ofNumDen [0, -1] [1] (by decide), ofConstNZ 1]

/-- Example 5.6.2's log argument at the residue `c = 1/2`: `t + x` (low→high in `t`; Bronstein
`g₁ = t + 2αx` at `α = 1/2`). -/
def logPartExampleArgPlus : CPolyG QFunNZ := [ofNumDen [0, 1] [1] (by decide), ofConstNZ 1]

/-- Example 5.6.2's log argument at the residue `c = −1/2`: `t − x` (low→high in `t`;
`g₁ = t + 2αx` at `α = −1/2`). -/
def logPartExampleArgMinus : CPolyG QFunNZ := [ofNumDen [0, -1] [1] (by decide), ofConstNZ 1]

-- **Sanity prints** (book p.151–152), each ℚ(x) coefficient reduced to lowest terms for legibility
-- (`qnorm`): `Dd = (3/x)t² − 2xt − x`; the monic residue resultant `z³ − xz² − z/4 + x/4` (low→high in
-- `z`: `[x/4, −1/4, −x, 1]`); and the two log-argument gcds `t + x` / `t − x`.
#eval (cDd logPartExampleDt logPartExampleD : List QFunNZ).map (fun c => Compute.qnorm 30 c.1)
#eval ((CPolyG.cnormG (cmonicG
  (cResidueResultantTower logPartExampleDt 30 logPartExampleA logPartExampleD))) : List QFunNZ).map
    (fun c => Compute.qnorm 30 c.1)
#eval (cLogArgTower logPartExampleDt 30 logPartExampleA logPartExampleD (1/2) : List QFunNZ).map
    (fun c => Compute.qnorm 30 c.1)
#eval (cLogArgTower logPartExampleDt 30 logPartExampleA logPartExampleD (-1/2) : List QFunNZ).map
    (fun c => Compute.qnorm 30 c.1)

/-- **Example 5.6.2 — the computable log part executes over the tower** (`native_decide`, Bronstein
§5.6, p.151–152). For the simple integrand `f = (2t²−t−x²)/(t³−x²t)` over ℚ(x)(t), `t = log(x)`,
`Dt = 1/x`:

1. **Residue resultant.** `cResidueResultantTower` computes `R(z) = res_t(d, a − z·Dd) ∈ ℚ(x)[z]`
   by evaluation + interpolation, and its monic part equals the book's `z³ − xz² − z/4 + x/4`
   (`= (z−x)(z²−1/4)`, the monic part of `r = 4x³(1−x²)(z³−xz²−z/4+x/4)`): checked by `cisZeroG` of
   the difference `cmonicG R − (z³−xz²−z/4+x/4)` over ℚ(x)[z].
2. **Log arguments.** For the rational residues `c = ±1/2` (roots of `z² − 1/4`), the log argument
   `cLogArgTower … c = gcd_t(d, a − c·Dd)` equals `t + x` at `c = 1/2` and `t − x` at `c = −1/2`
   (Bronstein's `g₁ = t + 2αx`, `α² = 1/4`), so the logarithmic part is
   `(1/2)log(t+x) − (1/2)log(t−x)` plus the `z = x` term.

This is the deliverable: the §5.6 residue-criterion log part — the residue resultant `R(z)` and the
per-residue log-argument gcds — *computes* over the monomial tower ℚ(x)[t] and returns the book's
values. Abstract correctness is not proved here. -/
theorem logPartTower_example :
    cisZeroG (csubG
        (cmonicG (cResidueResultantTower logPartExampleDt 30 logPartExampleA logPartExampleD))
        logPartExampleResMonic) = true
    ∧ cisZeroG (csubG (cLogArgTower logPartExampleDt 30 logPartExampleA logPartExampleD (1/2))
        logPartExampleArgPlus) = true
    ∧ cisZeroG (csubG (cLogArgTower logPartExampleDt 30 logPartExampleA logPartExampleD (-1/2))
        logPartExampleArgMinus) = true := by native_decide

#print axioms logPartTower_example

end DeepWiki.SymbolicIntegration
