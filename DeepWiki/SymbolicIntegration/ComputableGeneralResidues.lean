import DeepWiki.SymbolicIntegration.ComputableAlgebraicResidues
import DeepWiki.SymbolicIntegration.ComputableAlgFunctionField

/-! # Algebraic-function residues for ARBITRARY curves: the full double resultant
(Trager, *Integration of Algebraic Functions*, Ch. 5 §2, eq. 7 — the general `F`)

`ComputableAlgebraicResidues` computes Trager's residue resultant for the **hyperelliptic / simple
radical** case `F = y² − ρ`: there `g = g₀ + g₁·y` is linear in `y`, so the inner `resultant_Y` against
`F` collapses to the **norm** `(Z·D' − g₀)² − g₁²·ρ`, and the whole eq. 7 is *one norm + one univariate
resultant*. This file does the **general** curve: an arbitrary monic plane curve `F(x, y) = 0`
(degree `n` in `y` — trigonal `y³ + xy + x`, the non-radical `y² − xy − x³`, any plane curve), where the
inner elimination is the **full bivariate resultant in `y`** of `Z·D'(x) − g(x, y)` against `F(x, y)`.

  **`R(Z) = resultant_X( resultant_Y( Z·D'(X) − g(X, Y), F(X, Y) ), D(X) )`**   (eq. 7, general `F`).

The residues of the differential `f dx = (g/D) dx` (simple finite poles) are the roots of `R(Z)`,
divided by their branch orders — computed by **rational operations over the constant field `K`** alone
(no extension to *find* them); `R`'s splitting field is the minimal field in which the integral can be
expressed (Trager's heart of the log-part computation).

**The two-resultant carrier tower.** Work over the field `α = K(x) = QFunNZG ℚ` (the same carrier as
`ComputableAlgFunctionField`, which already gives `F`, `g` as `α[y]`-polynomials and `afMul`). Evaluate
at a rational `Z`-node `z` (mirroring `cResidueResultantTower`'s evaluate-at-node, keeping things
univariate):

* **inner** `res_Y(z·D' − g, F)` — a univariate resultant **in `y`** of two polynomials with `K(x)`
  coefficients, i.e. `cresultantG` over the *field* `α = QFunNZG ℚ`. Since `F` is monic in `y`, the
  result is a *polynomial* in `x` (a `K(x)`-value whose denominator is a constant), read back as a
  `K[x] = CPolyG ℚ` by `qToPolyQ` (numerator over its constant denominator);
* **outer** `res_X(inner, D)` — a univariate resultant **in `x`** of `inner ∈ K[x]` against `D ∈ K[x]`,
  i.e. `cresultantG` over `ℚ`, giving the value `R(z) ∈ ℚ`.

Sampling `R(z)` at `n·deg_X D + 1` nodes and Lagrange-interpolating (`cinterpolateG`, the
`cResidueResultantTower` template) recovers `R(Z) ∈ ℚ[Z]` (`deg_Z R ≤ n·deg_X D`: each of the `deg D`
roots of `D` contributes a `res_Y` factor of `Z`-degree `≤ n`).

* **`resYAtNode f g Dder z`** — the inner `res_Y(z·D' − g, F)` evaluated at the rational node `z`, read
  as a `CPolyG ℚ` (the `K[x]`-polynomial in `x`).
* **`genResidueResultant fuel f g Dder D`** — the full `R(Z) ∈ ℚ[Z]` by evaluate-`Z`-nodes +
  Lagrange-interpolate, the general-`F` analogue of `cAlgResidueResultant`.

**Validation** (`native_decide`): the trigonal curve `F = y³ + x·y + x` (`n = 3`, genuinely
non-hyperelliptic), plus a **conservativity** check that on a hyperelliptic `F = y² − ρ` the general
`genResidueResultant` reproduces the existing `cAlgResidueResultant` (same `R(Z)` up to normalization). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Reading a `K(x)`-value that is a polynomial back as `K[x] = CPolyG ℚ`

The inner `res_Y` lands in `α = K(x) = QFunNZG ℚ`. When `F` is monic in `y` the resultant is a genuine
*polynomial* in `x`, so the `QFunNZG ℚ` value is `numerator/denominator` with the denominator a nonzero
**constant** (the engine keeps fractions unreduced, so the constant may be any nonzero scalar `c`, not
literally `1`). `qToPolyQ` recovers the `ℚ[x]`-polynomial by the exact division `numerator / denominator`
(`cdivG` over ℚ): when `denominator ∣ numerator` this is the polynomial quotient, here `cscale (c⁻¹)`. -/

/-- **Read a `QFunNZG ℚ` value as a `ℚ[x]`-polynomial** `qToPolyQ fuel v = numerator(v) / denominator(v)`
(`cdivG` over ℚ). Faithful exactly when `v` *is* a polynomial — i.e. `denominator(v) ∣ numerator(v)`
(true here because `res_Y` against a `y`-monic `F` is a polynomial in `x`, with a constant denominator).
The bridge from the inner `res_Y`'s `K(x)` output to the outer `res_X`'s `K[x] = CPolyG ℚ` input. -/
def qToPolyQ (fuel : ℕ) (v : QFunNZG ℚ) : CPolyG ℚ :=
  cdivG fuel v.1.1 v.1.2

/-! ### The inner `res_Y(Z·D' − g, F)` at a rational `Z`-node (the full bivariate resultant in `y`)

For a rational node `z : ℚ`, lift it into `K(x)` (`qxOfNum [z]`), form the polynomial in `y`

  `z·D'(x) − g(x, y) = [z·D'] − g`   (a `CPolyG (QFunNZG ℚ) = (K(x))[y]`),

whose `y⁰` coefficient `z·D' − g₀` is the only one carrying `Z`, and take its **resultant in `y`**
against the curve `F = f` (`cresultantG` over the *field* `α = QFunNZG ℚ`). Because `F` is monic in `y`,
the resultant is a polynomial in `x` (its `K(x)`-denominator is a nonzero constant), read back as a
`ℚ[x]`-polynomial by `qToPolyQ`. This is the general-`F` analogue of `cAlgResidueNorm` — but the *full*
`resultant_Y`, not the `n = 2` norm shortcut. -/

/-- **The `y`-polynomial `z·D'(x) − g(x, y)`** at a rational node `z`: the constant-in-`y` term
`z·D'(x)` (`qxOfNum [z] · Dder`, lifted to a singleton `CPolyG`) minus `g`. Its only `Z`-dependent
coefficient is the `y⁰` one (`z·D' − g₀`), so `res_Y` of this against `F` is degree `≤ deg_y F = n` in
`Z`. `Dder = D'(x) ∈ K(x)` (the `x`-derivative of `D`, a constant in `y`, supplied by the caller). -/
def zDderMinusG (g : CPolyG (QFunNZG ℚ)) (Dder : QFunNZG ℚ) (z : ℚ) : CPolyG (QFunNZG ℚ) :=
  csubG [CField.mul (qxOfNum [z]) Dder] g

/-- **The inner residue resultant at a node** `resYAtNode fuelY fuelD f g Dder z =
res_Y(z·D'(X) − g(X, Y), F(X, Y))` evaluated at the rational node `Z = z`, read as a `ℚ[X]`-polynomial.
Trager eq. 7's inner `resultant_Y` for a **general** monic curve `F = f` (degree `n` in `y`) and a
general `g(x, y)`: the resultant in `y` (`cresultantG fuelY` over the field `α = QFunNZG ℚ`) of
`z·D' − g` (`zDderMinusG`) against `f`, landing in `K(x)`; since `f` is `y`-monic the result is a
polynomial in `x`, recovered as `CPolyG ℚ` by `qToPolyQ fuelD`. The full bivariate `resultant_Y` — the
general-curve replacement for the `n = 2` norm `(z·D' − g₀)² − g₁²·ρ`. -/
def resYAtNode (fuelY fuelD : ℕ) (f g : CPolyG (QFunNZG ℚ)) (Dder : QFunNZG ℚ) (z : ℚ) : CPolyG ℚ :=
  qToPolyQ fuelD (cresultantG fuelY (zDderMinusG g Dder z) f)

/-! ### The full general-`F` residue resultant `R(Z) = res_X(res_Y(Z·D' − g, F), D)`

Assemble the outer `resultant_X` over `ℚ` by the **evaluate-`Z`-nodes + Lagrange-interpolate** template
of `cResidueResultantTower` / `cAlgResidueResultant`: for each rational node `z`, the inner resultant
`resYAtNode` gives the `ℚ[x]`-polynomial `res_Y(z·D' − g, F)(x)`, then `res_X(that, D)` (`cresultantG`
over ℚ) gives the value `R(z) ∈ ℚ`; interpolating the points `(z, R(z))` recovers `R(Z) ∈ ℚ[Z]`.

**`Z`-degree bound.** `res_Y(Z·D' − g, F)` is degree `≤ n = deg_y F` in `Z` (only the `y⁰` coefficient
`Z·D' − g₀` carries `Z`, and the resultant against the degree-`n` `F` is degree `n` in `F`'s argument's
coefficients). The outer `res_X(·, D)` is `∏` over the `deg_X D` roots of `D`, each contributing a
`res_Y` factor of `Z`-degree `≤ n`, so `deg_Z R ≤ n · deg_X D`. Hence `n · deg_X D + 1` nodes are exact
(the hyperelliptic `n = 2` gives `2·deg D`, matching `cAlgResidueResultant`). -/

/-- **The general-curve algebraic-residue resultant** `genResidueResultant fuelY fuelD fuelX f g Dder D
= R(Z) ∈ ℚ[Z]` (Trager Ch. 5 §2 eq. 7, **arbitrary** monic curve `F = f`): the full double resultant
`R(Z) = res_X(res_Y(Z·D'(X) − g(X, Y), F(X, Y)), D(X))`, returned as a `CPolyG ℚ` in the residue
indeterminate `Z`. Computed by **evaluation + interpolation**: for nodes `z = 0, 1, …, n·deg_X D`, the
inner `res_Y` (`resYAtNode`, the full bivariate resultant in `y` over `K(x) = QFunNZG ℚ`) gives the
`ℚ[X]`-polynomial `res_Y(z·D' − g, F)`, then `res_X(·, D)` (`cresultantG fuelX` over ℚ, eliminating `X`)
gives `R(z) ∈ ℚ`, and `cinterpolateG` recovers `R(Z)`. `deg_Z R ≤ n·deg_X D` (`n = deg_y f`), so
`n·deg_X D + 1` nodes are exact. The general-`F` generalization of `cAlgResidueResultant`: where the
hyperelliptic case collapsed the inner `res_Y` to the norm `(z·D' − g₀)² − g₁²·ρ`, here it is the full
`res_Y`. `Dder = D'(x) ∈ K(x)` (the `x`-derivative of `D`, supplied by the caller — `D` itself is a
`ℚ[X]`-polynomial). -/
def genResidueResultant (fuelY fuelD fuelX : ℕ) (f g : CPolyG (QFunNZG ℚ)) (Dder : QFunNZG ℚ)
    (D : CPolyG ℚ) : CPolyG ℚ :=
  let nNodes := cdegG f * cdegG D + 1                        -- `deg_Z R ≤ n · deg_X D`
  let pts : List (ℚ × ℚ) := (List.range (nNodes + 1)).map (fun k =>
    let z : ℚ := (k : ℚ)
    (z, cresultantG fuelX (resYAtNode fuelY fuelD f g Dder z) D))
  cinterpolateG pts

end CPolyG

end DeepWiki.SymbolicIntegration
