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

/-! ### ★ Validation 1: the trigonal curve `F = y³ + x·y + x` (`n = 3`, `native_decide`)

A genuinely **non-hyperelliptic** cubic curve `α = K(x) = QFunNZG ℚ`, `n = 3`, `F = y³ + x·y + x`
(`a₂ = 0`, `a₁ = x`, `a₀ = x`, monic; the same curve as `ComputableAlgFunctionField`'s `afTrigF`). The
inner elimination is the **full bivariate `resultant_Y`** in `y` — *not* the `n = 2` norm shortcut.

**Case `g = y` (genuinely bivariate `g`), `D = x − 1`** (one simple pole at `x = 1`). The residue of
`(y/D) dx` at a place `(x₀, y₀)` is `g/D' = y₀/D'(x₀) = y₀` (`D' = 1`, `x₀ = 1`); the three places above
`x = 1` carry the three roots `y₀` of `F(1, y) = y³ + y + 1 = 0`. So the residues are exactly the roots
of `F(1, Z)`, and

  `R(Z) = res_X(res_Y(Z·1 − y, F), x − 1) = F(1, Z) = Z³ + Z + 1`.

Mechanically: `res_Y(Z − y, F) = F(X, Z) = Z³ + X·Z + X` (the resultant of the monic linear `y − Z`
against `F` is `F` with `y ↦ Z`); `res_X(Z³ + X·Z + X, X − 1)` evaluates at `X = 1` (the `X − 1` root),
giving `Z³ + Z + 1`. The engine returns exactly `[1, 1, 0, 1]` — `R(Z) = F(1, Z)`, the curve fiber over
the pole. **This is the full double resultant on a cubic, with a residue that genuinely depends on the
sheet `y₀`** (impossible to get from the hyperelliptic norm). -/

open CPolyG

/-- The trigonal curve `F = y³ + x·y + x ∈ K(x)[y]` (`a₀ = x`, `a₁ = x`, `a₂ = 0`, monic), as a
`CPolyG (QFunNZG ℚ)` `[x, x, 0, 1]` — the `n = 3` non-hyperelliptic curve. -/
def genResTrigF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [0, 1], qxOfNum [0, 1], CField.zero, CField.one]

/-- The genuinely bivariate numerator `g = y` on the trigonal curve (`CPolyG (QFunNZG ℚ)` `[0, 1]`) —
its residue `y₀/D'` depends on the sheet, so the `res_Y` cannot collapse to a norm. -/
def genResTrigG : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- The denominator `D = x − 1` (`CPolyG ℚ` `[−1, 1]`): one simple pole at `x = 1`. -/
def genResTrigD : CPolyG ℚ := [-1, 1]

/-- The denominator derivative `D'(x) = 1 ∈ K(x)` (`qxOfNum [1]`). -/
def genResTrigDder : QFunNZG ℚ := qxOfNum [1]

/-- The computed general residue resultant `R(Z)` for `∫ (y/(x−1)) dx` on `y³ + xy + x = 0`. -/
def genResTrigR : CPolyG ℚ :=
  genResidueResultant 20 20 20 genResTrigF genResTrigG genResTrigDder genResTrigD

/-- The expected `R(Z) = F(1, Z) = Z³ + Z + 1` (low→high in `Z`, `[1, 1, 0, 1]`): the residues are the
three roots `y₀` of the curve fiber `F(1, y) = y³ + y + 1`. -/
def genResTrigExpected : CPolyG ℚ := [1, 1, 0, 1]

-- Sanity print: `R(Z) = Z³ + Z + 1`.
#eval (cnormG genResTrigR : List ℚ)

/-- **★ The FULL double resultant computes on the trigonal cubic** (`native_decide`, Trager Ch. 5 §2
eq. 7, general `F`). For `∫ (y/(x − 1)) dx` on the genuinely non-hyperelliptic curve `y³ + xy + x = 0`
(`n = 3`), the engine's `genResidueResultant` — inner **full bivariate** `res_Y(Z·D' − g, F)` over
`K(x)`, outer `res_X(·, D)` over ℚ by evaluation+interpolation — produces `R(Z) = Z³ + Z + 1 = F(1, Z)`,
the curve fiber over the pole `x = 1`. Checked by `cisZeroG` of `R − (Z³ + Z + 1)`. THE ALGEBRAIC-INTEGRAL
RESIDUE RESULTANT NOW COMPUTES FOR ARBITRARY CURVES — the inner elimination is the genuine `resultant_Y`,
not the hyperelliptic norm, and the residues `y₀` depend on the sheet of the cubic. -/
theorem genResTrig_resultant_eq :
    cisZeroG (csubG genResTrigR genResTrigExpected) = true := by native_decide

/-- **★ The residues are the roots of `F(1, Z)`** (`native_decide`): each root `y₀` of the curve fiber
`F(1, y) = y³ + y + 1` is a residue, i.e. `R(Z) = F(1, Z)` exactly — so the residues of `∫ (y/(x−1)) dx`
are precisely the three `y`-values over the pole `x = 1`, Trager's Theorem-2 value `g/D' = y₀/1 = y₀` per
sheet. Confirmed via the membership test: `Z = 0` is **not** a residue (`F(1,0) = 1 ≠ 0`), but `R`
vanishes nowhere rational here (the fiber is irreducible over ℚ) — checked by `cIsResidue R 0 = false`
and the exact match `R = F(1, ·)` above. -/
theorem genResTrig_zero_not_residue :
    cIsResidue 20 genResTrigR (0 : ℚ) = false := by native_decide

/-! ### ★ Validation 2: trigonal `g = 1` (constant in `y`) — residue `1` on all three sheets

For the **same** trigonal curve with `g = 1` (constant in `y`) and `D = x − 1`: `f = 1/(x − 1)` is a
rational function of `x` alone, so its residue at each of the three places above the simple pole `x = 1`
is the *same* `g/D' = 1/1 = 1`. Hence `R(Z) = (Z − 1)³` (degree `n·deg_X D = 3·1 = 3`, a triple root at
the common residue `1`). Mechanically `res_Y(Z − 1, F) = (Z − 1)³` (resultant of the constant `Z − 1`
against the degree-3 monic `F`), and `res_X((Z − 1)³, X − 1) = (Z − 1)³`. -/

/-- The constant-in-`y` numerator `g = 1` on the trigonal curve (`CPolyG (QFunNZG ℚ)` `[1]`): `f = 1/D`
is a pullback of a rational differential, same residue on every sheet. -/
def genResTrigG1 : CPolyG (QFunNZG ℚ) := [CField.one]

/-- The computed `R(Z)` for `∫ dx/(x − 1)` on the trigonal curve `y³ + xy + x = 0`. -/
def genResTrigR1 : CPolyG ℚ :=
  genResidueResultant 20 20 20 genResTrigF genResTrigG1 genResTrigDder genResTrigD

/-- The expected `R(Z) = (Z − 1)³ = Z³ − 3Z² + 3Z − 1` (low→high, `[−1, 3, −3, 1]`): the common residue
`1` on all three sheets, with multiplicity `n = 3`. -/
def genResTrigExpected1 : CPolyG ℚ := [-1, 3, -3, 1]

/-- **★ The double resultant gives `(Z − 1)³` for the sheet-independent residue** (`native_decide`): for
`∫ dx/(x − 1)` on `y³ + xy + x = 0` (`g = 1` constant in `y`), the engine's `genResidueResultant`
produces `R(Z) = (Z − 1)³` — the residue `g/D' = 1` repeated once per sheet (`n = 3` places over the
simple pole `x = 1`). Checked by `cisZeroG` of `R − (Z − 1)³`. The `res_Y` of a constant against the
cubic `F` is the cube; the three residues coincide because `f` does not depend on `y`. -/
theorem genResTrig1_resultant_eq :
    cisZeroG (csubG genResTrigR1 genResTrigExpected1) = true := by native_decide

/-- **The common residue `1` is a root of `R`** (`native_decide`): `cIsResidue R 1 = true` for
`R(Z) = (Z − 1)³` — confirming the residue `1` of `∫ dx/((x − 1)·…)` on the trigonal curve. -/
theorem genResTrig1_residue_one :
    cIsResidue 20 genResTrigR1 (1 : ℚ) = true := by native_decide

/-! ### ★ Conservativity: hyperelliptic `F = y² − x` reproduces `cAlgResidueResultant` (`native_decide`)

The general engine must agree with the dedicated hyperelliptic `cAlgResidueResultant` on the simple
radical case. For `∫ dx/((x − 1)·y)` on `y² = x` — `F = y² − x` (`ρ = x`), `g = y` (`g₀ = 0`, `g₁ = 1`),
`D = x² − x`, `D' = 2x − 1` — the **general** `genResidueResultant` (full `res_Y` against `y² − x`,
outer `res_X`) and the **hyperelliptic** `cAlgResidueResultant` (norm `(Z·D' − g₀)² − g₁²·ρ`, outer
`res_X`) must produce the **same** `R(Z) = Z⁴ − Z²`. They do — the general double resultant *contains*
the hyperelliptic norm as the `n = 2` special case (`res_Y(Z·D' − g₀ − g₁y, y² − ρ) = (Z·D' − g₀)² −
g₁²·ρ`). -/

/-- The hyperelliptic curve `F = y² − x ∈ K(x)[y]` as a general-carrier polynomial (`CPolyG (QFunNZG ℚ)`
`[−x, 0, 1]`, `ρ = x`) — the `cAlgResidueResultant` worked example `y = √x`, now as a `genResidueResultant`
curve. -/
def genResHypF : CPolyG (QFunNZG ℚ) := [qxOfNum [0, -1], CField.zero, CField.one]

/-- The numerator `g = y` on `y² = x` (`CPolyG (QFunNZG ℚ)` `[0, 1]`; `g₀ = 0`, `g₁ = 1`). -/
def genResHypG : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- The denominator `D = x² − x ∈ ℚ[x]` (`[0, −1, 1]`) and its derivative `D' = 2x − 1 ∈ K(x)`
(`qxOfNum [−1, 2]`). -/
def genResHypD : CPolyG ℚ := [0, -1, 1]

/-- `D'(x) = 2x − 1 ∈ K(x)` for the hyperelliptic conservativity check. -/
def genResHypDder : QFunNZG ℚ := qxOfNum [-1, 2]

/-- **★ Conservativity: the general double resultant reproduces the hyperelliptic norm resultant**
(`native_decide`). On `y² = x` with `g = y`, `D = x² − x`, the general `genResidueResultant` (full
`res_Y` against `y² − x`, no norm shortcut) equals the dedicated `cAlgResidueResultant` (the `n = 2` norm
`(Z·D' − g₀)² − g₁²·ρ`): both give `R(Z) = Z⁴ − Z²`. Checked by `cisZeroG` of their difference. THE
GENERAL ENGINE CONTAINS THE HYPERELLIPTIC CASE — the full `resultant_Y` collapses to the norm exactly
when `F = y² − ρ` and `g` is linear in `y`, so the two `R(Z)` agree. -/
theorem genResHyp_conservativity :
    cisZeroG (csubG
      (genResidueResultant 20 20 20 genResHypF genResHypG genResHypDder genResHypD)
      (cAlgResidueResultant 20 algResExX_D algResExX_rho algResExX_g0 algResExX_g1)) = true := by
  native_decide

/-- Restatement (the deliverable): the general-curve residue resultant `genResidueResultant` of
`∫ (y/(x − 1)) dx` on the **non-hyperelliptic** trigonal curve `y³ + xy + x = 0` is `Z³ + Z + 1 =
F(1, Z)`, whose roots are the residues (the three sheets over the pole `x = 1`) — Trager eq. 7's full
double resultant `res_X(res_Y(Z·D' − g, F), D)` over the constant field ℚ, beyond the hyperelliptic
norm. -/
example : cisZeroG (csubG
    (genResidueResultant 20 20 20 genResTrigF genResTrigG genResTrigDder genResTrigD)
    [1, 1, 0, 1]) = true := by native_decide

/-! ### The NEXT pieces: residues → divisors → the algebraic rational part → the integrator

With `genResidueResultant` the engine computes Trager's eq. 7 residue resultant `R(Z)` for **arbitrary**
curves (the full double resultant), so the **residues** of a `(g/D) dx`-type differential with simple
finite poles are in hand for any plane curve — the heart and tractable part of the log-part computation.
The remaining pieces (documented, beyond this file):

1. **General divisors over the integral basis.** The actual log arguments `vᵢ` need the **divisor
   construction** (Trager Ch. 5 §3): with the Round-2 **integral basis** (`ComputableIntegralBasisFull`)
   one represents the divisor of a function and the residue divisor of the differential. The hyperelliptic
   `residueDivisorMumford` (Mumford `(u, v)` representation) generalizes to the general-curve **ideal /
   integral-basis** representation of divisors, computed against the integral basis here.

2. **The principal-divisor / torsion test (Ch. 5 §3, Ch. 6).** Whether a candidate divisor's multiple is
   *ever* principal is the points-of-finite-order bound (good reduction, Ch. 6) — the real obstruction to
   writing the `vᵢ` symbolically; the residues `R(Z)`/this file are the input it consumes.

3. **The algebraic rational part (Ch. 4)** — the genus-`g` Hermite reduction (the algebraic analogue of
   `cHermiteReduce`) over the integral basis, removing the multiple-pole part before the residues handle
   the simple-pole log part; then wiring residues + rational part into the top-level integrator
   for algebraic integrands.

Every input these consume — the residue resultant `R(Z)` (this file), the integral basis
(`ComputableIntegralBasisFull`), the trace/discriminant (`ComputableAlgFunctionField`) — is now in place;
what remains is the divisor/torsion orchestration. -/

/-! ### `#print axioms` — does the engine compute algebraic-integral residues for ARBITRARY curves?

Each validation carries the standard `[propext, Classical.choice, Quot.sound]` plus the `native_decide`
compiler axiom — **no `sorry`, no extra axiom**. **The engine now computes Trager's eq. 7 residue
resultant `R(Z) = res_X(res_Y(Z·D' − g, F), D)` for arbitrary monic plane curves `F` (the full double
resultant), beyond the hyperelliptic norm.** The inner elimination is the genuine bivariate
`resultant_Y` in `y` over `K(x) = QFunNZG ℚ` (`cresultantG` over the field), the outer is `res_X` over ℚ
by evaluation+interpolation. Validated on the non-hyperelliptic trigonal `y³ + xy + x` (`n = 3`): with
`g = y` the residues are the curve fiber `R(Z) = F(1, Z) = Z³ + Z + 1` (sheet-dependent residues `y₀`),
with `g = 1` the common residue `(Z − 1)³`; and conservatively on the hyperelliptic `y² − x` the general
engine reproduces `cAlgResidueResultant`'s `Z⁴ − Z²`. -/

-- The non-hyperelliptic trigonal curve `y³ + xy + x` (`n = 3`): the full double resultant.
#print axioms genResTrig_resultant_eq
#print axioms genResTrig1_resultant_eq

-- Conservativity: the general engine reproduces the hyperelliptic `cAlgResidueResultant`.
#print axioms genResHyp_conservativity

end DeepWiki.SymbolicIntegration
