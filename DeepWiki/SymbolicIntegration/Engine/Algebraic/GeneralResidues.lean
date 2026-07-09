import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicResiduesExamples
import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgFunctionField
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # Algebraic-function residues for arbitrary curves: the full double resultant

The residue resultant `R(Z) = res_X(res_Y(Z·D'(X) − g(X, Y), F(X, Y)), D(X))` for an arbitrary monic
plane curve `F(x, y) = 0` (`genResidueResultant`, by evaluate-`Z`-nodes + Lagrange interpolation over
`K(x) = CFrac ℚ`), generalizing the hyperelliptic norm shortcut of `cAlgResidueResultant`; the roots of
`R` are the residues of `(g/D) dx` at its simple finite poles. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### Reading a `K(x)`-value that is a polynomial back as `K[x] = DensePoly ℚ`

The inner `res_Y` lands in `α = K(x) = CFrac ℚ`. When `F` is monic in `y` the resultant is a genuine
*polynomial* in `x`, so the `CFrac ℚ` value is `numerator/denominator` with the denominator a nonzero
constant (the engine keeps fractions unreduced, so the constant may be any nonzero scalar `c`, not
literally `1`). `qToPolyQ` recovers the `ℚ[x]`-polynomial by the exact division `numerator / denominator`
(`cdivWf` over ℚ): when `denominator ∣ numerator` this is the polynomial quotient, here `cscale (c⁻¹)`. -/

/-- `qToPolyQ v = numerator(v) / denominator(v)` (`cdivWf` over ℚ): read a `CFrac ℚ` value as a
`ℚ[x]`-polynomial. Faithful exactly when `denominator(v) ∣ numerator(v)` — true for the inner
`res_Y` against a `y`-monic `F`, which is a polynomial in `x` with a constant denominator. -/
def qToPolyQ (v : CFrac ℚ) : DensePoly ℚ :=
  cdivWf v.1.1 v.1.2

/-! ### The inner `res_Y(Z·D' − g, F)` at a rational `Z`-node -/

/-- `zDderMinus g Dder z`: the `y`-polynomial `z·D'(x) − g(x, y)` at a rational node `z` — the
constant-in-`y` term `z·D'(x)` (`qxOfNum [z] · Dder`, a singleton `DensePoly`) minus `g`. Its only
`Z`-dependent coefficient is the `y⁰` one, so `res_Y` of this against `F` has `Z`-degree
`≤ deg_y F = n`. `Dder = D'(x) ∈ K(x)` is supplied by the caller. -/
def zDderMinus (g : DensePoly (CFrac ℚ)) (Dder : CFrac ℚ) (z : ℚ) : DensePoly (CFrac ℚ) :=
  csub [CCommRing.mul (qxOfNum [z]) Dder] g

/-- `resYAtNode f g Dder z = res_Y(z·D'(X) − g(X, Y), F(X, Y))` at the rational node `Z = z`,
read as a `ℚ[X]`-polynomial: the resultant in `y` (`cresultantG fuelY` over the field
`α = CFrac ℚ`) of `zDderMinus g Dder z` against the monic curve `f`, recovered as `DensePoly ℚ` by
`qToPolyQ`. The general-curve replacement for the `n = 2` norm `(z·D' − g₀)² − g₁²·ρ`. -/
def resYAtNode (f g : DensePoly (CFrac ℚ)) (Dder : CFrac ℚ) (z : ℚ) : DensePoly ℚ :=
  qToPolyQ (cresultantWf (zDderMinus g Dder z) f)

/-! ### The full general-`F` residue resultant `R(Z) = res_X(res_Y(Z·D' − g, F), D)`

Assemble the outer `resultant_X` over `ℚ` by the evaluate-`Z`-nodes plus Lagrange-interpolate template
of `cResidueResultantTower` / `cAlgResidueResultant`: for each rational node `z`, the inner resultant
`resYAtNode` gives the `ℚ[x]`-polynomial `res_Y(z·D' − g, F)(x)`, then `res_X(that, D)` (`cresultantG`
over ℚ) gives the value `R(z) ∈ ℚ`; interpolating the points `(z, R(z))` recovers `R(Z) ∈ ℚ[Z]`.

The `Z`-degree bound is `deg_Z R ≤ n · deg_X D`: `res_Y(Z·D' − g, F)` is degree `≤ n = deg_y F`
in `Z` (only the `y⁰` coefficient
`Z·D' − g₀` carries `Z`, and the resultant against the degree-`n` `F` is degree `n` in `F`'s argument's
coefficients). The outer `res_X(·, D)` is `∏` over the `deg_X D` roots of `D`, each contributing a
`res_Y` factor of `Z`-degree `≤ n`, so `deg_Z R ≤ n · deg_X D`. Hence `n · deg_X D + 1` nodes are exact
(the hyperelliptic `n = 2` gives `2·deg D`, matching `cAlgResidueResultant`). -/

/-- The general-curve algebraic-residue resultant `genResidueResultant f g Dder D = R(Z) ∈ ℚ[Z]` for an
arbitrary monic curve `F = f`: the full double resultant `R(Z) = res_X(res_Y(Z·D'(X) − g(X, Y), F(X, Y)),
D(X))`, in the residue indeterminate `Z`. Computed by evaluation + interpolation: for nodes
`z = 0, …, n·deg_X D`, the inner `res_Y` (`resYAtNode`) gives `res_Y(z·D' − g, F)`, then `res_X(·, D)`
gives `R(z) ∈ ℚ`, and `cinterpolate` recovers `R(Z)`; `deg_Z R ≤ n·deg_X D` (`n = deg_y f`). Generalizes
`cAlgResidueResultant`'s hyperelliptic norm shortcut. `Dder = D'(x) ∈ K(x)` supplied by the caller. -/
def genResidueResultant (f g : DensePoly (CFrac ℚ)) (Dder : CFrac ℚ)
    (D : DensePoly ℚ) : DensePoly ℚ :=
  let nNodes := cdeg f * cdeg D + 1                        -- `deg_Z R ≤ n · deg_X D`
  let pts : List (ℚ × ℚ) := (List.range (nNodes + 1)).map (fun k =>
    let z : ℚ := (k : ℚ)
    (z, cresultantWf (resYAtNode f g Dder z) D))
  cinterpolate pts

end DensePoly

/-! ### Example: the trigonal curve `F = y³ + x·y + x` (`n = 3`)

A non-hyperelliptic cubic curve over `K(x) = CFrac ℚ`. With `g = y` and `D = x − 1` (one simple pole at
`x = 1`), the residue of `(y/D) dx` at a place `(x₀, y₀)` is `y₀`, so the residues are the roots of
`F(1, y) = y³ + y + 1` and `R(Z) = F(1, Z) = Z³ + Z + 1`. The inner elimination is the full bivariate
`res_Y`, giving a residue that depends on the sheet `y₀`. -/

open DensePoly

/-- The trigonal curve `F = y³ + x·y + x ∈ K(x)[y]` as `DensePoly (CFrac ℚ)` `[x, x, 0, 1]` — the `n = 3`
non-hyperelliptic curve. -/
def genResTrigF : DensePoly (CFrac ℚ) :=
  [qxOfNum [0, 1], qxOfNum [0, 1], CCommRing.zero, CCommRing.one]

/-- The bivariate numerator `g = y` on the trigonal curve (`DensePoly (CFrac ℚ)` `[0, 1]`); its residue
`y₀/D'` depends on the sheet, so `res_Y` cannot collapse to a norm. -/
def genResTrig : DensePoly (CFrac ℚ) := [CCommRing.zero, CCommRing.one]

/-- The denominator `D = x − 1` (`DensePoly ℚ` `[−1, 1]`): one simple pole at `x = 1`. -/
def genResTrigD : DensePoly ℚ := [-1, 1]

/-- The denominator derivative `D'(x) = 1 ∈ K(x)` (`qxOfNum [1]`). -/
def genResTrigDder : CFrac ℚ := qxOfNum [1]

/-- The computed general residue resultant `R(Z)` for `∫ (y/(x−1)) dx` on `y³ + xy + x = 0`. -/
def genResTrigR : DensePoly ℚ :=
  genResidueResultant genResTrigF genResTrig genResTrigDder genResTrigD

/-- The expected `R(Z) = F(1, Z) = Z³ + Z + 1` (low→high in `Z`, `[1, 1, 0, 1]`): the residues are the
three roots `y₀` of the curve fiber `F(1, y) = y³ + y + 1`. -/
def genResTrigExpected : DensePoly ℚ := [1, 1, 0, 1]

/-- The full double resultant on the trigonal cubic: for `∫ (y/(x − 1)) dx` on the non-hyperelliptic
`y³ + xy + x = 0` (`n = 3`), `genResidueResultant` produces `R(Z) = Z³ + Z + 1 = F(1, Z)`, the curve
fiber over the pole `x = 1`, via `cisZero` of `R − (Z³ + Z + 1)`. -/
theorem genResTrig_resultant_eq :
    cisZero (csub genResTrigR genResTrigExpected) = true := by native_decide

/-- The residues are the roots of `F(1, Z)`: `Z = 0` is not a residue (`cIsResidue R 0 = false`), matching
`R = F(1, Z) = Z³ + Z + 1` whose roots are the three `y`-values over the pole `x = 1`. -/
theorem genResTrig_zero_not_residue :
    cIsResidue genResTrigR (0 : ℚ) = false := by native_decide

/-! ### Example: trigonal `g = 1` (constant in `y`) — residue `1` on all three sheets

For the same trigonal curve with `g = 1` and `D = x − 1`, the residue at each of the three places above
`x = 1` is the same `g/D' = 1`, so `R(Z) = (Z − 1)³` (a triple root at the common residue `1`). -/

/-- The constant-in-`y` numerator `g = 1` on the trigonal curve (`DensePoly (CFrac ℚ)` `[1]`): `f = 1/D`
has the same residue on every sheet. -/
def genResTrigG1 : DensePoly (CFrac ℚ) := [CCommRing.one]

/-- The computed `R(Z)` for `∫ dx/(x − 1)` on the trigonal curve `y³ + xy + x = 0`. -/
def genResTrigR1 : DensePoly ℚ :=
  genResidueResultant genResTrigF genResTrigG1 genResTrigDder genResTrigD

/-- The expected `R(Z) = (Z − 1)³ = Z³ − 3Z² + 3Z − 1` (low→high, `[−1, 3, −3, 1]`): the common residue
`1` on all three sheets, with multiplicity `n = 3`. -/
def genResTrigExpected1 : DensePoly ℚ := [-1, 3, -3, 1]

/-- The double resultant gives `(Z − 1)³` for the sheet-independent residue: for `∫ dx/(x − 1)` on
`y³ + xy + x = 0` (`g = 1`), `genResidueResultant` produces `R(Z) = (Z − 1)³`, the residue `1` repeated
once per sheet, via `cisZero` of `R − (Z − 1)³`. -/
theorem genResTrig1_resultant_eq :
    cisZero (csub genResTrigR1 genResTrigExpected1) = true := by native_decide

/-- The common residue `1` is a root of `R`: `cIsResidue R 1 = true` for `R(Z) = (Z − 1)³`. -/
theorem genResTrig1_residue_one :
    cIsResidue genResTrigR1 (1 : ℚ) = true := by native_decide

/-! ### Conservativity: hyperelliptic `F = y² − x` reproduces `cAlgResidueResultant`

On the simple radical case `y² = x` with `g = y`, `D = x² − x`, the general `genResidueResultant` (full
`res_Y`) and the dedicated hyperelliptic `cAlgResidueResultant` (norm `(Z·D' − g₀)² − g₁²·ρ`) both give
`R(Z) = Z⁴ − Z²`: the general double resultant contains the hyperelliptic norm as the `n = 2` case. -/

/-- The hyperelliptic curve `F = y² − x ∈ K(x)[y]` as a general-carrier polynomial (`DensePoly (CFrac ℚ)`
`[−x, 0, 1]`, `ρ = x`) — the `cAlgResidueResultant` example `y = √x`, as a `genResidueResultant` curve. -/
def genResHypF : DensePoly (CFrac ℚ) := [qxOfNum [0, -1], CCommRing.zero, CCommRing.one]

/-- The numerator `g = y` on `y² = x` (`DensePoly (CFrac ℚ)` `[0, 1]`; `g₀ = 0`, `g₁ = 1`). -/
def genResHyp : DensePoly (CFrac ℚ) := [CCommRing.zero, CCommRing.one]

/-- The denominator `D = x² − x ∈ ℚ[x]` (`[0, −1, 1]`) and its derivative `D' = 2x − 1 ∈ K(x)`
(`qxOfNum [−1, 2]`). -/
def genResHypD : DensePoly ℚ := [0, -1, 1]

/-- `D'(x) = 2x − 1 ∈ K(x)` for the hyperelliptic conservativity check. -/
def genResHypDder : CFrac ℚ := qxOfNum [-1, 2]

/-- Conservativity: the general double resultant reproduces the hyperelliptic norm resultant. On `y² = x`
with `g = y`, `D = x² − x`, the general `genResidueResultant` equals the dedicated `cAlgResidueResultant`
(both `R(Z) = Z⁴ − Z²`), via `cisZero` of their difference. -/
theorem genResHyp_conservativity :
    cisZero (csub
      (genResidueResultant genResHypF genResHyp genResHypDder genResHypD)
      (cAlgResidueResultant algResExX_D algResExX_rho algResExX_g0 algResExX_g1)) = true := by
  native_decide

example : cisZero (csub
    (genResidueResultant genResTrigF genResTrig genResTrigDder genResTrigD)
    [1, 1, 0, 1]) = true := by native_decide

/-! ### Related pieces

The residue resultant `R(Z)` computed here feeds the divisor construction over the integral basis,
the principal-divisor/torsion test, and the algebraic rational part. -/

end DeepWiki.SymbolicIntegration
