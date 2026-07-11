import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicResiduesExamples
import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgFunctionField
import DeepWiki.ComputableAlgebra.FracReduce
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.ComputableAlgebra.PolyResultantDense
import DeepWiki.ComputableAlgebra.PolyInterpolateDense
import DeepWiki.ComputableAlgebra.PolyInterpolateSparse

/-! # Algebraic-function residues for arbitrary curves: the full double resultant

The residue resultant `R(Z) = res_X(res_Y(Z·D'(X) − g(X, Y), F(X, Y)), D(X))` for an arbitrary monic
plane curve `F(x, y) = 0` (`genResidueResultant`, by evaluate-`Z`-nodes + Lagrange interpolation),
generalizing the hyperelliptic norm shortcut of `cAlgResidueResultant`; the roots of `R` are the residues
of `(g/D) dx` at its simple finite poles. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### Reading a `K(x)`-value that is a polynomial back as `K[x] = DensePoly ℚ`

The inner `res_Y` lands in `α = K(x) = DenseFrac ℚ`. When `F` is monic in `y` the resultant is a genuine
*polynomial* in `x`, so the `DenseFrac ℚ` value is `numerator/denominator` with the denominator a nonzero
constant (the engine keeps fractions unreduced, so the constant may be any nonzero scalar `c`, not
literally `1`). `CFrac.polynomialQuotient` recovers the `ℚ[x]`-polynomial through the selected Euclidean
capability: when `denominator ∣ numerator` this is the exact polynomial quotient, here a scalar rescaling. -/

/-! ### The inner `res_Y(Z·D' − g, F)` at a rational `Z`-node -/

/-- `zDderMinus g Dder z`: the `y`-polynomial `z·D'(x) − g(x, y)` at a rational node `z` — the
constant-in-`y` term `z·D'(x)` (`CFrac.ofPoly [z] · Dder`, a singleton `DensePoly`) minus `g`. Its only
`Z`-dependent coefficient is the `y⁰` one, so `res_Y` of this against `F` has `Z`-degree
`≤ deg_y F = n`. `Dder = D'(x) ∈ K(x)` is supplied by the caller. -/
def zDderMinus
    {F : (α : Type) → [CField α] → Type} {X Y : Type → Type}
    [CPoly X] [CPolyEngine X] [CFrac F X] [LawfulCFrac F X] [CFieldDomain ℚ X]
    [CPoly Y] [CPolyEngine Y]
    (g : Y (F ℚ)) (Dder : F ℚ) (z : ℚ) : Y (F ℚ) :=
  CPolyEngine.sub
    (CPolyEngine.ofCoeffList
      [CCommRing.mul (CFrac.ofScalar (F := F) z) Dder]) g

example :
    let ofList : List (DenseFrac ℚ) → CPoly.SparsePoly (DenseFrac ℚ) := CPolyEngine.ofCoeffList
    let g := ofList [CFrac.ofPoly [1], CCommRing.one]
    let r := zDderMinus g (CFrac.ofPoly [2]) (3 : ℚ)
    CCommRing.isZero (CField.sub (CPoly.coeff r 0) (CFrac.ofPoly [5])) = true ∧
      CCommRing.isZero (CField.sub (CPoly.coeff r 1)
        (CCommRing.neg (CCommRing.one : DenseFrac ℚ))) = true := by
  native_decide

/-- `resYAtNode f g Dder z = res_Y(z·D'(X) − g(X, Y), F(X, Y))` at the rational node `Z = z`,
read as a `ℚ[X]`-polynomial: the resultant in `y` over the field `α = DenseFrac ℚ` of
`zDderMinus g Dder z` against the monic curve `f`, recovered through
`CFrac.polynomialQuotient`. The general-curve replacement for the `n = 2` norm
`(z·D' − g₀)² − g₁²·ρ`. -/
def resYAtNode
    {F : (α : Type) → [CField α] → Type} {X Y : Type → Type}
    [CPoly X] [CPolyEngine X] [CPolyEuclidean X]
    [CFrac F X] [LawfulCFrac F X] [CFieldDomain ℚ X]
    [CPoly Y] [CPolyEngine Y] [CPolyResultant Y]
    (f g : Y (F ℚ)) (Dder : F ℚ) (z : ℚ) : X ℚ :=
  CFrac.polynomialQuotient (CPolyResultant.compute (zDderMinus g Dder z) f)

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

/-- The general-curve algebraic-residue resultant with independently selected base, curve, fraction,
and interpolation representations. -/
def genResidueResultantWith
    {F : (α : Type) → [CField α] → Type} {X Y Q : Type → Type}
    [CPoly X] [CPolyEngine X] [CPolyEuclidean X] [CPolyResultant X]
    [CFrac F X] [LawfulCFrac F X] [CFieldDomain ℚ X]
    [CPoly Y] [CPolyEngine Y] [CPolyResultant Y]
    [CPoly Q] [CPolyEngine Q] [CPolyInterpolate Q]
    (f g : Y (F ℚ)) (Dder : F ℚ) (D : X ℚ) : Q ℚ :=
  let nNodes := CPolyEngine.cdeg f * CPolyEngine.cdeg D + 1
  let pts : List (ℚ × ℚ) := (List.range (nNodes + 1)).map (fun k =>
    let z : ℚ := (k : ℚ)
    (z, CPolyResultant.compute (resYAtNode f g Dder z) D))
  CPoly.interpolate pts

/-- The dense general-curve algebraic-residue resultant `genResidueResultant f g Dder D = R(Z) ∈ ℚ[Z]` for an
arbitrary monic curve `F = f`: the full double resultant `R(Z) = res_X(res_Y(Z·D'(X) − g(X, Y), F(X, Y)),
D(X))`, in the residue indeterminate `Z`. Computed by evaluation + interpolation: for nodes
`z = 0, …, n·deg_X D`, the inner `res_Y` (`resYAtNode`) gives `res_Y(z·D' − g, F)`, then `res_X(·, D)`
gives `R(z) ∈ ℚ`, and `cinterpolate` recovers `R(Z)`; `deg_Z R ≤ n·deg_X D` (`n = deg_y f`). Generalizes
`cAlgResidueResultant`'s hyperelliptic norm shortcut. `Dder = D'(x) ∈ K(x)` supplied by the caller. -/
def genResidueResultant [CPolyResultant DensePoly]
    (f g : DensePoly (DenseFrac ℚ)) (Dder : DenseFrac ℚ)
    (D : DensePoly ℚ) : DensePoly ℚ :=
  genResidueResultantWith (F := DenseFrac) (X := DensePoly) (Y := DensePoly) (Q := DensePoly)
    f g Dder D

end DensePoly

/-! ### Example: the trigonal curve `F = y³ + x·y + x` (`n = 3`)

A non-hyperelliptic cubic curve over `K(x) = DenseFrac ℚ`. With `g = y` and `D = x − 1` (one simple pole at
`x = 1`), the residue of `(y/D) dx` at a place `(x₀, y₀)` is `y₀`, so the residues are the roots of
`F(1, y) = y³ + y + 1` and `R(Z) = F(1, Z) = Z³ + Z + 1`. The inner elimination is the full bivariate
`res_Y`, giving a residue that depends on the sheet `y₀`. -/

open DensePoly

/-- The trigonal curve `F = y³ + x·y + x ∈ K(x)[y]` as `DensePoly (DenseFrac ℚ)` `[x, x, 0, 1]` — the `n = 3`
non-hyperelliptic curve. -/
def genResTrigF : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [0, 1], CFrac.ofPoly [0, 1], CCommRing.zero, CCommRing.one]

/-- The bivariate numerator `g = y` on the trigonal curve (`DensePoly (DenseFrac ℚ)` `[0, 1]`); its residue
`y₀/D'` depends on the sheet, so `res_Y` cannot collapse to a norm. -/
def genResTrig : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CCommRing.one]

/-- The denominator `D = x − 1` (`DensePoly ℚ` `[−1, 1]`): one simple pole at `x = 1`. -/
def genResTrigD : DensePoly ℚ := [-1, 1]

/-- The denominator derivative `D'(x) = 1 ∈ K(x)` (`CFrac.ofPoly [1]`). -/
def genResTrigDder : DenseFrac ℚ := CFrac.ofPoly [1]

/-- The computed general residue resultant `R(Z)` for `∫ (y/(x−1)) dx` on `y³ + xy + x = 0`. -/
def genResTrigR : DensePoly ℚ :=
  genResidueResultant genResTrigF genResTrig genResTrigDder genResTrigD

/-- The expected `R(Z) = F(1, Z) = Z³ + Z + 1` (low→high in `Z`, `[1, 1, 0, 1]`): the residues are the
three roots `y₀` of the curve fiber `F(1, y) = y³ + y + 1`. -/
def genResTrigExpected : DensePoly ℚ := [1, 1, 0, 1]

/-- The trigonal residue resultant executes end-to-end with sparse base, curve, fraction, and residue
storage. -/
example :
    let x : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(1, 1)]
    let xFrac : SparseFrac ℚ := CFrac.ofPoly x
    let f : CPoly.SparsePoly (SparseFrac ℚ) :=
      CPoly.SparsePoly.ofList [(0, xFrac), (1, xFrac), (3, CCommRing.one)]
    let g : CPoly.SparsePoly (SparseFrac ℚ) :=
      CPoly.SparsePoly.ofList [(1, CCommRing.one)]
    let Dder : SparseFrac ℚ := CFrac.ofPoly (CPoly.one : CPoly.SparsePoly ℚ)
    let D : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, -1), (1, 1)]
    genResidueResultantWith (Q := CPoly.SparsePoly) f g Dder D =
        CPoly.SparsePoly.ofList [(0, 1), (1, 1), (2, 0), (3, 1)] := by
  native_decide

/-- The full double resultant on the trigonal cubic: for `∫ (y/(x − 1)) dx` on the non-hyperelliptic
`y³ + xy + x = 0` (`n = 3`), `genResidueResultant` produces `R(Z) = Z³ + Z + 1 = F(1, Z)`, the curve
fiber over the pole `x = 1`, via `cisZero` of `R − (Z³ + Z + 1)`. -/
theorem genResTrig_resultant_eq :
    cisZero (csub genResTrigR genResTrigExpected) = true := by native_decide

/-- The residues are the roots of `F(1, Z)`: `Z = 0` is not a residue (`CPoly.isRoot R 0 = false`), matching
`R = F(1, Z) = Z³ + Z + 1` whose roots are the three `y`-values over the pole `x = 1`. -/
theorem genResTrig_zero_not_residue :
    CPoly.isRoot genResTrigR (0 : ℚ) = false := by native_decide

/-! ### Example: trigonal `g = 1` (constant in `y`) — residue `1` on all three sheets

For the same trigonal curve with `g = 1` and `D = x − 1`, the residue at each of the three places above
`x = 1` is the same `g/D' = 1`, so `R(Z) = (Z − 1)³` (a triple root at the common residue `1`). -/

/-- The constant-in-`y` numerator `g = 1` on the trigonal curve (`DensePoly (DenseFrac ℚ)` `[1]`): `f = 1/D`
has the same residue on every sheet. -/
def genResTrigG1 : DensePoly (DenseFrac ℚ) := [CCommRing.one]

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

/-- The common residue `1` is a root of `R`: `CPoly.isRoot R 1 = true` for `R(Z) = (Z − 1)³`. -/
theorem genResTrig1_residue_one :
    CPoly.isRoot genResTrigR1 (1 : ℚ) = true := by native_decide

/-! ### Conservativity: hyperelliptic `F = y² − x` reproduces `cAlgResidueResultant`

On the simple radical case `y² = x` with `g = y`, `D = x² − x`, the general `genResidueResultant` (full
`res_Y`) and the dedicated hyperelliptic `cAlgResidueResultant` (norm `(Z·D' − g₀)² − g₁²·ρ`) both give
`R(Z) = Z⁴ − Z²`: the general double resultant contains the hyperelliptic norm as the `n = 2` case. -/

/-- The hyperelliptic curve `F = y² − x ∈ K(x)[y]` as a general-carrier polynomial (`DensePoly (DenseFrac ℚ)`
`[−x, 0, 1]`, `ρ = x`) — the `cAlgResidueResultant` example `y = √x`, as a `genResidueResultant` curve. -/
def genResHypF : DensePoly (DenseFrac ℚ) := [CFrac.ofPoly [0, -1], CCommRing.zero, CCommRing.one]

/-- The numerator `g = y` on `y² = x` (`DensePoly (DenseFrac ℚ)` `[0, 1]`; `g₀ = 0`, `g₁ = 1`). -/
def genResHyp : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CCommRing.one]

/-- The denominator `D = x² − x ∈ ℚ[x]` (`[0, −1, 1]`) and its derivative `D' = 2x − 1 ∈ K(x)`
(`CFrac.ofPoly [−1, 2]`). -/
def genResHypD : DensePoly ℚ := [0, -1, 1]

/-- `D'(x) = 2x − 1 ∈ K(x)` for the hyperelliptic conservativity check. -/
def genResHypDder : DenseFrac ℚ := CFrac.ofPoly [-1, 2]

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
