import DeepWiki.ComputableAlgebra.FracReduce
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.ExampleData

/-! # Tower-level demos for the `CFrac` gcd-cancel reducer `CFrac.reduce`
`CFrac.reduce` divides a fraction's numerator and denominator by their monic gcd, preserving the field value
(`CFrac.toRatFunc_reduce`). These examples show it shrinks a swollen product and lets a hyperexponential
residual solver see a reduced constant residual. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration


/-! ### Product-size example: `CFrac.reduce` shrinks an unreduced product

`mul (t/(t−1)) ((t−1)/t)` stores the constant `1` as `(t·(t−1))/((t−1)·t)` (num/den length 3);
`CFrac.reduce` cancels to `1/1` (length 1) with the field value unchanged. -/

namespace CFrac

/-- The fraction `t/(t−1) ∈ DenseFrac ℚ` (numerator `[0,1]`, denominator `[−1,1]`). -/
def swellA : DenseFrac ℚ := CFrac.ofFraction [(0 : ℚ), 1] [(-1 : ℚ), 1] (by cfrac_nonzero)

/-- The fraction `(t−1)/t ∈ DenseFrac ℚ` (numerator `[−1,1]`, denominator `[0,1]`), the reciprocal of
`swellA`. -/
def swellB : DenseFrac ℚ := CFrac.ofFraction [(-1 : ℚ), 1] [(0 : ℚ), 1] (by cfrac_nonzero)

/-- The unreduced product `swellA · swellB = (t·(t−1))/((t−1)·t)` via `mul`: both num and den are
`t²−t` (length 3) though the value is `1`. -/
def swellProd : DenseFrac ℚ := mul swellA swellB

/-- The unreduced product `swellProd` has numerator length 3. -/
theorem swellProd_num_length : (DensePoly.cnorm (CFrac.num swellProd) : List ℚ).length = 3 := by ccompute

/-- The unreduced product `swellProd` has denominator length 3. -/
theorem swellProd_den_length : (DensePoly.cnorm (CFrac.den swellProd) : List ℚ).length = 3 := by ccompute

/-- `CFrac.reduce` shrinks the swollen product's numerator to length 1. -/
theorem swellProd_reduced_num_length :
    (DensePoly.cnorm (CFrac.num (CFrac.reduce swellProd)) : List ℚ).length = 1 := by ccompute

/-- `CFrac.reduce` shrinks the swollen product's denominator to length 1. -/
theorem swellProd_reduced_den_length :
    (DensePoly.cnorm (CFrac.den (CFrac.reduce swellProd)) : List ℚ).length = 1 := by ccompute

/-- The reduced product `CFrac.reduce swellProd` has nonzero numerator (`cisZero` is `false`). -/
theorem swellProd_reduced_num_nonzero :
    DensePoly.cisZero (CFrac.num (CFrac.reduce swellProd)) = false := by ccompute

/-- `CFrac.reduce` preserves the field value: `toRatFunc (CFrac.reduce swellProd) = toRatFunc swellProd`. -/
theorem swellProd_value_preserved :
    toRatFunc (CFrac.reduce swellProd) = toRatFunc swellProd :=
  CFrac.toRatFunc_reduce swellProd

/-! #### `CFrac.reduce` preserves the zero test

Since `CFrac.reduce` preserves the field value, it preserves the zero test `isZero` (theorem
`CFrac.isZero_reduce`): a reduced fraction tests zero exactly when the original does. -/

#print axioms swellProd_value_preserved
#print axioms CFrac.isZero_reduce

end CFrac

/-! ### Sparse specialization: the same reducer selects sparse polynomial capabilities -/

namespace CFrac

/-- File-local reducible sparse fraction `(x² - 1)/(x² + 2x - 3)`. -/
private def sparseSwellFrac : SparseFrac ℚ :=
  CFrac.ofFraction
    (CPoly.SparsePoly.ofList [(0, -1), (2, 1)])
    (CPoly.SparsePoly.ofList [(0, -3), (1, 2), (2, 1)])
    (by ccompute)

example :
    CPolyEngine.cdeg (CFrac.num (CFrac.reduce sparseSwellFrac)) = 1 := by
  ccompute

end CFrac

/-! ### Residual-solver example: `CFrac.reduce` exposes a constant residual

A residual that is the value `1` stored as `(2x)/(2x)` makes `crischDESolve 0 R` return `none`
(`Rstuck_unreduced_returns_none`); after `CFrac.reduce` collapses it to `1/1` the base solve succeeds,
recovering `∫1 = x` (`Rstuck_reduced_solves`). The obstruction is representational. -/

namespace CFrac

open DensePoly

/-! #### The unreduced and reduced residual cases -/

/-- The residual `1 ∈ ℚ(x)` stored unreduced as `(2x)/(2x)` via `mul (2x/1) (1/(2x))` (num and den
both length 2). -/
def Rstuck : DenseFrac ℚ :=
  mul nLvl1TwoX (CFrac.ofFraction [CCommRing.one] [(0 : ℚ), (2 : ℚ)] (by cfrac_nonzero))

/-- `Rstuck` is the value `1`: `isZero (Rstuck − 1) = true`. -/
theorem Rstuck_eq_one : CCommRing.isZero (CField.sub Rstuck (CCommRing.one : DenseFrac ℚ)) = true := by
  ccompute

/-- `Rstuck`'s stored denominator is swollen: length 2 (`2x`, not the reduced `1`). -/
theorem Rstuck_den_swollen : (DensePoly.cnorm (CFrac.den Rstuck) : List ℚ).length = 2 := by ccompute

/-- The unreduced residual makes `crischDESolve 0 Rstuck` return `none` even though `Rstuck = 1`,
because the stored denominator is the spurious factor `2x`. -/
theorem Rstuck_unreduced_returns_none :
    CRischField.crischDESolve (CCommRing.zero : DenseFrac ℚ) Rstuck = none := by ccompute

/-- The reduced residual solves: `crischDESolve 0 (CFrac.reduce Rstuck)` returns `some y` with `y = x`,
recovering `∫1 = x`. -/
theorem Rstuck_reduced_solves :
    (match CRischField.crischDESolve (CCommRing.zero : DenseFrac ℚ) (CFrac.reduce Rstuck) with
      | some y => CCommRing.isZero (CField.sub y nLvl1X)
      | none => false) = true := by ccompute

#print axioms Rstuck_unreduced_returns_none
#print axioms Rstuck_reduced_solves

end CFrac

end DeepWiki.SymbolicIntegration
