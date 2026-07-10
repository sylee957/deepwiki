import DeepWiki.ComputableAlgebra.FracReduce
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.ExampleData

/-! # Tower-level demos for the `CFrac` gcd-cancel reducer `qReduce`
`qReduce` divides a fraction's numerator and denominator by their monic gcd, preserving the field value
(`toRatFunc_qReduce`). These examples show it shrinks a swollen product and lets a hyperexponential
residual solver see a reduced constant residual. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration


/-! ### Product-size example: `qReduce` shrinks an unreduced product

`qmulNZ (t/(t−1)) ((t−1)/t)` stores the constant `1` as `(t·(t−1))/((t−1)·t)` (num/den length 3);
`qReduce` cancels to `1/1` (length 1) with the field value unchanged. -/

namespace CFrac

/-- The fraction `t/(t−1) ∈ DenseFrac ℚ` (numerator `[0,1]`, denominator `[−1,1]`). -/
def swellA : DenseFrac ℚ := CFrac.ofFraction [(0 : ℚ), 1] [(-1 : ℚ), 1] (by ccompute)

/-- The fraction `(t−1)/t ∈ DenseFrac ℚ` (numerator `[−1,1]`, denominator `[0,1]`), the reciprocal of
`swellA`. -/
def swellB : DenseFrac ℚ := CFrac.ofFraction [(-1 : ℚ), 1] [(0 : ℚ), 1] (by ccompute)

/-- The unreduced product `swellA · swellB = (t·(t−1))/((t−1)·t)` via `qmulNZ`: both num and den are
`t²−t` (length 3) though the value is `1`. -/
def swellProd : DenseFrac ℚ := qmulNZ swellA swellB

/-- The unreduced product `swellProd` has numerator length 3. -/
theorem swellProd_num_length : (DensePoly.cnorm swellProd.num : List ℚ).length = 3 := by ccompute

/-- The unreduced product `swellProd` has denominator length 3. -/
theorem swellProd_den_length : (DensePoly.cnorm swellProd.den : List ℚ).length = 3 := by ccompute

/-- `qReduce` shrinks the swollen product's numerator to length 1. -/
theorem swellProd_reduced_num_length :
    (DensePoly.cnorm (qReduce swellProd).num : List ℚ).length = 1 := by ccompute

/-- `qReduce` shrinks the swollen product's denominator to length 1. -/
theorem swellProd_reduced_den_length :
    (DensePoly.cnorm (qReduce swellProd).den : List ℚ).length = 1 := by ccompute

/-- The reduced product `qReduce swellProd` has nonzero numerator (`cisZero` is `false`). -/
theorem swellProd_reduced_num_nonzero :
    DensePoly.cisZero (qReduce swellProd).num = false := by ccompute

/-- `qReduce` preserves the field value: `toRatFunc (qReduce swellProd) = toRatFunc swellProd`. -/
theorem swellProd_value_preserved :
    toRatFunc (qReduce swellProd) = toRatFunc swellProd :=
  toRatFunc_qReduce swellProd

/-! #### `qReduce` preserves the zero test

Since `qReduce` preserves the field value, it preserves the zero test `isZeroNZ` (theorem
`CFrac.isZeroNZ_qReduce`): a reduced fraction tests zero exactly when the original does. -/

#print axioms swellProd_value_preserved
#print axioms CFrac.isZeroNZ_qReduce

end CFrac

/-! ### Residual-solver example: `qReduce` exposes a constant residual

A residual that is the value `1` stored as `(2x)/(2x)` makes `crischDESolve 0 R` return `none`
(`Rstuck_unreduced_returns_none`); after `qReduce` collapses it to `1/1` the base solve succeeds,
recovering `∫1 = x` (`Rstuck_reduced_solves`). The obstruction is representational. -/

namespace CFrac

open DensePoly

/-! #### The unreduced and reduced residual cases -/

/-- The residual `1 ∈ ℚ(x)` stored unreduced as `(2x)/(2x)` via `qmulNZ (2x/1) (1/(2x))` (num and den
both length 2). -/
def Rstuck : DenseFrac ℚ :=
  qmulNZ nLvl1TwoX (CFrac.ofFraction [CCommRing.one] [(0 : ℚ), (2 : ℚ)] (by ccompute))

/-- `Rstuck` is the value `1`: `isZero (Rstuck − 1) = true`. -/
theorem Rstuck_eq_one : CCommRing.isZero (CField.sub Rstuck (CCommRing.one : DenseFrac ℚ)) = true := by
  ccompute

/-- `Rstuck`'s stored denominator is swollen: length 2 (`2x`, not the reduced `1`). -/
theorem Rstuck_den_swollen : (DensePoly.cnorm Rstuck.den : List ℚ).length = 2 := by ccompute

/-- The unreduced residual makes `crischDESolve 0 Rstuck` return `none` even though `Rstuck = 1`,
because the stored denominator is the spurious factor `2x`. -/
theorem Rstuck_unreduced_returns_none :
    CRischField.crischDESolve (CCommRing.zero : DenseFrac ℚ) Rstuck = none := by ccompute

/-- The reduced residual solves: `crischDESolve 0 (qReduce Rstuck)` returns `some y` with `y = x`,
recovering `∫1 = x`. -/
theorem Rstuck_reduced_solves :
    (match CRischField.crischDESolve (CCommRing.zero : DenseFrac ℚ) (qReduce Rstuck) with
      | some y => CCommRing.isZero (CField.sub y nLvl1X)
      | none => false) = true := by ccompute

#print axioms Rstuck_unreduced_returns_none
#print axioms Rstuck_reduced_solves

end CFrac

end DeepWiki.SymbolicIntegration
