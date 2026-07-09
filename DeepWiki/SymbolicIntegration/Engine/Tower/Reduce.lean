import DeepWiki.SymbolicIntegration.Engine.QFunReduce
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.ExampleData

/-! # Tower-level demos for the `QFunNZG` gcd-cancel reducer `qReduce`
`qReduce` divides a fraction's numerator and denominator by their monic gcd, preserving the field value
(`toQFunNZG_qReduce`). These examples show it shrinks a swollen product and lets a hyperexponential
residual solver see a reduced constant residual. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ### Product-size example: `qReduce` shrinks an unreduced product

`qmulNZG (t/(t−1)) ((t−1)/t)` stores the constant `1` as `(t·(t−1))/((t−1)·t)` (num/den length 3);
`qReduce` cancels to `1/1` (length 1) with the field value unchanged. -/

namespace QFunNZG

/-- The fraction `t/(t−1) ∈ QFunNZG ℚ` (numerator `[0,1]`, denominator `[−1,1]`). -/
def swellA : QFunNZG ℚ := ⟨([(0 : ℚ), 1], [(-1 : ℚ), 1]), by native_decide⟩

/-- The fraction `(t−1)/t ∈ QFunNZG ℚ` (numerator `[−1,1]`, denominator `[0,1]`), the reciprocal of
`swellA`. -/
def swellB : QFunNZG ℚ := ⟨([(-1 : ℚ), 1], [(0 : ℚ), 1]), by native_decide⟩

/-- The unreduced product `swellA · swellB = (t·(t−1))/((t−1)·t)` via `qmulNZG`: both num and den are
`t²−t` (length 3) though the value is `1`. -/
def swellProd : QFunNZG ℚ := qmulNZG swellA swellB

/-- The unreduced product `swellProd` has numerator length 3. -/
theorem swellProd_num_length : (CPolyG.cnormG swellProd.1.1 : List ℚ).length = 3 := by native_decide

/-- The unreduced product `swellProd` has denominator length 3. -/
theorem swellProd_den_length : (CPolyG.cnormG swellProd.1.2 : List ℚ).length = 3 := by native_decide

/-- `qReduce` shrinks the swollen product's numerator to length 1. -/
theorem swellProd_reduced_num_length :
    (CPolyG.cnormG (qReduce swellProd).1.1 : List ℚ).length = 1 := by native_decide

/-- `qReduce` shrinks the swollen product's denominator to length 1. -/
theorem swellProd_reduced_den_length :
    (CPolyG.cnormG (qReduce swellProd).1.2 : List ℚ).length = 1 := by native_decide

/-- The reduced product `qReduce swellProd` has nonzero numerator (`cisZeroG` is `false`). -/
theorem swellProd_reduced_num_nonzero :
    CPolyG.cisZeroG (qReduce swellProd).1.1 = false := by native_decide

/-- `qReduce` preserves the field value: `toQFunNZG (qReduce swellProd) = toQFunNZG swellProd`. -/
theorem swellProd_value_preserved :
    toQFunNZG (qReduce swellProd) = toQFunNZG swellProd :=
  toQFunNZG_qReduce swellProd

/-! #### `qReduce` preserves the zero test

Since `qReduce` preserves the field value, it preserves the zero test `isZeroNZG` (theorem
`QFunNZG.isZeroNZG_qReduce`): a reduced fraction tests zero exactly when the original does. -/

#print axioms swellProd_value_preserved
#print axioms isZeroNZG_qReduce

end QFunNZG

/-! ### Residual-solver example: `qReduce` exposes a constant residual

A residual that is the value `1` stored as `(2x)/(2x)` makes `crischDESolve 0 R` return `none`
(`Rstuck_unreduced_returns_none`); after `qReduce` collapses it to `1/1` the base solve succeeds,
recovering `∫1 = x` (`Rstuck_reduced_solves`). The obstruction is representational. -/

namespace QFunNZG

open CPolyG

/-! #### The unreduced and reduced residual cases -/

/-- The residual `1 ∈ ℚ(x)` stored unreduced as `(2x)/(2x)` via `qmulNZG (2x/1) (1/(2x))` (num and den
both length 2). -/
def Rstuck : QFunNZG ℚ :=
  qmulNZG nLvl1TwoX ⟨([CField.one], [(0 : ℚ), (2 : ℚ)]), by native_decide⟩

/-- `Rstuck` is the value `1`: `isZero (Rstuck − 1) = true`. -/
theorem Rstuck_eq_one : CField.isZero (CField.sub Rstuck (CField.one : QFunNZG ℚ)) = true := by
  native_decide

/-- `Rstuck`'s stored denominator is swollen: length 2 (`2x`, not the reduced `1`). -/
theorem Rstuck_den_swollen : (CPolyG.cnormG Rstuck.1.2 : List ℚ).length = 2 := by native_decide

/-- The unreduced residual makes `crischDESolve 0 Rstuck` return `none` even though `Rstuck = 1`,
because the stored denominator is the spurious factor `2x`. -/
theorem Rstuck_unreduced_returns_none :
    CRischField.crischDESolve (CField.zero : QFunNZG ℚ) Rstuck = none := by native_decide

/-- The reduced residual solves: `crischDESolve 0 (qReduce Rstuck)` returns `some y` with `y = x`,
recovering `∫1 = x`. -/
theorem Rstuck_reduced_solves :
    (match CRischField.crischDESolve (CField.zero : QFunNZG ℚ) (qReduce Rstuck) with
      | some y => CField.isZero (CField.sub y nLvl1X)
      | none => false) = true := by native_decide

#print axioms Rstuck_unreduced_returns_none
#print axioms Rstuck_reduced_solves

end QFunNZG

end DeepWiki.SymbolicIntegration
