import DeepWiki.CAlgebra.Diff.Derivative
import DeepWiki.CAlgebra.Frac.Field
import DeepWiki.Algebra.RatFuncDerivation

/-! # The formal derivative of canonical fractions

The computable quotient-rule derivative of `DenseFrac R`, exposed through Mathlib's
differential-algebra interface as a **scoped** `Differential (DenseFrac R)` instance
(`open scoped FormalDiff`), with the `′`-satellites and the bridge into `RatFunc.deriv`.
The raw quotient rule is `fracDeriv`; `f′` is the public spelling, and it computes. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

namespace DenseFrac

open scoped Differential FormalDiff

/-- The computable quotient-rule derivative of a canonical fraction (implementation; the
public spelling is `f′` via the scoped `Differential` instance). -/
def fracDeriv (f : DenseFrac R) : DenseFrac R :=
  normalize (f.num′ * f.den.toPoly - f.num * f.den.toPoly′) (f.den.toPoly ^ 2)

/-- The quotient rule commutes with the denotation:
`toRatFunc (fracDeriv f) = RatFunc.deriv (toRatFunc f)`. -/
theorem toRatFunc_fracDeriv (f : DenseFrac R) :
    toRatFunc (fracDeriv f) = RatFunc.deriv (toRatFunc f) := by
  rw [fracDeriv, toRatFunc_normalize, toRatFunc,
    RatFunc.deriv_div (toPolynomial_ne_zero f.den.ne_zero)]
  have hpow : toPolynomial (f.den.toPoly ^ 2) = (toPolynomial f.den.toPoly) ^ 2 := by
    simpa using map_pow (equiv (R := R)) f.den.toPoly 2
  rw [toPolynomial_sub, toPolynomial_mul, toPolynomial_mul, toPolynomial_deriv,
    toPolynomial_deriv, hpow]
  simp only [map_sub, map_mul, map_pow]

/-- The quotient rule restricts to the formal derivative on embedded polynomials. -/
theorem fracDeriv_ofPoly (p : DensePoly R) :
    fracDeriv (ofPoly p) = ofPoly (p′) :=
  toRatFunc_injective (by
    rw [toRatFunc_fracDeriv, toRatFunc_ofPoly, toRatFunc_ofPoly, RatFunc.deriv_algebraMap,
      toPolynomial_deriv])

/-- Additivity of the quotient rule. -/
theorem fracDeriv_add (a b : DenseFrac R) :
    fracDeriv (a + b) = fracDeriv a + fracDeriv b :=
  toRatFunc_injective (by
    rw [toRatFunc_fracDeriv, toRatFunc_add, RatFunc.deriv_add, toRatFunc_add,
      toRatFunc_fracDeriv, toRatFunc_fracDeriv])

/-- Leibniz rule for the quotient rule. -/
theorem fracDeriv_mul (a b : DenseFrac R) :
    fracDeriv (a * b) = a * fracDeriv b + b * fracDeriv a :=
  toRatFunc_injective (by
    rw [toRatFunc_fracDeriv, toRatFunc_mul, RatFunc.deriv_mul, toRatFunc_add,
      toRatFunc_mul, toRatFunc_mul, toRatFunc_fracDeriv, toRatFunc_fracDeriv])

/-- Integer constants have zero derivative. -/
theorem fracDeriv_intCast (n : ℤ) : fracDeriv ((n : ℤ) : DenseFrac R) = 0 :=
  toRatFunc_injective (by
    have hint : toRatFunc ((n : ℤ) : DenseFrac R) = ((n : ℤ) : RatFunc R) :=
      map_intCast (equivRatFunc (R := R)) n
    rw [toRatFunc_fracDeriv, hint, RatFunc.deriv_intCast, toRatFunc_zero])

/-- The unit has zero derivative. -/
theorem fracDeriv_one : fracDeriv (1 : DenseFrac R) = 0 :=
  toRatFunc_injective (by
    have h1 : RatFunc.deriv (1 : RatFunc R) = 0 := by
      have := RatFunc.deriv_algebraMap (K := R) 1
      simpa using this
    rw [toRatFunc_fracDeriv, toRatFunc_one, h1, toRatFunc_zero])

end DenseFrac

end DeepWiki.CAlgebra

namespace FormalDiff

/-- The quotient rule as the differential structure of `DenseFrac R` (scoped, matching the
`DensePoly` and `RatFunc` formal-derivative instances; `f′` computes). -/
scoped instance {R : Type u} [Field R] [DecidableEq R]
    [DeepWiki.CAlgebra.DensePolyGcd R] :
    Differential (DeepWiki.CAlgebra.DenseFrac R) where
  deriv :=
    letI : Algebra ℤ (DeepWiki.CAlgebra.DenseFrac R) := Ring.toIntAlgebra _
    { toFun := DeepWiki.CAlgebra.DenseFrac.fracDeriv
      map_add' := DeepWiki.CAlgebra.DenseFrac.fracDeriv_add
      map_smul' := fun n f => by
        show DeepWiki.CAlgebra.DenseFrac.fracDeriv (n • f)
          = n • DeepWiki.CAlgebra.DenseFrac.fracDeriv f
        rw [zsmul_eq_mul, zsmul_eq_mul, DeepWiki.CAlgebra.DenseFrac.fracDeriv_mul,
          DeepWiki.CAlgebra.DenseFrac.fracDeriv_intCast, mul_zero, add_zero]
      map_one_eq_zero' := DeepWiki.CAlgebra.DenseFrac.fracDeriv_one
      leibniz' := fun a b => by
        show DeepWiki.CAlgebra.DenseFrac.fracDeriv (a * b)
          = a • DeepWiki.CAlgebra.DenseFrac.fracDeriv b
            + b • DeepWiki.CAlgebra.DenseFrac.fracDeriv a
        rw [DeepWiki.CAlgebra.DenseFrac.fracDeriv_mul, smul_eq_mul, smul_eq_mul] }

end FormalDiff

namespace DeepWiki.CAlgebra

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

namespace DenseFrac

open scoped Differential FormalDiff

/-- The scoped `′` on `DenseFrac R` is the computable quotient rule. -/
@[simp] theorem differential_apply (f : DenseFrac R) : f′ = fracDeriv f := rfl

/-- The denotation is a differential morphism: `toRatFunc (f′) = (toRatFunc f)′`. -/
@[simp] theorem toRatFunc_deriv (f : DenseFrac R) :
    toRatFunc (f′) = (toRatFunc f)′ := by
  rw [differential_apply, RatFunc.differential_apply, toRatFunc_fracDeriv]

end DenseFrac

end DeepWiki.CAlgebra
