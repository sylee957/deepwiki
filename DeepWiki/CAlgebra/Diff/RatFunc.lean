import DeepWiki.CAlgebra.Diff.Basic
import DeepWiki.CAlgebra.PartFrac.Basic
import DeepWiki.Algebra.RatFuncDerivation

/-! # The rational-function derivative over the bridge

`toRatFuncHom` intertwines the engine derivative with the quotient-rule derivative on
`RatFunc R`, extending the differential-morphism chain of `Diff/Basic` to the fraction
field. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

open scoped Differential

/-- `toRatFuncHom` is a differential morphism into `RatFunc R`. -/
@[simp] theorem toRatFuncHom_deriv (p : DensePoly R) :
    (toRatFuncHom p)′ = toRatFuncHom (deriv p) := by
  rw [toRatFuncHom_apply, toRatFuncHom_apply, RatFunc.differential_apply,
    RatFunc.deriv_algebraMap, toPolynomial_deriv]

end DensePoly

end DeepWiki.CAlgebra
