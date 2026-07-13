import DeepWiki.CAlgebra.Frac.Dense

/-! # Rational-function arithmetic (multiplicative)

`mul`/`one` on `DenseFrac` and their homomorphism squares into `RatFunc R`. These hold
unconditionally (a field's `(a/b)·(c/d) = (a·c)/(b·d)` needs no `den ≠ 0`), so the multiplicative
bridge lands first. Additive/inverse structure (which needs the `den ≠ 0` invariant) is Phase 4b-ii. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R]

namespace DenseFrac

/-- Rational-function multiplication: multiply numerators and denominators. -/
def mul (f g : DenseFrac R) : DenseFrac R := ⟨f.num * g.num, f.den * g.den⟩

instance : Mul (DenseFrac R) where mul := mul

/-- The multiplicative unit `1/1`. -/
instance : One (DenseFrac R) where one := ⟨1, 1⟩

theorem mul_def (f g : DenseFrac R) : f * g = ⟨f.num * g.num, f.den * g.den⟩ := rfl

/-- `toRatFunc` intertwines multiplication (unconditionally). -/
@[simp] theorem toRatFunc_mul (f g : DenseFrac R) :
    toRatFunc (f * g) = toRatFunc f * toRatFunc g := by
  rw [mul_def, toRatFunc_mk, toRatFunc, toRatFunc, toPolynomial_mul, toPolynomial_mul,
    map_mul, map_mul, div_mul_div_comm]

/-- `toRatFunc` sends the unit to `1`. -/
@[simp] theorem toRatFunc_one : toRatFunc (1 : DenseFrac R) = 1 := by
  show toRatFunc (⟨1, 1⟩ : DenseFrac R) = 1
  rw [toRatFunc_mk, toPolynomial_one, map_one, div_one]

/-- Validation: `toRatFunc` is a multiplicative homomorphism into the rational-function field. -/
example (f g : DenseFrac R) : toRatFunc (f * g) = toRatFunc f * toRatFunc g := toRatFunc_mul f g

end DenseFrac

end DeepWiki.CAlgebra
