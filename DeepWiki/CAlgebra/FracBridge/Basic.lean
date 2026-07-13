import DeepWiki.CAlgebra.Frac.Additive
import DeepWiki.CAlgebra.PolyBridge.Basic
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Mathlib bridge for `DenseFrac`: `toRatFunc`

The Mathlib correspondence for the computable rational-function carrier: `toRatFunc` sends a
`DenseFrac` to `RatFunc R` as `num/den`, and the homomorphism squares relate the computable
arithmetic (`Frac/*`) to `RatFunc` operations. Kept out of the `Frac/` core modules so those stay
Mathlib-correspondence-free. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R]

/-- A nonzero dense polynomial has nonzero Mathlib image. -/
theorem toPolynomial_ne_zero {p : DensePoly R} (h : p ≠ 0) : toPolynomial p ≠ 0 :=
  fun hz => h (toPolynomial_injective (by rw [hz, toPolynomial_zero]))

namespace DenseFrac

/-- Bridge to Mathlib: `num/den` in the rational-function field. -/
noncomputable def toRatFunc (f : DenseFrac R) : RatFunc R :=
  algebraMap (Polynomial R) (RatFunc R) (toPolynomial f.num) /
    algebraMap (Polynomial R) (RatFunc R) (toPolynomial f.den)

@[simp] theorem toRatFunc_mk (num den : DensePoly R) :
    toRatFunc (⟨num, den⟩ : DenseFrac R) =
      algebraMap (Polynomial R) (RatFunc R) (toPolynomial num) /
        algebraMap (Polynomial R) (RatFunc R) (toPolynomial den) := rfl

/-- The polynomial embedding reads as the polynomial itself in `RatFunc R`. -/
@[simp] theorem toRatFunc_ofPoly (p : DensePoly R) :
    toRatFunc (ofPoly p) = algebraMap (Polynomial R) (RatFunc R) (toPolynomial p) := by
  rw [ofPoly, toRatFunc_mk, toPolynomial_one, map_one, div_one]

/-- `toRatFunc` intertwines multiplication (unconditionally). -/
@[simp] theorem toRatFunc_mul (f g : DenseFrac R) :
    toRatFunc (f * g) = toRatFunc f * toRatFunc g := by
  rw [mul_def, toRatFunc_mk, toRatFunc, toRatFunc, toPolynomial_mul, toPolynomial_mul,
    map_mul, map_mul, div_mul_div_comm]

/-- `toRatFunc` sends the unit to `1`. -/
@[simp] theorem toRatFunc_one : toRatFunc (1 : DenseFrac R) = 1 := by
  show toRatFunc (⟨1, 1⟩ : DenseFrac R) = 1
  rw [toRatFunc_mk, toPolynomial_one, map_one, div_one]

/-- `toRatFunc` intertwines negation (unconditionally). -/
@[simp] theorem toRatFunc_neg (f : DenseFrac R) : toRatFunc (-f) = -toRatFunc f := by
  rw [neg_def, toRatFunc_mk, toRatFunc, toPolynomial_neg, map_neg, neg_div]

/-- `toRatFunc` intertwines inversion (unconditionally). -/
@[simp] theorem toRatFunc_inv (f : DenseFrac R) : toRatFunc f⁻¹ = (toRatFunc f)⁻¹ := by
  rw [inv_def, toRatFunc_mk, toRatFunc, inv_div]

/-- `toRatFunc` intertwines addition when both denominators are nonzero. -/
theorem toRatFunc_add (f g : DenseFrac R) (hf : f.den ≠ 0) (hg : g.den ≠ 0) :
    toRatFunc (f + g) = toRatFunc f + toRatFunc g := by
  have haf := RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hf)
  have hag := RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hg)
  rw [add_def, toRatFunc_mk, toRatFunc, toRatFunc, div_add_div _ _ haf hag]
  simp only [toPolynomial_add, toPolynomial_mul, map_add, map_mul]
  congr 1
  ring

/-- Validation: `toRatFunc` is a ring homomorphism into the rational-function field (mul/one
unconditional; add on genuine nonzero-denominator fractions). -/
example (f g : DenseFrac R) (hf : f.den ≠ 0) (hg : g.den ≠ 0) :
    toRatFunc (f * g) = toRatFunc f * toRatFunc g ∧
    toRatFunc (f + g) = toRatFunc f + toRatFunc g :=
  ⟨toRatFunc_mul f g, toRatFunc_add f g hf hg⟩

end DenseFrac

end DeepWiki.CAlgebra
