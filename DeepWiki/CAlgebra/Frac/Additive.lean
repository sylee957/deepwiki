import DeepWiki.CAlgebra.Frac.Arithmetic

/-! # Rational-function arithmetic (additive + inverse)

`neg`/`inv`/`add` on `DenseFrac` and their homomorphism squares into `RatFunc R`. `neg` and `inv`
transport unconditionally; `add` needs both denominators nonzero (a field's
`a/b + c/d = (ad+bc)/(bd)` requires `b, d ≠ 0`), so `toRatFunc_add` carries `den ≠ 0` hypotheses. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R]

/-- A nonzero dense polynomial has nonzero Mathlib image. -/
theorem toPolynomial_ne_zero {p : DensePoly R} (h : p ≠ 0) : toPolynomial p ≠ 0 :=
  fun hz => h (toPolynomial_injective (by rw [hz, toPolynomial_zero]))

namespace DenseFrac

/-- Rational-function negation: negate the numerator. -/
def neg (f : DenseFrac R) : DenseFrac R := ⟨-f.num, f.den⟩

instance : Neg (DenseFrac R) where neg := neg

theorem neg_def (f : DenseFrac R) : -f = ⟨-f.num, f.den⟩ := rfl

/-- `toRatFunc` intertwines negation (unconditionally). -/
@[simp] theorem toRatFunc_neg (f : DenseFrac R) : toRatFunc (-f) = -toRatFunc f := by
  rw [neg_def, toRatFunc_mk, toRatFunc, toPolynomial_neg, map_neg, neg_div]

/-- Rational-function inverse: swap numerator and denominator. -/
def inv (f : DenseFrac R) : DenseFrac R := ⟨f.den, f.num⟩

instance : Inv (DenseFrac R) where inv := inv

theorem inv_def (f : DenseFrac R) : f⁻¹ = ⟨f.den, f.num⟩ := rfl

/-- `toRatFunc` intertwines inversion (unconditionally). -/
@[simp] theorem toRatFunc_inv (f : DenseFrac R) : toRatFunc f⁻¹ = (toRatFunc f)⁻¹ := by
  rw [inv_def, toRatFunc_mk, toRatFunc, inv_div]

/-- Rational-function addition by cross-multiplication. -/
def add (f g : DenseFrac R) : DenseFrac R := ⟨f.num * g.den + g.num * f.den, f.den * g.den⟩

instance : Add (DenseFrac R) where add := add

theorem add_def (f g : DenseFrac R) :
    f + g = ⟨f.num * g.den + g.num * f.den, f.den * g.den⟩ := rfl

/-- `toRatFunc` intertwines addition when both denominators are nonzero. -/
theorem toRatFunc_add (f g : DenseFrac R) (hf : f.den ≠ 0) (hg : g.den ≠ 0) :
    toRatFunc (f + g) = toRatFunc f + toRatFunc g := by
  have haf := RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hf)
  have hag := RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hg)
  rw [add_def, toRatFunc_mk, toRatFunc, toRatFunc, div_add_div _ _ haf hag]
  simp only [toPolynomial_add, toPolynomial_mul, map_add, map_mul]
  congr 1
  ring

/-- Validation: `toRatFunc` respects addition on genuine (nonzero-denominator) fractions. -/
example (f g : DenseFrac R) (hf : f.den ≠ 0) (hg : g.den ≠ 0) :
    toRatFunc (f + g) = toRatFunc f + toRatFunc g := toRatFunc_add f g hf hg

end DenseFrac

end DeepWiki.CAlgebra
