import DeepWiki.CAlgebra.Poly.Operations
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Raw fraction pairs (`DenseFrac`) — the representation layer

`DenseFrac R` is a numerator/denominator pair of dense polynomials: the **representation layer**
beneath the canonical carrier `CanonicalFrac`, supplying the data type, the one-step arithmetic,
and the `toRatFunc` homomorphism that the canonical construction reduces and transports. It is not
itself a carrier: raw pairs form no lawful ring (representatives drift, e.g. `f + (−f) = ⟨0, d²⟩`),
and unreduced arithmetic grows exponentially under iteration — engine-facing code uses
`CanonicalFrac`. Pair + ops need only `CommRing`; the `RatFunc` bridge needs `Field`. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

/-! ### Carrier and arithmetic (any `CommRing` coefficient) -/

section Carrier
variable {R : Type u} [CommRing R] [DecidableEq R]

/-- Computable rational function: a numerator and denominator of dense polynomials. -/
structure DenseFrac (R : Type u) [CommRing R] [DecidableEq R] where
  /-- The numerator polynomial. -/
  num : DensePoly R
  /-- The denominator polynomial. -/
  den : DensePoly R

namespace DenseFrac

/-- Structural equality of fractions is decidable (componentwise on the dense polynomials). -/
instance : DecidableEq (DenseFrac R) := fun a b =>
  match decEq a.num b.num, decEq a.den b.den with
  | isTrue h1, isTrue h2 => isTrue (by cases a; cases b; cases h1; cases h2; rfl)
  | isFalse h1, _ => isFalse fun h => h1 (congrArg DenseFrac.num h)
  | _, isFalse h2 => isFalse fun h => h2 (congrArg DenseFrac.den h)

/-- Embed a dense polynomial as a rational function with denominator `1`. -/
def ofPoly (p : DensePoly R) : DenseFrac R := ⟨p, 1⟩

/-- Rational-function multiplication: multiply numerators and denominators. -/
def mul (f g : DenseFrac R) : DenseFrac R := ⟨f.num * g.num, f.den * g.den⟩
instance : Mul (DenseFrac R) where mul := mul
theorem mul_def (f g : DenseFrac R) : f * g = ⟨f.num * g.num, f.den * g.den⟩ := rfl

/-- The multiplicative unit `1/1`. -/
instance : One (DenseFrac R) where one := ⟨1, 1⟩

/-- Rational-function negation: negate the numerator. -/
def neg (f : DenseFrac R) : DenseFrac R := ⟨-f.num, f.den⟩
instance : Neg (DenseFrac R) where neg := neg
theorem neg_def (f : DenseFrac R) : -f = ⟨-f.num, f.den⟩ := rfl

/-- Rational-function inverse: swap numerator and denominator. -/
def inv (f : DenseFrac R) : DenseFrac R := ⟨f.den, f.num⟩
instance : Inv (DenseFrac R) where inv := inv
theorem inv_def (f : DenseFrac R) : f⁻¹ = ⟨f.den, f.num⟩ := rfl

/-- Rational-function addition by cross-multiplication. -/
def add (f g : DenseFrac R) : DenseFrac R := ⟨f.num * g.den + g.num * f.den, f.den * g.den⟩
instance : Add (DenseFrac R) where add := add
theorem add_def (f g : DenseFrac R) :
    f + g = ⟨f.num * g.den + g.num * f.den, f.den * g.den⟩ := rfl

/-- Pairwise (cross-multiplication) equivalence of raw fractions: semantic equality of the pairs,
expressible without normalization. -/
def Eqv (f g : DenseFrac R) : Prop := f.num * g.den = g.num * f.den

/-- Pairwise equivalence is decidable (one multiplication and a structural comparison — no gcd). -/
instance (f g : DenseFrac R) : Decidable (f.Eqv g) :=
  inferInstanceAs (Decidable (_ = _))

end DenseFrac
end Carrier

/-! ### Mathlib bridge `toRatFunc` (any `Field` coefficient) -/

section Bridge
variable {R : Type u} [Field R] [DecidableEq R]

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

/-- For nonzero denominators, the `RatFunc` denotations agree iff the pairs are
cross-multiplication equivalent: `Eqv` is exactly denotational equality. -/
theorem toRatFunc_eq_iff_eqv {f g : DenseFrac R} (hf : f.den ≠ 0) (hg : g.den ≠ 0) :
    toRatFunc f = toRatFunc g ↔ f.Eqv g := by
  have hF : algebraMap (Polynomial R) (RatFunc R) (toPolynomial f.den) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hf)
  have hG : algebraMap (Polynomial R) (RatFunc R) (toPolynomial g.den) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hg)
  simp only [toRatFunc]
  rw [div_eq_div_iff hF hG, ← map_mul, ← map_mul, ← toPolynomial_mul, ← toPolynomial_mul]
  exact ((IsFractionRing.injective (Polynomial R) (RatFunc R)).comp
    toPolynomial_injective).eq_iff

/-- Validation: `toRatFunc` is a ring homomorphism into the rational-function field. -/
example (f g : DenseFrac R) (hf : f.den ≠ 0) (hg : g.den ≠ 0) :
    toRatFunc (f * g) = toRatFunc f * toRatFunc g ∧
    toRatFunc (f + g) = toRatFunc f + toRatFunc g :=
  ⟨toRatFunc_mul f g, toRatFunc_add f g hf hg⟩

end DenseFrac
end Bridge

end DeepWiki.CAlgebra
