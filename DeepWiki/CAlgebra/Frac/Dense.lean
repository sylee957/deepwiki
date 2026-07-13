import DeepWiki.CAlgebra.PolyBridge.Basic
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Computable rational functions (`DenseFrac`)

`DenseFrac R` is a numerator/denominator pair of normalized dense polynomials — the computable carrier
for rational functions. The Mathlib bridge `toRatFunc` sends it to `RatFunc R` as `num/den` (through
`toPolynomial` and the fraction-field `algebraMap`); the bridge is noncomputable because `RatFunc`
division is, but the carrier and its arithmetic stay computable. Field structure and the hom squares
are Phase 4b; the tower iteration is 4c. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R]

/-- Computable rational function: a numerator and denominator of dense polynomials. -/
structure DenseFrac (R : Type u) [Field R] [DecidableEq R] where
  /-- The numerator polynomial. -/
  num : DensePoly R
  /-- The denominator polynomial. -/
  den : DensePoly R

namespace DenseFrac

/-- Bridge to Mathlib: `num/den` in the rational-function field. -/
noncomputable def toRatFunc (f : DenseFrac R) : RatFunc R :=
  algebraMap (Polynomial R) (RatFunc R) (toPolynomial f.num) /
    algebraMap (Polynomial R) (RatFunc R) (toPolynomial f.den)

@[simp] theorem toRatFunc_mk (num den : DensePoly R) :
    toRatFunc (⟨num, den⟩ : DenseFrac R) =
      algebraMap (Polynomial R) (RatFunc R) (toPolynomial num) /
        algebraMap (Polynomial R) (RatFunc R) (toPolynomial den) := rfl

/-- Embed a dense polynomial as a rational function with denominator `1`. -/
def ofPoly (p : DensePoly R) : DenseFrac R := ⟨p, 1⟩

/-- The embedding reads as the polynomial itself in `RatFunc R`. -/
@[simp] theorem toRatFunc_ofPoly (p : DensePoly R) :
    toRatFunc (ofPoly p) = algebraMap (Polynomial R) (RatFunc R) (toPolynomial p) := by
  rw [ofPoly, toRatFunc_mk, toPolynomial_one, map_one, div_one]

end DenseFrac

end DeepWiki.CAlgebra
