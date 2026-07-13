import DeepWiki.CAlgebra.Poly.Operations

/-! # Computable rational functions (`DenseFrac`) — carrier

`DenseFrac R` is a numerator/denominator pair of normalized dense polynomials — the computable
carrier for rational functions. Its Mathlib correspondence (`toRatFunc` into `RatFunc R`) lives in
`FracBridge/Basic.lean`, keeping this core module correspondence-free. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- Computable rational function: a numerator and denominator of dense polynomials. -/
structure DenseFrac (R : Type u) [CommRing R] [DecidableEq R] where
  /-- The numerator polynomial. -/
  num : DensePoly R
  /-- The denominator polynomial. -/
  den : DensePoly R

namespace DenseFrac

/-- Embed a dense polynomial as a rational function with denominator `1`. -/
def ofPoly (p : DensePoly R) : DenseFrac R := ⟨p, 1⟩

end DenseFrac

end DeepWiki.CAlgebra
