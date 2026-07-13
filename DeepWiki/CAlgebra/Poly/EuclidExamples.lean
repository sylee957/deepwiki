import DeepWiki.CAlgebra.Poly.Euclid

/-! # Computational validation of the Euclidean layer over `ℚ`

Concrete `native_decide` checks that the executable division/gcd genuinely run (via the compiler):
the whole normalized-`DensePoly` stack is computable, not just provable. -/

namespace DeepWiki.CAlgebra

open DensePoly

/-- `x² − 1 = (x + 1)(x − 1)`: division is exact, quotient `x + 1`, remainder `0`. -/
example : divMod (ofList [-1, 0, 1] : DensePoly ℚ) (ofList [-1, 1]) = (ofList [1, 1], ofList []) := by
  native_decide

/-- `gcd(x² − 1, x − 1) = x − 1` (the executable Euclidean gcd, run concretely). -/
example : gcd (ofList [-1, 0, 1] : DensePoly ℚ) (ofList [-1, 1]) = ofList [-1, 1] := by
  native_decide

/-- `gcd(x² − 1, x² − 2x + 1) = 2(x − 1)`: the raw Euclidean gcd returns `2x − 2`, a unit multiple
of `x − 1` — a concrete witness that the executable gcd is `Associated` to, not equal to, the
normalized gcd (exactly why the Mathlib bridge is stated up to `Associated`). -/
example : gcd (ofList [-1, 0, 1] : DensePoly ℚ) (ofList [1, -2, 1]) = ofList [-2, 2] := by
  native_decide

end DeepWiki.CAlgebra
