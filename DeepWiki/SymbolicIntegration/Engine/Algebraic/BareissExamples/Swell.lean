import DeepWiki.SymbolicIntegration.Engine.Algebraic.BareissExamples.Agreement

/-! # Bareiss degree-swell benchmark

A Cauchy-matrix benchmark comparing the fraction-free determinant against the unreduced `ℚ(x)` path. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly

/-- The `3×3` Cauchy matrix over `ℚ(x)` `H[i][j] = 1/(x + i + j + 1)`, with denominators `x+1, …, x+5`;
`fieldDet` over it carries an unreduced `ℚ(x)` value whose denominator balloons. -/
def bareissCauchyQ : List (List (QFunNZG ℚ)) :=
  [[qxOfFrac [1] [1, 1] (by decide), qxOfFrac [1] [2, 1] (by decide), qxOfFrac [1] [3, 1] (by decide)],
   [qxOfFrac [1] [2, 1] (by decide), qxOfFrac [1] [3, 1] (by decide), qxOfFrac [1] [4, 1] (by decide)],
   [qxOfFrac [1] [3, 1] (by decide), qxOfFrac [1] [4, 1] (by decide), qxOfFrac [1] [5, 1] (by decide)]]

/-- The Cauchy matrix cleared to `ℚ[x]` `H[i][j] = D/(x + i + j + 1)` with common denominator
`D = (x+1)(x+2)(x+3)(x+4)(x+5)`; each entry is a degree-`4` polynomial, so `bareissDet` runs over
`ℚ[x]`. -/
def bareissCauchyCleared : List (List (CPoly ℚ)) :=
  let D : CPoly ℚ := cmulG (cmulG (cmulG (cmulG [1, 1] [2, 1]) [3, 1]) [4, 1]) [5, 1]
  [[cdivWf D [1, 1], cdivWf D [2, 1], cdivWf D [3, 1]],
   [cdivWf D [2, 1], cdivWf D [3, 1], cdivWf D [4, 1]],
   [cdivWf D [3, 1], cdivWf D [4, 1], cdivWf D [5, 1]]]

/-- The fraction-path total degree `cdegG num + cdegG den` of the unreduced `ℚ(x)` value
`fieldDet bareissCauchyQ` (numerator degree `6` plus denominator degree `15`, total `21`). -/
def bareissCauchyFracTotalDeg : ℕ :=
  let z := fieldDet bareissCauchyQ
  cdegG z.1.1 + cdegG z.1.2

/-- The fraction-free flat degree `cdegG (bareissDet bareissCauchyCleared)`, the degree of the single
`ℚ[x]` polynomial the Bareiss path produces for the cleared Cauchy matrix (degree `6`). -/
def bareissCauchyFlatDeg : ℕ := cdegG (bareissDet bareissCauchyCleared)

/-- The measured swell win: `bareissCauchyFlatDeg < bareissCauchyFracTotalDeg` — the fraction-free
Bareiss flat degree is strictly smaller than the fraction-path total degree on the `3×3` Cauchy matrix. -/
theorem bareissSwellWin : bareissCauchyFlatDeg < bareissCauchyFracTotalDeg := by native_decide

/-- The Bareiss flat degree is `6`: the fraction-free determinant of the cleared Cauchy matrix is a
single degree-`6` polynomial. -/
theorem bareissCauchyFlatDeg_eq : bareissCauchyFlatDeg = 6 := by native_decide

/-- The fraction path's total degree is `21`: `fieldDet` over `ℚ(x)` carries the Cauchy determinant as
an unreduced value of numerator degree `6` over denominator degree `15`. -/
theorem bareissCauchyFracTotalDeg_eq : bareissCauchyFracTotalDeg = 21 := by native_decide

end DeepWiki.SymbolicIntegration
