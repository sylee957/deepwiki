import DeepWiki.SymbolicIntegration.Computable.Algebraic.BareissEngine
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.Algebraic.AlgFunctionField

/-! # Agreement of the fraction-free Bareiss determinant with `fieldDet`

Validations that `bareissDet M = fieldDet (fromQ M)`, that `bareissAdjugate`/`bareissSolve` satisfy
`M·adj = det·I` and Cramer's rule, and a degree-swell benchmark on a `3×3` Cauchy matrix. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### Embedding `ℚ[x]` matrices into `ℚ(x)` (`fromQ`) -/

open CPolyG

/-- Embed a `ℚ[x]`-matrix into `ℚ(x)`: `fromQ M` replaces each entry `p` by `qxOfNum p = p/1`. -/
def fromQ (M : List (List (CPolyG ℚ))) : List (List (QFunNZG ℚ)) :=
  M.map (fun row => row.map qxOfNum)

/-! ### Agreement: `bareissDet = fieldDet` on the trace-matrix curves -/

/-- A `2×2` `ℚ[x]`-matrix `[[2, x], [x, x² + 2x³]]`, the trace matrix of the curve `y² − xy − x³`;
its determinant is the discriminant `x² + 4x³`. -/
def bareissNonRadT : List (List (CPolyG ℚ)) :=
  [[[2], [0, 1]], [[0, 1], [0, 0, 1, 2]]]

/-- `bareissDet = fieldDet ∘ fromQ` on the `2×2` trace matrix, both the discriminant `x² + 4x³`. -/
theorem bareiss_eq_fieldDet_nonRad :
    CField.isZero (CField.sub (fieldDet (fromQ bareissNonRadT))
      (qxOfNum (bareissDet bareissNonRadT))) = true := by native_decide

/-- `bareissDet` of the `2×2` trace matrix is the discriminant `x² + 4x³`. -/
theorem bareissDet_nonRad_eq :
    cisZeroG (csubG (bareissDet bareissNonRadT) [0, 0, 1, 4]) = true := by native_decide

/-- A `3×3` `ℚ[x]`-matrix, the trace matrix of the trigonal curve `y³ + xy + x`; its determinant is
the discriminant `−4x³ − 27x²`. Entries are the Newton power sums `Tr(yⁱ⁺ʲ)`. -/
def bareissTrigT : List (List (CPolyG ℚ)) :=
  [[[3], [], [0, -2]],
   [[], [0, -2], [0, -3]],
   [[0, -2], [0, -3], [0, 0, 2]]]

/-- `bareissDet = fieldDet ∘ fromQ` on the `3×3` trigonal trace matrix, both `−4x³ − 27x²`. -/
theorem bareiss_eq_fieldDet_trig :
    CField.isZero (CField.sub (fieldDet (fromQ bareissTrigT))
      (qxOfNum (bareissDet bareissTrigT))) = true := by native_decide

/-- `bareissDet` of the `3×3` trigonal trace matrix is the discriminant `−4x³ − 27x²`. -/
theorem bareissDet_trig_eq :
    cisZeroG (csubG (bareissDet bareissTrigT) [0, 0, -27, -4]) = true := by native_decide

/-! ### A `4×4` Vandermonde over `ℚ[x]` -/

/-- A `4×4` Vandermonde `ℚ[x]`-matrix with nodes `[x, x+1, x+2, x+3]`, row `i` = `[xⁱ, (x+1)ⁱ, (x+2)ⁱ,
(x+3)ⁱ]`; determinant `∏_{i<j}(nodeⱼ − nodeᵢ) = 12`. -/
def bareissVander4 : List (List (CPolyG ℚ)) :=
  [[[1], [1], [1], [1]],
   [[0, 1], [1, 1], [2, 1], [3, 1]],
   [cmulG [0, 1] [0, 1], cmulG [1, 1] [1, 1], cmulG [2, 1] [2, 1], cmulG [3, 1] [3, 1]],
   [cmulG (cmulG [0, 1] [0, 1]) [0, 1], cmulG (cmulG [1, 1] [1, 1]) [1, 1],
    cmulG (cmulG [2, 1] [2, 1]) [2, 1], cmulG (cmulG [3, 1] [3, 1]) [3, 1]]]

/-- `bareissDet` of the `4×4` Vandermonde is the constant `12`. -/
theorem bareissDet_vander4_eq :
    cisZeroG (csubG (bareissDet bareissVander4) [12]) = true := by native_decide

/-- `bareissDet = fieldDet` on the `4×4` Vandermonde, both the constant `12`. -/
theorem bareiss_eq_fieldDet_vander4 :
    CField.isZero (CField.sub (fieldDet (fromQ bareissVander4))
      (qxOfNum (bareissDet bareissVander4))) = true := by native_decide

/-! ### Adjugate / solve sanity: `M · adj M = det M · I` -/

/-- `M · adj M = det M · I` on the `2×2` trace matrix: the fraction-free adjugate satisfies the
defining identity over `ℚ[x]`. -/
theorem bareiss_adjugate_nonRad :
    let M := bareissNonRadT
    let A := bareissAdjugate M
    let d := bareissDet M
    let prod := (List.range 2).map (fun i => (List.range 2).map (fun j =>
      (List.range 2).foldl (fun acc k => caddG acc (cmulG (getEntry M i k) (getEntry A k j))) []))
    (cisZeroG (csubG (getEntry prod 0 0) d)
      && cisZeroG (getEntry prod 0 1)
      && cisZeroG (getEntry prod 1 0)
      && cisZeroG (csubG (getEntry prod 1 1) d)) = true := by native_decide

/-- `M · adj M = det M · I` on the `3×3` trigonal trace matrix: the diagonal of `M·adj M` is
`det M = −4x³ − 27x²` and every off-diagonal entry vanishes. -/
theorem bareiss_adjugate_trig :
    let M := bareissTrigT
    let A := bareissAdjugate M
    let d := bareissDet M
    let prod := (List.range 3).map (fun i => (List.range 3).map (fun j =>
      (List.range 3).foldl (fun acc k => caddG acc (cmulG (getEntry M i k) (getEntry A k j))) []))
    (List.range 3).all (fun i => (List.range 3).all (fun j =>
      cisZeroG (csubG (getEntry prod i j) (if i = j then d else [])))) = true := by native_decide

/-- `bareissSolve` solves `M·(det·x) = det·b` on the `2×2` trace matrix with `b = [1, x]`: multiplying
`M` by the returned solution vector recovers `det M · b`. -/
theorem bareiss_solve_nonRad :
    let M := bareissNonRadT
    let b : List (CPolyG ℚ) := [[1], [0, 1]]
    let ds := bareissSolve M b
    let d := ds.1
    let sol := ds.2
    let lhs := (List.range 2).map (fun i =>
      (List.range 2).foldl (fun acc j => caddG acc (cmulG (getEntry M i j) (sol.getD j []))) [])
    (cisZeroG (csubG (lhs.getD 0 []) (cmulG d (b.getD 0 [])))
      && cisZeroG (csubG (lhs.getD 1 []) (cmulG d (b.getD 1 [])))) = true := by native_decide

/-! ### The swell benchmark: fraction-free `bareissDet` vs the `ℚ(x)`-fraction path

On the `3×3` Cauchy matrix `H[i][j] = 1/(x + i + j + 1)`, the fraction-based `fieldDet` over `ℚ(x)`
carries an unreduced value whose denominator degree balloons, while the fraction-free path clears to a
common denominator once and runs `bareissDet` to a single flat polynomial. -/

/-- The `3×3` Cauchy matrix over `ℚ(x)` `H[i][j] = 1/(x + i + j + 1)`, with denominators `x+1, …, x+5`;
`fieldDet` over it carries an unreduced `ℚ(x)` value whose denominator balloons. -/
def bareissCauchyQ : List (List (QFunNZG ℚ)) :=
  [[qxOfFrac [1] [1, 1] (by decide), qxOfFrac [1] [2, 1] (by decide), qxOfFrac [1] [3, 1] (by decide)],
   [qxOfFrac [1] [2, 1] (by decide), qxOfFrac [1] [3, 1] (by decide), qxOfFrac [1] [4, 1] (by decide)],
   [qxOfFrac [1] [3, 1] (by decide), qxOfFrac [1] [4, 1] (by decide), qxOfFrac [1] [5, 1] (by decide)]]

/-- The Cauchy matrix cleared to `ℚ[x]` `H[i][j] = D/(x + i + j + 1)` with common denominator
`D = (x+1)(x+2)(x+3)(x+4)(x+5)`; each entry is a degree-`4` polynomial, so `bareissDet` runs over
`ℚ[x]`. -/
def bareissCauchyCleared : List (List (CPolyG ℚ)) :=
  let D : CPolyG ℚ := cmulG (cmulG (cmulG (cmulG [1, 1] [2, 1]) [3, 1]) [4, 1]) [5, 1]
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

/-! ### `#print axioms` for the Bareiss validations -/

-- Agreement of the fraction-free Bareiss determinant with the fraction-based `fieldDet`.
#print axioms bareiss_eq_fieldDet_nonRad
#print axioms bareiss_eq_fieldDet_trig
#print axioms bareiss_eq_fieldDet_vander4

-- The fraction-free adjugate / solve identities `M·adj = det·I`, `M·(det·x) = det·b`.
#print axioms bareiss_adjugate_nonRad
#print axioms bareiss_adjugate_trig
#print axioms bareiss_solve_nonRad

-- The swell benchmark: unreduced fraction-path total degree 21 vs flat fraction-free Bareiss degree 6.
#print axioms bareissSwellWin
#print axioms bareissCauchyFlatDeg_eq
#print axioms bareissCauchyFracTotalDeg_eq

end DeepWiki.SymbolicIntegration
