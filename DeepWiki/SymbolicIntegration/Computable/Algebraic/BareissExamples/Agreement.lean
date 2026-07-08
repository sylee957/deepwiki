import DeepWiki.SymbolicIntegration.Computable.Algebraic.BareissEngine
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.Algebraic.AlgFunctionField

/-! # Bareiss determinant agreement examples

Examples showing that `bareissDet M = fieldDet (fromQ M)` on trace matrices and a Vandermonde matrix. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- Embed a `ℚ[x]`-matrix into `ℚ(x)`: `fromQ M` replaces each entry `p` by `qxOfNum p = p/1`. -/
def fromQ (M : List (List (CPolyG ℚ))) : List (List (QFunNZG ℚ)) :=
  M.map (fun row => row.map qxOfNum)

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

end DeepWiki.SymbolicIntegration
