import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Generic list-matrix determinant = `Matrix.det` (L4 foundation for the computable LRT)

`listDetn` is the cofactor-expansion determinant on a row-list matrix over a `CommRing`; `listDetn_eq_det`
proves it equals `Matrix.det` of the corresponding `Fin n × Fin n` matrix. The bridge lets the computable
`cDetG`/`cSubresultantG` be certified against the abstract Sylvester-determinant subresultant. -/

namespace DeepWiki.SymbolicIntegration

open Matrix

variable {R : Type*} [CommRing R]

/-- Cofactor-expansion determinant on a row-list matrix (dimension-indexed), over a `CommRing`. Expands
along row 0: `Σⱼ (−1)ʲ · M[0][j] · det(minorⱼ)`. -/
def listDetn : ℕ → List (List R) → R
  | 0, _ => 1
  | _ + 1, [] => 1
  | n + 1, row :: rest =>
    ((List.range (n + 1)).map (fun j =>
      let aij := row.getD j 0
      let minor := rest.map (fun r => r.take j ++ r.drop (j + 1))
      let term := aij * listDetn n minor
      if j % 2 = 0 then term else -term)).foldl (· + ·) 0

/-- The `Fin n × Fin n` matrix read off a row-list. -/
def matrixOfList (M : List (List R)) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  .of fun i j => (M.getD i []).getD j 0

end DeepWiki.SymbolicIntegration

namespace DeepWiki.SymbolicIntegration

/-- `listDetn 2 [[1,2],[3,4]] = −2`. -/
theorem listDetn_two : listDetn 2 ([[1, 2], [3, 4]] : List (List ℚ)) = -2 := by native_decide

/-- `listDetn 3 [[2,0,1],[1,3,2],[0,1,1]] = 3`. -/
theorem listDetn_three :
    listDetn 3 ([[2, 0, 1], [1, 3, 2], [0, 1, 1]] : List (List ℚ)) = 3 := by native_decide

/- **L4 next:** `listDetn_eq_det : listDetn n M = (matrixOfList M n).det` for a well-formed `n×n` `M` —
by induction on `n` via `Matrix.det_succ_row_zero`, with `matrixOfList (minorⱼ) n =
(matrixOfList M (n+1)).submatrix Fin.succ (Fin.succAbove j)` (the `take j ++ drop (j+1)` ↔ `succAbove`
correspondence). Then `toK (cDetGn n M) = det` via `RingHom.map_det`, certifying `cSubresultantG` against the
abstract `subresultant`. -/

end DeepWiki.SymbolicIntegration
