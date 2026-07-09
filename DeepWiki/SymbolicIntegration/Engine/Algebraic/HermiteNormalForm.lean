import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Hermite row reduction (Hermite normal form) over the Euclidean domain `K[x] = DensePoly`

Triangularizes a matrix of polynomials by ring row operations only (swap, scale by a ring
element, subtract a ring multiple), reducing below-pivot entries by the Euclidean quotient
`cdivWf`. `PolyMatrix α := List (List (DensePoly α))`; `hermiteRowReduce` returns the upper-triangular
form and `hermiteRank` its row rank over `K(x)`. Validated on `DensePoly ℚ` matrices. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### The matrix representation `PolyMatrix α` and the Euclidean row operations

A `PolyMatrix α` is a `List` of rows of `DensePoly α` entries, indexed by position; the row helpers
only swap, scale by a ring element, and subtract a ring multiple of one row from another. -/

/-- A matrix of polynomials over a computable field `α`: `List (List (DensePoly α))`, indexed by
position. -/
abbrev PolyMatrix (α : Type*) := List (List (DensePoly α))

/-- Entry `M[i][j]` of a `PolyMatrix` (the zero polynomial `[]` out of range), via `getD`. -/
def polyMatGet (M : PolyMatrix α) (i j : ℕ) : DensePoly α :=
  (M.getD i []).getD j []

/-- Number of columns of a `PolyMatrix` (the length of its first row; `0` if empty). -/
def polyMatNCols (M : PolyMatrix α) : ℕ := (M.headD []).length

/-- Swap rows `i` and `j` of a `PolyMatrix` (an elementary Euclidean row operation). -/
def rowSwap (M : PolyMatrix α) (i j : ℕ) : PolyMatrix α :=
  let ri := M.getD i []
  let rj := M.getD j []
  (M.set i rj).set j ri

/-- Scale row `i` of a `PolyMatrix` by a polynomial `c : DensePoly α`, entrywise `cmul`. -/
def rowScale (M : PolyMatrix α) (i : ℕ) (c : DensePoly α) : PolyMatrix α :=
  M.set i ((M.getD i []).map (fun a => cmul c a))

/-- Subtract `q · (row k)` from row `i` of a `PolyMatrix`, entrywise (`row i ↦ row i − q · row k`). -/
def rowSub (M : PolyMatrix α) (i k : ℕ) (q : DensePoly α) : PolyMatrix α :=
  let ri := M.getD i []
  let rk := M.getD k []
  M.set i ((List.range (max ri.length rk.length)).map (fun c =>
    csub (ri.getD c []) (cmul q (rk.getD c []))))

/-- Index of the minimal-`cdeg` nonzero entry in column `j` over rows `j ≤ k < nrows` (the pivot
choice), `none` if the column is zero from row `j` down. Zero entries are filtered out explicitly. -/
def polyMatMinDegPivot (M : PolyMatrix α) (j : ℕ) : Option ℕ :=
  let nrows := M.length
  let cand := (List.range nrows).filter (fun k => j ≤ k && (!cisZero (polyMatGet M k j)))
  match cand with
  | [] => none
  | k0 :: ks =>
    some (ks.foldl (fun best k =>
      if cdeg (polyMatGet M k j) < cdeg (polyMatGet M best j) then k else best) k0)

/-! ### The Hermite row-reduction loop

`hermiteRowReduce` walks the columns; for each it brings the minimal-degree nonzero entry to the
pivot, reduces lower entries by `cdivWf`, and repeats the sweep until the column clears below the
pivot. Fuel-bounded, since each repetition strictly drops the below-pivot degree sum. -/

/-- One sweep over the rows below the pivot `(j, j)`: replace `row i` (`j < i`) by
`row i − q · row j` with `q := cdivWf (M[i][j]) (M[j][j])`, dropping each below-pivot entry's degree. -/
def hermiteSweepBelow (j : ℕ) (M : PolyMatrix α) : PolyMatrix α :=
  let nrows := M.length
  let piv := polyMatGet M j j
  (List.range nrows).foldl (fun acc i =>
    if j < i then
      let e := polyMatGet acc i j
      if cisZero e then acc
      else
        let q := cdivWf e piv
        rowSub acc i j q
    else acc) M

/-- `true` iff column `j` is zero strictly below the pivot row `j`. -/
def polyMatColZeroBelow (M : PolyMatrix α) (j : ℕ) : Bool :=
  (List.range M.length).all (fun i => j ≥ i || cisZero (polyMatGet M i j))

/-- The Hermite inner loop on column `j`, fuel-bounded: swap the minimal-degree nonzero entry to the
pivot, sweep the rows below, and repeat while the column is nonzero below the pivot. -/
def hermiteClearCol (j : ℕ) : ℕ → PolyMatrix α → PolyMatrix α
  | 0, M => M
  | loopFuel + 1, M =>
    match polyMatMinDegPivot M j with
    | none => M
    | some k =>
      let M := rowSwap M j k
      let M := hermiteSweepBelow j M
      if polyMatColZeroBelow M j then M
      else hermiteClearCol j loopFuel M

/-- Hermite row reduction: triangularize a `PolyMatrix` over `K[x]` to upper-triangular form by
Euclidean row operations, clearing each column below its pivot via `hermiteClearCol`. -/
def hermiteRowReduce (M : PolyMatrix α) : PolyMatrix α :=
  let ncols := polyMatNCols M
  let degSum := (M.map (fun row => (row.map cdeg).foldl (· + ·) 0)).foldl (· + ·) 0
  let fuel := ncols * (degSum + 2)
  (List.range ncols).foldl (fun acc j => hermiteClearCol j fuel acc) M

/-! ### Rank and triangularity readouts -/

/-- `true` iff a `PolyMatrix` is upper-triangular: every entry `M[i][j]` with `i > j` is `cisZero`. -/
def polyMatIsUpperTriangular (M : PolyMatrix α) : Bool :=
  let ncols := polyMatNCols M
  (List.range M.length).all (fun i =>
    (List.range ncols).all (fun j => j ≥ i || cisZero (polyMatGet M i j)))

/-- Row rank of a `PolyMatrix`: the number of rows not entirely `cisZero` (the rank over `K(x)`
on `hermiteRowReduce` output). -/
def hermiteRank (M : PolyMatrix α) : ℕ :=
  (M.filter (fun row => !row.all cisZero)).length

/-- Product of the diagonal entries `∏ᵢ M[i][i]` of a `PolyMatrix` (the determinant of an
upper-triangular matrix), used to certify row-equivalence up to a unit. -/
def polyMatDiagProd (M : PolyMatrix α) : DensePoly α :=
  let n := min M.length (polyMatNCols M)
  (List.range n).foldl (fun acc i => cmul acc (polyMatGet M i i)) [CCommRing.one]

/-- The `2×2` polynomial determinant `M[0][0]·M[1][1] − M[0][1]·M[1][0]` of a `PolyMatrix`. -/
def polyMat2x2Det (M : PolyMatrix α) : DensePoly α :=
  csub (cmul (polyMatGet M 0 0) (polyMatGet M 1 1))
        (cmul (polyMatGet M 0 1) (polyMatGet M 1 0))

end DensePoly

/-! ### `native_decide` validation over `DensePoly ℚ = ℚ[x]`

Concrete `2×2`/`3×3` matrices reduce to upper-triangular form, preserve the determinant up to a
unit, and (for a rank-deficient case) drop to a zero row. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- A concrete `2×2` matrix over `ℚ[x]`: `[[x² + 1, x], [x³, x + 2]]` (entries low→high). -/
def hermiteEx2 : PolyMatrix ℚ :=
  [[[1, 0, 1], [0, 1]],
   [[0, 0, 0, 1], [2, 1]]]

-- Sanity: the reduced matrix (coefficient lists of each entry).
#eval (hermiteRowReduce hermiteEx2).map (fun row => row.map (fun p => cnorm p))

/-- The `2×2` Hermite reduction is upper-triangular: `M[1][0]` of `hermiteRowReduce hermiteEx2`
is `cisZero`. -/
theorem hermiteEx2_upperTriangular :
    polyMatIsUpperTriangular (hermiteRowReduce hermiteEx2) = true := by native_decide

/-- The `2×2` Hermite reduction preserves the determinant: the diagonal product of
`hermiteRowReduce hermiteEx2` equals the original `2×2` determinant exactly. -/
theorem hermiteEx2_detPreserved :
    cisZero (csub (polyMatDiagProd (hermiteRowReduce hermiteEx2)) (polyMat2x2Det hermiteEx2)) =
      true := by native_decide

/-- The `2×2` reduction has full rank: `hermiteRank (hermiteRowReduce hermiteEx2) = 2`. -/
theorem hermiteEx2_rank :
    hermiteRank (hermiteRowReduce hermiteEx2) = 2 := by native_decide

/-- A concrete full-rank `3×3` matrix over `ℚ[x]`: `[[x, 1, 0], [x², x+1, 1], [0, x, x²+1]]`. -/
def hermiteEx3 : PolyMatrix ℚ :=
  [[[0, 1], [1],       []],
   [[0, 0, 1], [1, 1], [1]],
   [[],         [0, 1], [1, 0, 1]]]

-- Sanity: the reduced `3×3` matrix (coefficient lists of each entry).
#eval (hermiteRowReduce hermiteEx3).map (fun row => row.map (fun p => cnorm p))

/-- The `3×3` Hermite reduction is upper-triangular: every strictly-lower entry of
`hermiteRowReduce hermiteEx3` is `cisZero`. -/
theorem hermiteEx3_upperTriangular :
    polyMatIsUpperTriangular (hermiteRowReduce hermiteEx3) = true := by native_decide

/-- The `3×3` reduction has full rank: `hermiteRank (hermiteRowReduce hermiteEx3) = 3`. -/
theorem hermiteEx3_rank :
    hermiteRank (hermiteRowReduce hermiteEx3) = 3 := by native_decide

/-- The full-rank `3×3` reduction has a nonzero diagonal product: `∏ᵢ M[i][i]` of
`hermiteRowReduce hermiteEx3` is `¬ cisZero`. -/
theorem hermiteEx3_diagProd_nonzero :
    cisZero (polyMatDiagProd (hermiteRowReduce hermiteEx3)) = false := by native_decide

/-- A rank-deficient `3×3` matrix over `ℚ[x]` with `row 2 = x · row 0 + row 1`:
`[[1, x, x²], [0, 1, x], [x, x²+1, x³+x]]`. -/
def hermiteEx3Singular : PolyMatrix ℚ :=
  [[[1], [0, 1], [0, 0, 1]],
   [[],  [1],    [0, 1]],
   [[0, 1], [1, 0, 1], [0, 1, 0, 1]]]

-- Sanity: the reduced singular matrix — the bottom row should normalize to all-zero.
#eval (hermiteRowReduce hermiteEx3Singular).map (fun row => row.map (fun p => cnorm p))

/-- The rank-deficient `3×3` reduction drops rank:
`hermiteRank (hermiteRowReduce hermiteEx3Singular) < 3`. -/
theorem hermiteEx3Singular_rankDeficient :
    hermiteRank (hermiteRowReduce hermiteEx3Singular) < 3 := by native_decide

/-- The rank-deficient `3×3` reduction is still upper-triangular:
`hermiteRowReduce hermiteEx3Singular` is `polyMatIsUpperTriangular`. -/
theorem hermiteEx3Singular_upperTriangular :
    polyMatIsUpperTriangular (hermiteRowReduce hermiteEx3Singular) = true := by native_decide

/-! ### Hermite row reduction over `K[x]`

The matrix-triangularization primitive (swap / ring-scale / subtract-a-ring-multiple) the
general-curve integral basis is built on: the trace matrix, the discriminant, the p-trace-radical,
and the idealizer all reduce to a Hermite/kernel solve over `K[x]`. -/

end DeepWiki.SymbolicIntegration
