import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.ComputableAlgebra.LinearAlgebra

/-! # Executable dense linear solving over `ℚ`

List-based reduced row echelon form, nullspace bases, and unique or particular
solution reading for dense rational matrices, plus the small generic `getD`
helper used by downstream matrix proofs.
-/

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

/-- `crref rows ncols` computes the RREF and pivot columns of a dense rational matrix. -/
def crref (rows : List (List ℚ)) (ncols : ℕ) : List (List ℚ) × List ℕ :=
  -- work column by column, maintaining the not-yet-pivoted rows and the accumulated pivot rows.
  let rec go : ℕ → ℕ → List (List ℚ) → List (List ℚ) → List ℕ →
      List (List ℚ) × List ℕ
    | 0, _, _, pivRows, pivCols => (pivRows.reverse, pivCols.reverse)
    | _, _, [], pivRows, pivCols => (pivRows.reverse, pivCols.reverse)  -- no rows left
    | fuel + 1, col, rest, pivRows, pivCols =>
      if col ≥ ncols then (pivRows.reverse, pivCols.reverse)
      else
        -- find a row in `rest` with a nonzero entry in column `col`.
        match rest.find? (fun r => (r.getD col 0) ≠ 0) with
        | none => go (fuel) (col + 1) rest pivRows pivCols  -- free column, skip
        | some pr =>
          let piv := pr.getD col 0
          let prn := pr.map (· / piv)                       -- normalize pivot to 1
          -- eliminate column `col` from every other current row (rest minus pr, and pivRows).
          let elim : List ℚ → List ℚ := fun r =>
            let f := r.getD col 0
            (List.zipWith (fun ri pi => ri - f * pi) r prn)
          let restElim := (rest.filter (fun r => !(decide (r = pr)))).map elim
          let pivRowsElim := pivRows.map elim
          go fuel (col + 1) restElim (prn :: pivRowsElim) (col :: pivCols)
  go (ncols + rows.length + 1) 0 rows [] []

/-- `cNullspaceBasisQ rows ncols` returns nullspace basis vectors for a rational matrix. -/
def cNullspaceBasisQ (rows : List (List ℚ)) (ncols : ℕ) : List (List ℚ) :=
  let (R, pivCols) := crref rows ncols
  let freeCols := (List.range ncols).filter (fun j => !pivCols.contains j)
  freeCols.map (fun fc =>
    (List.range ncols).map (fun j =>
      if j = fc then (1 : ℚ)
      else match pivCols.idxOf? j with
        | some pr => - ((R.getD pr []).getD fc 0)   -- pivot column `j` is at RREF row `pr`
        | none => 0))                                -- another free column ⇒ 0

/-- `cConstSolveUniqueQ Arows urhs ncols` solves a rational system when the solution is unique. -/
def cConstSolveUniqueQ (Arows : List (List ℚ)) (urhs : List ℚ) (ncols : ℕ) : Option (List ℚ) :=
  let aug := List.zipWith (fun r u => r ++ [u]) Arows urhs
  let (R, pivCols) := crref aug (ncols + 1)
  if pivCols.contains ncols then none           -- pivot in the rhs column: inconsistent
  else if pivCols.length < ncols then none       -- a free variable: not unique
  else
    -- full rank: variable `j` (pivot column) reads its value off the augmented entry of its pivot row.
    some ((List.range ncols).map (fun j =>
      match pivCols.idxOf? j with
      | some pr => (R.getD pr []).getD ncols 0
      | none => 0))

/-- Return a particular solution of a consistent rational system, setting free variables to zero. -/
def cConstSolveAnyQ (Arows : List (List ℚ)) (urhs : List ℚ) (ncols : ℕ) : Option (List ℚ) :=
  let aug := List.zipWith (fun r u => r ++ [u]) Arows urhs
  let (R, pivCols) := crref aug (ncols + 1)
  if pivCols.contains ncols then none
  else
    some ((List.range ncols).map (fun j =>
      match pivCols.idxOf? j with
      | some pr => (R.getD pr []).getD ncols 0
      | none => 0))

/-- `getD` within range reads the element. -/
theorem getD_lt_gen {α : Type*} (l : List α) (n : ℕ) (d : α) (hn : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl

/-- `getD` past the end is the default. -/
theorem getD_long_gen {α : Type*} (l : List α) (n : ℕ) (d : α) (hn : l.length ≤ n) :
    l.getD n d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hn]; rfl

end DensePoly

/-- The existing rational RREF implementation supplies the abstract linear-solver capability. -/
instance instCLinearSolveRat : CLinearSolve ℚ where
  solveUnique := DensePoly.cConstSolveUniqueQ
  solveAny := DensePoly.cConstSolveAnyQ

end DeepWiki.SymbolicIntegration
