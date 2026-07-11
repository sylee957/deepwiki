import DeepWiki.ComputableAlgebra.Field

/-! # Abstract executable linear algebra

`CLinearSolve` separates unique, particular, and homogeneous-kernel linear-system computations from
their implementation. `LawfulCLinearSolve` supplies the shape and row-equation guarantees consumed by
symbolic-integration proofs; `CLinearSolve.matrixInverse` derives square-matrix inversion from the
selected unique solver. Concrete solvers remain responsible for providing the operations and laws. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Dot product of two coefficient lists, truncated at the shorter list. -/
def linearDot {α : Type u} [CCommRing α] (row x : List α) : α :=
  (List.zipWith CCommRing.mul row x).foldr CCommRing.add CCommRing.zero

/-- A returned vector solves row `i` of a coefficient matrix against the right-hand side. -/
def linearSolveRow {α : Type u} [CCommRing α]
    (rows : List (List α)) (rhs x : List α) (i : ℕ) : Prop :=
  linearDot (rows.getD i []) x = rhs.getD i CCommRing.zero

/-- Executable linear-system solving over a computable field. -/
class CLinearSolve (α : Type u) [CField α] where
  /-- Solve a system with `ncols` unknowns when it has a unique solution. -/
  solveUnique : List (List α) → List α → ℕ → Option (List α)
  /-- Return a particular solution of a consistent system, allowing free variables. -/
  solveAny : List (List α) → List α → ℕ → Option (List α)
  /-- Return a basis of the nullspace of a homogeneous system with `ncols` unknowns. -/
  nullspaceBasis : List (List α) → ℕ → List (List α)

/-- Reduce a computable-field matrix to row-echelon form, returning its pivot columns. -/
def gaussElim {α : Type u} [CField α] (ncols : ℕ) (rows : List (List α)) :
    List (List α) × List ℕ :=
  let step : (List (List α) × ℕ × List ℕ) → ℕ → (List (List α) × ℕ × List ℕ) :=
    fun (rs, pr, piv) col =>
      if pr ≥ rs.length then (rs, pr, piv)
      else
        match (List.range rs.length).find?
            (fun i => i ≥ pr && (!CCommRing.isZero (rs[i]!.getD col CCommRing.zero))) with
        | none => (rs, pr, piv)
        | some i =>
          let rowPr := rs[pr]!
          let rowI := rs[i]!
          let rs := rs.set pr rowI |>.set i rowPr
          let pivotRow := rs[pr]!
          let lead := pivotRow.getD col CCommRing.zero
          let pivotRow := pivotRow.map (fun a => CField.div a lead)
          let rs := rs.set pr pivotRow
          let rs := (List.range rs.length).foldl (fun acc r =>
            if r = pr then acc
            else
              let row := acc[r]!
              let factor := row.getD col CCommRing.zero
              if CCommRing.isZero factor then acc
              else
                let newRow := (List.range ncols).map (fun c =>
                  CField.sub (row.getD c CCommRing.zero)
                    (CCommRing.mul factor (pivotRow.getD c CCommRing.zero)))
                acc.set r newRow) rs
          (rs, pr + 1, col :: piv)
  let (rs, _, pivRev) := (List.range ncols).foldl step (rows, 0, [])
  (rs, pivRev.reverse)

namespace CLinearSolve

/-- Generic particular solve obtained from computable-field Gauss–Jordan elimination. -/
private def gaussSolveAny {α : Type u} [CField α] (rows : List (List α)) (rhs : List α)
    (ncols : ℕ) : Option (List α) :=
  let aug := List.zipWith (fun row b => row ++ [b]) rows rhs
  let (reduced, pivots) := gaussElim (ncols + 1) aug
  if pivots.contains ncols then none
  else
    some ((List.range ncols).map (fun j =>
      match pivots.idxOf? j with
      | some r => (reduced.getD r []).getD ncols CCommRing.zero
      | none => CCommRing.zero))

/-- Generic unique solve obtained from computable-field Gauss–Jordan elimination. -/
private def gaussSolveUnique {α : Type u} [CField α] (rows : List (List α)) (rhs : List α)
    (ncols : ℕ) : Option (List α) :=
  let aug := List.zipWith (fun row b => row ++ [b]) rows rhs
  let (reduced, pivots) := gaussElim (ncols + 1) aug
  if pivots.contains ncols then none
  else if pivots.length < ncols then none
  else
    some ((List.range ncols).map (fun j =>
      match pivots.idxOf? j with
      | some r => (reduced.getD r []).getD ncols CCommRing.zero
      | none => CCommRing.zero))

/-- Generic nullspace basis obtained from computable-field Gauss–Jordan elimination. -/
private def gaussNullspaceBasis {α : Type u} [CField α] (rows : List (List α))
    (ncols : ℕ) : List (List α) :=
  let (reduced, pivots) := gaussElim ncols rows
  let freeCols := (List.range ncols).filter (fun j => !pivots.contains j)
  freeCols.map (fun free =>
    let base := (List.range ncols).map (fun j =>
      if j = free then (CCommRing.one : α) else CCommRing.zero)
    (List.range pivots.length).foldl (fun acc r =>
      let pivot := pivots[r]!
      let value := CCommRing.neg ((reduced[r]!).getD free CCommRing.zero)
      acc.set pivot value) base)

/-! The generic implementation is an explicit builder, not a global fallback instance: callers choose it
when no representation-specific solver is available, avoiding incoherent hidden instance arguments. -/

/-- Build the generic Gauss–Jordan linear-solver implementation over a computable field. -/
@[reducible]
def gauss {α : Type u} [CField α] : CLinearSolve α where
  solveUnique := gaussSolveUnique
  solveAny := gaussSolveAny
  nullspaceBasis := gaussNullspaceBasis

/-- Invert a square matrix by solving its columns against the standard basis through the selected
`CLinearSolve.solveUnique` operation. -/
def matrixInverse {α : Type u} [CField α] [CLinearSolve α]
    (n : ℕ) (rows : List (List α)) : Option (List (List α)) :=
  let columns := (List.range n).map (fun j =>
    CLinearSolve.solveUnique rows
      ((List.range n).map (fun i => if i = j then CCommRing.one else CCommRing.zero)) n)
  if columns.all Option.isSome then
    some ((List.range n).map (fun i =>
      (List.range n).map (fun j =>
        (Option.getD (columns.getD j none) []).getD i CCommRing.zero)))
  else none

/-- A returned selected matrix inverse has the requested number of rows. -/
theorem matrixInverse_length {α : Type u} [CField α] [CLinearSolve α]
    (n : ℕ) (rows inverse : List (List α))
    (h : matrixInverse n rows = some inverse) : inverse.length = n := by
  simp only [matrixInverse] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst inverse
    simp
  · simp at h

/-- Every row of a returned selected matrix inverse has the requested width. -/
theorem matrixInverse_row_length {α : Type u} [CField α] [CLinearSolve α]
    (n : ℕ) (rows inverse : List (List α))
    (h : matrixInverse n rows = some inverse) :
    ∀ row ∈ inverse, row.length = n := by
  simp only [matrixInverse] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst inverse
    simp
  · simp at h

end CLinearSolve

/-- Select the first vector returned by an abstract homogeneous-kernel computation. -/
def kernelVector {α : Type u} [CField α] [CLinearSolve α]
    (ncols : ℕ) (rows : List (List α)) : Option (List α) :=
  (CLinearSolve.nullspaceBasis rows ncols).head?

/-- Lawful interface for executable system solves and homogeneous-kernel vector shape. -/
class LawfulCLinearSolve (α : Type u) [CField α] [CLinearSolve α] where
  /-- A returned unique solution has exactly the requested number of columns. -/
  solveUnique_length : ∀ (rows : List (List α)) (rhs : List α) (ncols : ℕ) (x : List α),
    CLinearSolve.solveUnique rows rhs ncols = some x → x.length = ncols
  /-- A returned solution satisfies every row equation when the input matrix is well formed. -/
  solveUnique_sound : ∀ (rows : List (List α)) (rhs : List α) (ncols : ℕ) (x : List α),
    (∀ row ∈ rows, row.length = ncols) → rows.length = rhs.length →
      CLinearSolve.solveUnique rows rhs ncols = some x →
        ∀ i, i < rows.length → linearSolveRow rows rhs x i
  /-- A returned particular solution has exactly the requested number of columns. -/
  solveAny_length : ∀ (rows : List (List α)) (rhs : List α) (ncols : ℕ) (x : List α),
    CLinearSolve.solveAny rows rhs ncols = some x → x.length = ncols
  /-- A returned particular solution satisfies every row equation when the matrix is well formed. -/
  solveAny_sound : ∀ (rows : List (List α)) (rhs : List α) (ncols : ℕ) (x : List α),
    (∀ row ∈ rows, row.length = ncols) → rows.length = rhs.length →
      CLinearSolve.solveAny rows rhs ncols = some x →
        ∀ i, i < rows.length → linearSolveRow rows rhs x i
  /-- Every returned nullspace vector has exactly the requested number of columns. -/
  nullspaceBasis_length : ∀ (rows : List (List α)) (ncols : ℕ) (x : List α),
    x ∈ CLinearSolve.nullspaceBasis rows ncols → x.length = ncols
  /-- Every returned nullspace vector solves each row of a well-formed homogeneous system. -/
  nullspaceBasis_sound : ∀ (rows : List (List α)) (ncols : ℕ) (x : List α),
    (∀ row ∈ rows, row.length = ncols) →
    x ∈ CLinearSolve.nullspaceBasis rows ncols →
      ∀ i, i < rows.length → linearDot (rows.getD i []) x = CCommRing.zero

/-- A selected kernel vector belongs to the abstract nullspace basis. -/
theorem mem_nullspaceBasis_of_kernelVector_eq_some {α : Type u} [CField α] [CLinearSolve α]
    (rows : List (List α)) (ncols : ℕ) (x : List α)
    (h : kernelVector ncols rows = some x) :
    x ∈ CLinearSolve.nullspaceBasis rows ncols := by
  unfold kernelVector at h
  cases hbasis : CLinearSolve.nullspaceBasis rows ncols with
  | nil => simp [hbasis] at h
  | cons y ys =>
    simp [hbasis] at h
    subst y
    exact List.mem_cons_self

/-- A lawful selected kernel vector has exactly the requested number of columns. -/
theorem kernelVector_length {α : Type u} [CField α] [CLinearSolve α] [LawfulCLinearSolve α]
    (rows : List (List α)) (ncols : ℕ) (x : List α)
    (h : kernelVector ncols rows = some x) : x.length = ncols :=
  LawfulCLinearSolve.nullspaceBasis_length rows ncols x
    (mem_nullspaceBasis_of_kernelVector_eq_some rows ncols x h)

/-- A lawful selected kernel vector solves every row of a well-formed homogeneous system. -/
theorem kernelVector_sound {α : Type u} [CField α] [CLinearSolve α] [LawfulCLinearSolve α]
    (rows : List (List α)) (ncols : ℕ) (x : List α)
    (hwidth : ∀ row ∈ rows, row.length = ncols)
    (h : kernelVector ncols rows = some x) :
    ∀ i, i < rows.length → linearDot (rows.getD i []) x = CCommRing.zero :=
  LawfulCLinearSolve.nullspaceBasis_sound rows ncols x hwidth
    (mem_nullspaceBasis_of_kernelVector_eq_some rows ncols x h)

end DeepWiki.SymbolicIntegration
