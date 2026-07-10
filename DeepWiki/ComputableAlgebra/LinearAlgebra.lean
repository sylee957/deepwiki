import DeepWiki.ComputableAlgebra.Field

/-! # Abstract executable linear algebra

`CLinearSolve` separates the executable linear-system operation from its implementation. `LawfulCLinearSolve`
supplies the length and row-equation guarantees consumed by symbolic-integration proofs; concrete solvers
remain responsible for providing the operation and its laws. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Dot product of two coefficient lists, truncated at the shorter list. -/
def linearDot {α : Type u} [CCommRing α] (row x : List α) : α :=
  (List.zipWith CCommRing.mul row x).foldr CCommRing.add CCommRing.zero

/-- A returned vector solves row `i` of a coefficient matrix against the right-hand side. -/
def linearSolveRow {α : Type u} [CCommRing α]
    (rows : List (List α)) (rhs x : List α) (i : ℕ) : Prop :=
  linearDot (rows.getD i []) x = rhs.getD i CCommRing.zero

/-- Executable unique-solution linear solver over a computable field. -/
class CLinearSolve (α : Type u) [CField α] where
  /-- Solve a system with `ncols` unknowns when it has a unique solution. -/
  solveUnique : List (List α) → List α → ℕ → Option (List α)

/-- Lawful interface for the executable unique-solution linear solver. -/
class LawfulCLinearSolve (α : Type u) [CField α] [CLinearSolve α] where
  /-- A returned unique solution has exactly the requested number of columns. -/
  solveUnique_length : ∀ (rows : List (List α)) (rhs : List α) (ncols : ℕ) (x : List α),
    CLinearSolve.solveUnique rows rhs ncols = some x → x.length = ncols
  /-- A returned solution satisfies every row equation when the input matrix is well formed. -/
  solveUnique_sound : ∀ (rows : List (List α)) (rhs : List α) (ncols : ℕ) (x : List α),
    (∀ row ∈ rows, row.length = ncols) → rows.length = rhs.length →
      CLinearSolve.solveUnique rows rhs ncols = some x →
        ∀ i, i < rows.length → linearSolveRow rows rhs x i

end DeepWiki.SymbolicIntegration
