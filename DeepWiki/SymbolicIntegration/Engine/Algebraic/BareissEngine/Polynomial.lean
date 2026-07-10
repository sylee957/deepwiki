import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Engine.Algebraic.HermiteNormalForm
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Representation-independent fraction-free polynomial Bareiss engine

The fraction-free determinant `bareissDet`, adjugate `bareissAdjugate`, and Cramer solve
`bareissSolve` select polynomial arithmetic and exact division through abstract capabilities. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPoly

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
variable {α : Type u} [CField α]

/-! ### The Bareiss single-step -/

/-- One representation-independent Bareiss step with pivot index `k` and previous pivot `prevPiv`: each
entry `[i][j]` with `i, j > k` becomes `(M[k][k]·M[i][j] − M[i][k]·M[k][j]) / prevPiv` (an exact
division); other entries are unchanged. -/
def bareissStep (prevPiv : P α) (k : ℕ) (M : List (List (P α))) : List (List (P α)) :=
  let mkk := polyMatGet M k k
  (List.range M.length).map (fun i =>
    (List.range (M.getD i []).length).map (fun j =>
      if k < i ∧ k < j then
        let num := CPolyEngine.sub (CPolyEngine.mul mkk (polyMatGet M i j))
          (CPolyEngine.mul (polyMatGet M i k) (polyMatGet M k j))
        CPolyEuclidean.div num prevPiv
      else polyMatGet M i j))

/-- Bareiss elimination driver: run `bareissStep` for pivot indices `k = 0, 1, …` carrying the previous
pivot, one step per pivot; returns the reduced matrix whose `[n-1][n-1]` entry is `det M`. -/
def bareissDrive : ℕ → P α → ℕ → List (List (P α)) → List (List (P α))
  | 0, _, _, M => M
  | fuel + 1, prevPiv, k, M =>
    let M' := bareissStep prevPiv k M
    bareissDrive fuel (polyMatGet M' k k) (k + 1) M'

/-- The represented-polynomial Bareiss determinant `bareissDet M`: run `bareissDrive` for `n =
M.length` pivots and read the final pivot `M⁽ⁿ⁾[n-1][n-1]`; the empty matrix has determinant `1`. -/
def bareissDet (M : List (List (P α))) : P α :=
  let n := M.length
  if n = 0 then CPoly.one
  else
    let M' := bareissDrive n CPoly.one 0 M
    polyMatGet M' (n - 1) (n - 1)

/-! ### Fraction-free solve and adjugate (the inverse representation `(det, adjugate)`) -/

/-- Delete row `i` and column `j` from a represented-polynomial matrix. -/
def minorMat (M : List (List (P α))) (i j : ℕ) : List (List (P α)) :=
  (M.eraseIdx i).map (fun row => row.eraseIdx j)

/-- The fraction-free adjugate `bareissAdjugate M`: the transpose of the cofactor
matrix, entry `(i, j) = (−1)^{i+j}·det(minor M j i)`; satisfies `M · adj M = (det M)·I`. -/
def bareissAdjugate (M : List (List (P α))) : List (List (P α)) :=
  let n := M.length
  (List.range n).map (fun i =>
    (List.range n).map (fun j =>
      let c := bareissDet (minorMat M j i)
      if (i + j) % 2 = 0 then c else CPolyEngine.neg c))

/-- Fraction-free linear solve `bareissSolve M b = (det M, det M · x)` where `x = M⁻¹·b`: by Cramer
`det M · x = adj M · b`, the polynomial solution of `M·(det M·x) = det M·b` over `ℚ[x]`. -/
def bareissSolve (M : List (List (P α))) (b : List (P α)) : P α × List (P α) :=
  let n := M.length
  let adj := bareissAdjugate M
  let sol := (List.range n).map (fun i =>
    (List.range n).foldl (fun acc j =>
      CPolyEngine.add acc
        (CPolyEngine.mul (polyMatGet adj i j) (b.getD j CPoly.czero))) CPoly.czero)
  (bareissDet M, sol)

-- The same Bareiss core executes over the sparse polynomial representation.
example :
    bareissDet (P := CPoly.SparsePoly)
      [[(CPoly.one : CPoly.SparsePoly ℚ)]] =
        (CPoly.one : CPoly.SparsePoly ℚ) := by
  rfl

end CPoly

end DeepWiki.SymbolicIntegration
