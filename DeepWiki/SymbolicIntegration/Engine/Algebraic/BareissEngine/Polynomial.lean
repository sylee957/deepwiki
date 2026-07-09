import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Engine.Algebraic.HermiteNormalForm
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Fraction-free polynomial Bareiss engine

The fraction-free determinant `bareissDet`, adjugate `bareissAdjugate`, and Cramer solve
`bareissSolve` over `ℚ[x]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### Matrix entry access and the Bareiss single-step over `ℚ[x]` -/

/-- Read the polynomial entry `M[i][j]` of a `ℚ[x]`-matrix, the zero polynomial `[]` past the end. -/
def getEntry (M : List (List (DensePoly α))) (i j : ℕ) : DensePoly α :=
  (M.getD i []).getD j []

/-- One Bareiss fraction-free elimination step with pivot index `k` and previous pivot `prevPiv`: each
entry `[i][j]` with `i, j > k` becomes `(M[k][k]·M[i][j] − M[i][k]·M[k][j]) / prevPiv` (an exact
division); other entries are unchanged. -/
def bareissStep (prevPiv : DensePoly α) (k : ℕ) (M : List (List (DensePoly α))) :
    List (List (DensePoly α)) :=
  let mkk := getEntry M k k
  (List.range M.length).map (fun i =>
    (List.range (M.getD i []).length).map (fun j =>
      if k < i ∧ k < j then
        let num := csub (cmul mkk (getEntry M i j)) (cmul (getEntry M i k) (getEntry M k j))
        cdivWf num prevPiv
      else getEntry M i j))

/-- Bareiss elimination driver: run `bareissStep` for pivot indices `k = 0, 1, …` carrying the previous
pivot, one step per pivot; returns the reduced matrix whose `[n-1][n-1]` entry is `det M`. -/
def bareissDrive : ℕ → DensePoly α → ℕ → List (List (DensePoly α)) → List (List (DensePoly α))
  | 0, _, _, M => M
  | fuel + 1, prevPiv, k, M =>
    let M' := bareissStep prevPiv k M
    bareissDrive fuel (getEntry M' k k) (k + 1) M'

/-- The Bareiss fraction-free determinant over `ℚ[x]` `bareissDet M`: run `bareissDrive` for `n =
M.length` pivots and read the final pivot `M⁽ⁿ⁾[n-1][n-1]`; the empty matrix has determinant `1`. -/
def bareissDet (M : List (List (DensePoly α))) : DensePoly α :=
  let n := M.length
  if n = 0 then [CField.one]
  else
    let M' := bareissDrive n [CField.one] 0 M
    getEntry M' (n - 1) (n - 1)

/-! ### Fraction-free solve and adjugate (the inverse representation `(det, adjugate)`) -/

/-- Delete row `i` and column `j` from a `ℚ[x]`-matrix (the `(i, j)` minor). -/
def minorMat (M : List (List (DensePoly α))) (i j : ℕ) : List (List (DensePoly α)) :=
  (M.eraseIdx i).map (fun row => row.eraseIdx j)

/-- The adjugate of a `ℚ[x]`-matrix `bareissAdjugate M`, fraction-free: the transpose of the cofactor
matrix, entry `(i, j) = (−1)^{i+j}·det(minor M j i)`; satisfies `M · adj M = (det M)·I`. -/
def bareissAdjugate (M : List (List (DensePoly α))) : List (List (DensePoly α)) :=
  let n := M.length
  (List.range n).map (fun i =>
    (List.range n).map (fun j =>
      let c := bareissDet (minorMat M j i)
      if (i + j) % 2 = 0 then c else cneg c))

/-- Fraction-free linear solve `bareissSolve M b = (det M, det M · x)` where `x = M⁻¹·b`: by Cramer
`det M · x = adj M · b`, the polynomial solution of `M·(det M·x) = det M·b` over `ℚ[x]`. -/
def bareissSolve (M : List (List (DensePoly α))) (b : List (DensePoly α)) : DensePoly α × List (DensePoly α) :=
  let n := M.length
  let adj := bareissAdjugate M
  let sol := (List.range n).map (fun i =>
    (List.range n).foldl (fun acc j =>
      cadd acc (cmul (getEntry adj i j) (b.getD j []))) [])
  (bareissDet M, sol)

end DensePoly

end DeepWiki.SymbolicIntegration
