import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.ComputableAlgebra.PolyInterpolate

/-! # Representation-selected polynomial subresultants

`CPolySubresultant` selects an executable subresultant algorithm for a computable polynomial
representation. Its denotation law lives with the abstract subresultant theory in SymbolicIntegration.
-/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Executable subresultant polynomial selected by a computable polynomial representation. -/
class CPolySubresultant (P : Type u → Type u) [CPoly P] where
  /-- Compute the `j`-th subresultant at the supplied formal degrees `n` and `m`. -/
  compute : {α : Type u} → [CField α] → P α → P α → ℕ → ℕ → ℕ → P α

namespace CPolySubresultant

/-- Cofactor-expansion determinant on a row-list matrix, indexed by its intended dimension. -/
def detAux {α : Type u} [CField α] : ℕ → List (List α) → α
  | 0, _ => CCommRing.one
  | _ + 1, [] => CCommRing.one
  | n + 1, row :: rest =>
    ((List.range (n + 1)).map (fun j =>
      let aij := row.getD j CCommRing.zero
      let minor := rest.map (fun r => r.take j ++ r.drop (j + 1))
      let term := CCommRing.mul aij (detAux n minor)
      if j % 2 = 0 then term else CCommRing.neg term)).foldl CCommRing.add CCommRing.zero

/-- Determinant of a square row-list matrix. -/
def det {α : Type u} [CField α] (M : List (List α)) : α := detAux M.length M

/-- The exact Sylvester matrix used by the selected subresultant algorithm. -/
def bSylvesterRows {α : Type u} [CField α] {P : Type u → Type u} [CPoly P]
    (p q : P α) (n m : ℕ) : List (List α) :=
  let width := m + n
  let arow (i : ℕ) : List α := (List.range width).map (fun l =>
    if i ≤ l ∧ l ≤ i + n then CPoly.coeff p (n + i - l) else CCommRing.zero)
  let brow (i : ℕ) : List α := (List.range width).map (fun l =>
    if i - m ≤ l ∧ l ≤ i then CPoly.coeff q (i - l) else CCommRing.zero)
  (List.range m).map (fun i => arow i) ++ (List.range n).map (fun jj => brow (m + jj))

/-- Row indices of the selected `j`-th Sylvester submatrix. -/
def subRowIdx (n m j : ℕ) : List ℕ :=
  (List.range (m + n - 2 * j)).map (fun t => if t < m - j then t else t + j)

/-- Column indices of one coefficient minor of the selected `j`-th subresultant. -/
def subColIdx (n m j i : ℕ) : List ℕ :=
  (List.range (m + n - 2 * j)).map
    (fun s => if s < m + n - 2 * j - 1 then s else m + n - i - j - 1)

/-- Extract a row- and column-indexed submatrix from a row-list matrix. -/
def submatrix {α : Type u} [CField α] (M : List (List α))
    (rows cols : List ℕ) : List (List α) :=
  rows.map (fun r => cols.map (fun c => (M.getD r []).getD c CCommRing.zero))

/-- Default Sylvester-submatrix implementation of the `j`-th polynomial subresultant. -/
def default {α : Type u} [CField α] {P : Type u → Type u} [CPoly P]
    (p q : P α) (n m j : ℕ) : P α :=
  CPoly.ofFn (j + 1) (fun i =>
    det (submatrix (bSylvesterRows p q n m) (subRowIdx n m j) (subColIdx n m j i)))

end CPolySubresultant

/-- Dense polynomials use the representation-independent Sylvester-submatrix implementation. -/
instance instCPolySubresultantDense : CPolySubresultant DensePoly where
  compute := CPolySubresultant.default

/-- Sparse polynomials use the representation-independent Sylvester-submatrix implementation. -/
instance instCPolySubresultantSparse : CPolySubresultant CPoly.SparsePoly where
  compute := CPolySubresultant.default

namespace CPolySubresultant

/-- The parametric subresultant `Sⱼ(z,t)` of `Dstar` and `A − z·Dd`, reconstructed coefficientwise
from evaluations of the selected scalar subresultant. -/
def parametric {α : Type u} [CField α] {P Q : Type u → Type u}
    [CPoly P] [CPolyEngine P] [CPolySubresultant P] [CPoly Q] [CPolyEngine Q]
    [CPolyInterpolate Q]
    (Dstar A Dd : P α) (n m j : ℕ) : List (Q α) :=
  let N := n + m + 1
  (List.range (j + 1)).map (fun k =>
    CPoly.interpolate ((List.range N).map (fun jj =>
      let c := CField.natCast jj
      (c, CPoly.coeff
        (CPolySubresultant.compute Dstar
          (CPolyEngine.sub A (CPolyEngine.scale c Dd)) n m j) k))))

/-- Dense subresultant selection unfolds to the representation-independent default. -/
@[simp] theorem compute_dense_eq {α : Type*} [CField α] (p q : DensePoly α) (n m j : ℕ) :
    CPolySubresultant.compute p q n m j = CPolySubresultant.default p q n m j := rfl

/-- Sparse subresultant selection unfolds to the representation-independent default. -/
@[simp] theorem compute_sparse_eq {α : Type*} [CField α]
    (p q : CPoly.SparsePoly α) (n m j : ℕ) :
    CPolySubresultant.compute p q n m j = CPolySubresultant.default p q n m j := rfl

end CPolySubresultant

end DeepWiki.SymbolicIntegration
