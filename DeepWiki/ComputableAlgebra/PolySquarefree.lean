import DeepWiki.ComputableAlgebra.PolyEuclidean

/-! # Representation-independent squarefree decomposition

Yun's multiplicity-indexed squarefree decomposition is composed from the selected polynomial engine
and Euclidean algorithms, so dense and sparse representations share one executable kernel.
-/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Executable squarefree decomposition selected by a computable polynomial representation. -/
class CPolySquarefree (P : Type u → Type u) [CPoly P] [CPolyEngine P] [CPolyEuclidean P] where
  /-- Return the multiplicity-indexed squarefree factors of a represented polynomial. -/
  compute : {α : Type u} → [CField α] → P α → List (P α)

namespace CPolySquarefree

/-- Internal bounded Yun loop producing the successive multiplicity factors. -/
private def defaultGo {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [CPolyEuclidean P] {α : Type u} [CField α] : ℕ → P α → P α → List (P α)
  | 0, _, _ => []
  | fuel + 1, b, d =>
    if CPolyEngine.cdeg b = 0 then []
    else
      let factor := CPolyEngine.cmonic (CPolyEuclidean.gcdExt b d).1
      let quotient := CPolyEuclidean.div b factor
      let residual := CPolyEngine.sub (CPolyEuclidean.div d factor)
        (CPolyEngine.deriv quotient)
      factor :: defaultGo fuel quotient residual

/-- Representation-generic Yun decomposition built from the selected engine and Euclidean operations. -/
def default {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (p : P α) : List (P α) :=
  let gcd := (CPolyEuclidean.gcdExt p (CPolyEngine.deriv p)).1
  let base := CPolyEuclidean.div p gcd
  let residual := CPolyEngine.sub (CPolyEuclidean.div (CPolyEngine.deriv p) gcd)
    (CPolyEngine.deriv base)
  defaultGo (CPoly.degBound p) base residual

end CPolySquarefree

/-- Sparse polynomials select the representation-generic Yun kernel. -/
instance instCPolySquarefreeSparse : CPolySquarefree CPoly.SparsePoly where
  compute := CPolySquarefree.default

namespace CPoly

/-- Yun squarefree decomposition selected for the polynomial representation, ordered by multiplicity. -/
def squarefreeYun {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    [CPolySquarefree P] {α : Type u} [CField α] (p : P α) : List (P α) :=
  CPolySquarefree.compute p

/-- Sparse selected Yun decomposition unfolds to the representation-generic kernel. -/
@[simp] theorem squarefreeYun_sparse_eq {α : Type u} [CField α] (p : CPoly.SparsePoly α) :
    squarefreeYun p = CPolySquarefree.default p := rfl

/-- Nonconstant selected Yun factors paired with their one-based multiplicities. -/
def squarefreeYunFactors {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    [CPolySquarefree P]
    {α : Type u} [CField α] (p : P α) : List (P α × ℕ) :=
  (squarefreeYun p).zipIdx.filterMap fun (q, i) =>
    if CPolyEngine.cdeg q = 0 then none else some (q, i + 1)

/-- Sparse Yun decomposition preserves multiplicities for `(x - 1)²(x + 2)`. -/
example :
    let p : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 2), (1, -3), (3, 1)]
    squarefreeYun p =
      [CPoly.SparsePoly.ofList [(0, 2), (1, 1)],
        CPoly.SparsePoly.ofList [(0, -1), (1, 1)]] := by
  ccompute

/-- Sparse Yun factor pairs retain their one-based multiplicities. -/
example :
    let p : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 2), (1, -3), (3, 1)]
    squarefreeYunFactors p =
      [(CPoly.SparsePoly.ofList [(0, 2), (1, 1)], 1),
        (CPoly.SparsePoly.ofList [(0, -1), (1, 1)], 2)] := by
  ccompute

end CPoly

end DeepWiki.SymbolicIntegration
