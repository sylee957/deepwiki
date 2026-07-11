import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyReprGcd

/-! # Representation-independent squarefree decomposition

Yun's multiplicity-indexed squarefree decomposition is composed from the selected polynomial engine,
gcd, and Euclidean algorithms, so dense and sparse representations share one executable kernel.
-/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Executable squarefree decomposition selected by a polynomial representation, gcd, and Euclidean engine. -/
class CPolySquarefree (P : Type u → Type u) [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    (α : Type u) [CField α] [CPolyGcd P α] where
  /-- Return the multiplicity-indexed squarefree factors of a represented polynomial. -/
  compute : P α → List (P α)

namespace CPolySquarefree

/-- Bounded Yun loop producing the successive multiplicity factors; kept qualified as a kernel detail. -/
protected def defaultGo {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [CPolyEuclidean P] {α : Type u} [CField α] [CPolyGcd P α] : ℕ → P α → P α → List (P α)
  | 0, _, _ => []
  | fuel + 1, b, d =>
    if CPolyEngine.cdeg b = 0 then []
    else
      let factor := CPolyEngine.cmonic (CPolyGcd.compute b d)
      let quotient := CPolyEuclidean.div b factor
      let residual := CPolyEngine.sub (CPolyEuclidean.div d factor)
        (CPolyEngine.deriv quotient)
      factor :: CPolySquarefree.defaultGo fuel quotient residual

/-- Representation-generic Yun decomposition built from the selected engine and Euclidean operations. -/
def default {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] [CPolyGcd P α] (p : P α) : List (P α) :=
  let gcd := CPolyGcd.compute p (CPolyEngine.deriv p)
  let base := CPolyEuclidean.div p gcd
  let residual := CPolyEngine.sub (CPolyEuclidean.div (CPolyEngine.deriv p) gcd)
    (CPolyEngine.deriv base)
  CPolySquarefree.defaultGo (CPoly.degBound p) base residual

end CPolySquarefree

/-- Sparse polynomials select the representation-generic Yun kernel. -/
instance instCPolySquarefreeSparse {α : Type u} [CField α] :
    CPolySquarefree CPoly.SparsePoly α where
  compute := CPolySquarefree.default

namespace CPoly

/-- Yun squarefree decomposition selected for the polynomial representation, ordered by multiplicity. -/
def squarefreeYun {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolySquarefree P α] (p : P α) : List (P α) :=
  CPolySquarefree.compute p

/-- Sparse selected Yun decomposition unfolds to the representation-generic kernel. -/
@[simp] theorem squarefreeYun_sparse_eq {α : Type u} [CField α] (p : CPoly.SparsePoly α) :
    squarefreeYun p = CPolySquarefree.default p := rfl

/-- Nonconstant selected Yun factors paired with their one-based multiplicities. -/
def squarefreeYunFactors {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolySquarefree P α] (p : P α) : List (P α × ℕ) :=
  (squarefreeYun p).zipIdx.filterMap fun (q, i) =>
    if CPolyEngine.cdeg q = 0 then none else some (q, i + 1)

end CPoly

end DeepWiki.SymbolicIntegration
