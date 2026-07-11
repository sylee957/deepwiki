import DeepWiki.ComputableAlgebra.PolyGcdAlgorithms
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv

/-! # Representation-independent differential split factorization

The normal/special polynomial split composes the selected gcd and Euclidean algorithms with the
representation-independent monomial derivative.
-/

namespace DeepWiki.SymbolicIntegration

universe u

namespace CPoly

/-- Internal bounded driver for differential normal/special factorization. -/
private def splitFactorAux {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] {α : Type u} [CField α] [CDiffField α]
    (Dt : P α) : ℕ → P α → P α × P α
  | 0, p => (p, CPoly.one)
  | fuel + 1, p =>
    let implicitGcd := CPolyGcd.compute p (DensePoly.cmonomialDeriv Dt p)
    let formalGcd := CPolyGcd.compute p (CPolyEngine.deriv p)
    let special := CPolyEuclidean.div implicitGcd formalGcd
    if CPolyEngine.cdeg special = 0 then (p, CPoly.one)
    else
      let quotient := CPolyEuclidean.div p special
      if CPolyEngine.cdeg quotient < CPolyEngine.cdeg p then
        let parts := splitFactorAux Dt fuel quotient
        (parts.1, CPolyEngine.mul special parts.2)
      else (p, CPoly.one)

/-- Split a represented differential polynomial into its normal and special factors. -/
def splitFactor {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] {α : Type u} [CField α] [CDiffField α]
    (Dt p : P α) : P α × P α :=
  splitFactorAux Dt (CPoly.degBound p) p

/-- Sparse splitting with the zero derivation extracts `(x - 1)²` as entirely special. -/
example :
    let p : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 1), (1, -2), (2, 1)]
    let parts := splitFactor (CPoly.czero : CPoly.SparsePoly ℚ) p
    CPolyEngine.cdeg parts.1 = 0
      ∧ CPolyEngine.cisZero
          (CPolyEngine.sub (CPolyEngine.mul parts.1 parts.2) p) = true := by
  ccompute

end CPoly

end DeepWiki.SymbolicIntegration
