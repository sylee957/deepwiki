import DeepWiki.SymbolicIntegration.Engine.Algebraic.IntegralBasisFull
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv

/-! # Base partial derivatives for general algebraic-function curves

The representation-independent coefficientwise `x`-partial derivative for a curve polynomial
`f ∈ K(x)[y]`; the formal `y`-partial derivative is the polynomial-engine derivative. -/

namespace DeepWiki.SymbolicIntegration

universe u

namespace DensePoly

variable {α : Type u} [CField α]

variable [CDiffField α]

/-- The coefficientwise base derivative `∂f/∂x` of a general curve polynomial. -/
abbrev afFx {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    (f : P α) : P α := cmapDeriv f

example :
    let p : CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList [1, 2, 3]
    CPolyEngine.cisZero (afFx p) = true := by
  native_decide

end DensePoly

end DeepWiki.SymbolicIntegration
