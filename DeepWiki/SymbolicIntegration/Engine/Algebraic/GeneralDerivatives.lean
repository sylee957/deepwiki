import DeepWiki.SymbolicIntegration.Engine.Algebraic.IntegralBasisFull

/-! # Base partial derivatives for general algebraic-function curves

The coefficientwise `x`-partial derivative for a curve polynomial `f ∈ K(x)[y]`;
the formal `y`-partial derivative is the canonical `DensePoly.cderiv`. -/

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

variable [CDiffField α]

/-- The coefficientwise base derivative `∂f/∂x` of a general curve polynomial. -/
def afFx (f : DensePoly α) : DensePoly α := (f : List α).map CDiffField.cderiv

end DensePoly

end DeepWiki.SymbolicIntegration
