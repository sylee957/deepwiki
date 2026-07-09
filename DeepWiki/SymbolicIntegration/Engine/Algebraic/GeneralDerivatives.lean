import DeepWiki.SymbolicIntegration.Engine.Algebraic.IntegralBasisFull

/-! # Partial derivatives for general algebraic-function curves

Formal `x`- and `y`-partial derivatives for a curve polynomial `f ∈ K(x)[y]`,
with their denotation bridges. -/

namespace DeepWiki.SymbolicIntegration

namespace CPoly

variable {α : Type*} [CField α]

/-- The formal `y`-derivative `∂f/∂y` of a general curve polynomial. -/
def afFy (f : CPoly α) : CPoly α := cderiv f

section AfFyDenote

variable [CFieldSpec α]

/-- `afFy` reads as the formal derivative through `toPoly`. -/
theorem derivative_toPolyG_eq_afFy (f : CPoly α) :
    Polynomial.derivative (toPoly f) = toPoly (afFy f) := by
  simp only [afFy, denote]

end AfFyDenote

variable [CDiffField α]

/-- The coefficientwise base derivative `∂f/∂x` of a general curve polynomial. -/
def afFx (f : CPoly α) : CPoly α := (f : List α).map CDiffField.cderiv

end CPoly

end DeepWiki.SymbolicIntegration
