import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv

/-! # Recursive coefficient-field integration capability

The coefficient recursion used by transcendental tower cases is an executable operation in its own
right. This interface isolates it from any particular polynomial representation or monomial solver. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Prop-free recursive coefficient-field integration operation. -/
structure CRecursiveCoefficientIntegrator (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate a coefficient in the immediately lower differential field, if possible. -/
  integrate : α → Option α

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]

/-- Denotation-level soundness contract for recursive coefficient integration. -/
class LawfulCRecursiveCoefficientIntegrator (C : CRecursiveCoefficientIntegrator α) : Prop where
  /-- Every returned coefficient differentiates to the requested input. -/
  sound : ∀ (c b : α), C.integrate c = some b →
    CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c

/-- Relative-completeness contract for recursive coefficient integration. -/
class CompleteCRecursiveCoefficientIntegrator (C : CRecursiveCoefficientIntegrator α) : Prop where
  /-- Every coefficient with a denotational antiderivative is accepted. -/
  complete : ∀ c : α,
    (∃ b : α, CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c) →
      ∃ b, C.integrate c = some b

end DeepWiki.SymbolicIntegration
