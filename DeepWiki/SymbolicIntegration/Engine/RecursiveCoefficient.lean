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
  /-- Attempt Bronstein's single-`w` limited integration, returning the rational and constant parts.
  The default uses an ordinary recursive antiderivative and a zero constant part. -/
  limitedIntegrate : α → α → Option (α × α) := fun _ c =>
    integrate c |>.map fun b => (b, CCommRing.zero)

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

/-- A pair `(b,r)` solves limited integration when `c = D b + r·η` and `D r = 0`. -/
def IsLimitedCoefficientResult (η c b r : α) : Prop :=
  CFieldSpec.toK c = CFieldSpec.toK (CDiffField.cderiv b) +
    CFieldSpec.toK r * CFieldSpec.toK η ∧
  CFieldSpec.toK (CDiffField.cderiv r) = 0

/-- A coefficient has a limited antiderivative with constant remainder relative to `η`. -/
def IsLimitedCoefficientIntegrable (η c : α) : Prop :=
  ∃ b r : α, IsLimitedCoefficientResult η c b r

/-- Denotation-level soundness contract for recursive limited integration. -/
class LawfulCLimitedCoefficientIntegrator (C : CRecursiveCoefficientIntegrator α) : Prop where
  /-- Every returned pair witnesses the limited-integration identity. -/
  limited_sound : ∀ (η c b r : α), C.limitedIntegrate η c = some (b, r) →
    IsLimitedCoefficientResult η c b r

/-- Relative-completeness contract for recursive limited integration. -/
class CompleteCLimitedCoefficientIntegrator (C : CRecursiveCoefficientIntegrator α)
    [LawfulCLimitedCoefficientIntegrator C] : Prop where
  /-- Every limited-integrable coefficient is accepted. -/
  limited_complete : ∀ (η c : α), IsLimitedCoefficientIntegrable η c →
    ∃ b r, C.limitedIntegrate η c = some (b, r) ∧ IsLimitedCoefficientResult η c b r

end DeepWiki.SymbolicIntegration
