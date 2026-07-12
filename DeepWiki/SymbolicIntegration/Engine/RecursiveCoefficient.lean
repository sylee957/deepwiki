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

/-- Elementary antiderivative data returned from the immediately lower coefficient field. -/
structure CoefficientIntegralResult (α : Type u) where
  /-- Rational part of the lower-field antiderivative. -/
  rational : α
  /-- Constant coefficients and nonzero lower-field logarithm arguments. -/
  logs : List (α × α)

/-- Prop-free recursive elementary-integration operation for the immediately lower field. -/
structure CRecursiveElementaryIntegrator (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate a coefficient to a rational part plus lower-field logarithms, if possible. -/
  integrate : α → Option (CoefficientIntegralResult α)

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]

/-- Denotation of the logarithmic terms in a recursive coefficient result. -/
def coefficientLogSum (logs : List (α × α)) : CFieldSpec.K α :=
  (logs.map fun cv => CFieldSpec.toK cv.1 *
    (CFieldSpec.toK (CDiffField.cderiv cv.2) / CFieldSpec.toK cv.2)).sum

/-- A recursive coefficient result is a valid elementary antiderivative of `c`. -/
def IsCoefficientIntegralResult (c : α) (res : CoefficientIntegralResult α) : Prop :=
  CFieldSpec.toK (CDiffField.cderiv res.rational) + coefficientLogSum res.logs =
      CFieldSpec.toK c ∧
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
    (∀ cv ∈ res.logs, CFieldSpec.toK cv.2 ≠ 0)

/-- A coefficient possesses a represented elementary antiderivative in the lower field. -/
def IsCoefficientElementarilyIntegrable (c : α) : Prop :=
  ∃ res : CoefficientIntegralResult α, IsCoefficientIntegralResult c res

/-- Denotation-level soundness of recursive elementary coefficient integration. -/
class LawfulCRecursiveElementaryIntegrator (C : CRecursiveElementaryIntegrator α) : Prop where
  /-- Every returned result is an elementary antiderivative of the requested coefficient. -/
  sound : ∀ (c : α) (res : CoefficientIntegralResult α),
    C.integrate c = some res → IsCoefficientIntegralResult c res

/-- Semantic domain for relative completeness of recursive elementary coefficient integration. -/
abbrev RecursiveElementaryDomain := α → Prop

/-- Domain-relative completeness of recursive elementary coefficient integration. -/
class CompleteCRecursiveElementaryIntegrator (C : CRecursiveElementaryIntegrator α)
    (domain : RecursiveElementaryDomain (α := α)) [LawfulCRecursiveElementaryIntegrator C] : Prop where
  /-- Every in-domain coefficient with a represented elementary antiderivative is accepted. -/
  complete : ∀ c : α, domain c → IsCoefficientElementarilyIntegrable c →
    ∃ res, C.integrate c = some res

/-- Semantic domain on which ordinary recursive coefficient integration is required to be complete. -/
abbrev RecursiveCoefficientDomain := α → Prop

/-- Semantic domain on which recursive limited integration is required to be complete. -/
abbrev LimitedCoefficientDomain := α → α → Prop

/-- Denotation-level soundness contract for recursive coefficient integration. -/
class LawfulCRecursiveCoefficientIntegrator (C : CRecursiveCoefficientIntegrator α) : Prop where
  /-- Every returned coefficient differentiates to the requested input. -/
  sound : ∀ (c b : α), C.integrate c = some b →
    CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c

/-- Domain-relative completeness contract for recursive coefficient integration. -/
class CompleteCRecursiveCoefficientIntegrator (C : CRecursiveCoefficientIntegrator α)
    (domain : RecursiveCoefficientDomain (α := α)) : Prop where
  /-- Every domain coefficient with a denotational antiderivative is accepted. -/
  complete : ∀ c : α, domain c →
    (∃ b : α, CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c) →
      ∃ b, C.integrate c = some b

/-- Regard a log-free recursive coefficient integrator as an elementary integrator with no logs. -/
def recursiveElementaryOfCoefficient (C : CRecursiveCoefficientIntegrator α) :
    CRecursiveElementaryIntegrator α where
  integrate c := C.integrate c |>.map fun b => { rational := b, logs := [] }

/-- A lawful log-free coefficient integrator remains lawful through the elementary-result embedding. -/
instance instLawfulCRecursiveElementaryIntegratorOfCoefficient
    (C : CRecursiveCoefficientIntegrator α) [LawfulCRecursiveCoefficientIntegrator C] :
    LawfulCRecursiveElementaryIntegrator (recursiveElementaryOfCoefficient C) where
  sound c res hrun := by
    rw [recursiveElementaryOfCoefficient, Option.map_eq_some_iff] at hrun
    obtain ⟨b, hb, rfl⟩ := hrun
    exact ⟨by simpa [coefficientLogSum] using LawfulCRecursiveCoefficientIntegrator.sound c b hb,
      by simp, by simp⟩

/-- Domain where a log-free recursive integrator supplies the required elementary result. -/
def recursiveElementaryOfCoefficientDomain (domain : RecursiveCoefficientDomain (α := α)) :
    RecursiveElementaryDomain (α := α) := fun c =>
  domain c ∧ ∃ b : α, CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c

/-- Relative completeness of a log-free integrator lifts to its explicit rational elementary domain. -/
instance instCompleteCRecursiveElementaryIntegratorOfCoefficient
    (C : CRecursiveCoefficientIntegrator α) [LawfulCRecursiveCoefficientIntegrator C]
    (domain : RecursiveCoefficientDomain (α := α))
    [CompleteCRecursiveCoefficientIntegrator C domain] :
    CompleteCRecursiveElementaryIntegrator (recursiveElementaryOfCoefficient C)
      (recursiveElementaryOfCoefficientDomain domain) where
  complete c hdomain _ := by
    obtain ⟨b, hrun⟩ := CompleteCRecursiveCoefficientIntegrator.complete
      (C := C) (domain := domain) c hdomain.1 hdomain.2
    exact ⟨{ rational := b, logs := [] }, by simp [recursiveElementaryOfCoefficient, hrun]⟩

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

/-- Domain-relative completeness contract for recursive limited integration. -/
class CompleteCLimitedCoefficientIntegrator (C : CRecursiveCoefficientIntegrator α)
    (domain : LimitedCoefficientDomain (α := α))
    [LawfulCLimitedCoefficientIntegrator C] : Prop where
  /-- Every domain pair admitting a limited decomposition is accepted. -/
  limited_complete : ∀ (η c : α), domain η c → IsLimitedCoefficientIntegrable η c →
    ∃ b r, C.limitedIntegrate η c = some (b, r) ∧ IsLimitedCoefficientResult η c b r

end DeepWiki.SymbolicIntegration
