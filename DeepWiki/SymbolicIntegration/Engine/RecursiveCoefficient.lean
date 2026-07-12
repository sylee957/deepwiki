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

/-- Executable value of the logarithmic derivative sum stored in a coefficient result. -/
def coefficientLogDerivative {α : Type u} [CField α] [CDiffField α] :
    List (α × α) → α
  | [] => CCommRing.zero
  | cv :: rest => CCommRing.add
      (CCommRing.mul cv.1 (CField.div (CDiffField.cderiv cv.2) cv.2))
      (coefficientLogDerivative rest)

/-- Check the derivative identity, constant coefficients, and nonzero arguments of a coefficient result. -/
def coefficientIntegralResultCheck {α : Type u} [CField α] [CDiffField α]
    (c : α) (res : CoefficientIntegralResult α) : Bool :=
  CCommRing.isZero (CField.sub
      (CCommRing.add (CDiffField.cderiv res.rational) (coefficientLogDerivative res.logs)) c) &&
    res.logs.all (fun cv => CCommRing.isZero (CDiffField.cderiv cv.1)) &&
    res.logs.all (fun cv => !CCommRing.isZero cv.2)

/-- Certificate-check an arbitrary recursive elementary coefficient candidate. -/
def checkedRecursiveElementaryIntegrator {α : Type u} [CField α] [CDiffField α]
    (raw : CRecursiveElementaryIntegrator α) : CRecursiveElementaryIntegrator α where
  integrate c := raw.integrate c |>.bind fun res =>
    if coefficientIntegralResultCheck c res then some res else none

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]

/-- Denotation of the logarithmic terms in a recursive coefficient result. -/
def coefficientLogSum (logs : List (α × α)) : CFieldSpec.K α :=
    (logs.map fun cv => CFieldSpec.toK cv.1 *
    (CFieldSpec.toK (CDiffField.cderiv cv.2) / CFieldSpec.toK cv.2)).sum

omit [CDiffFieldSpec α] in
/-- The executable logarithmic derivative sum denotes the semantic coefficient log sum. -/
theorem toK_coefficientLogDerivative (logs : List (α × α)) :
    CFieldSpec.toK (coefficientLogDerivative logs) = coefficientLogSum logs := by
  induction logs with
  | nil => simp [coefficientLogDerivative, coefficientLogSum, CFieldSpec.toK_zero]
  | cons cv rest ih =>
      simp [coefficientLogDerivative, coefficientLogSum, CFieldSpec.toK_add,
        CFieldSpec.toK_mul, CFieldSpec.toK_div, ih]

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

omit [CDiffFieldSpec α] in
/-- A passed coefficient-result certificate proves the denotational elementary antiderivative contract. -/
theorem isCoefficientIntegralResult_of_check (c : α) (res : CoefficientIntegralResult α)
    (hcheck : coefficientIntegralResultCheck c res = true) :
    IsCoefficientIntegralResult c res := by
  simp only [coefficientIntegralResultCheck, Bool.and_eq_true] at hcheck
  obtain ⟨⟨hid, hconstants⟩, hargs⟩ := hcheck
  rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero,
    CFieldSpec.toK_add, toK_coefficientLogDerivative] at hid
  refine ⟨hid, ?_, ?_⟩
  · intro cv hcv
    have hz := (List.all_eq_true.mp hconstants) cv hcv
    rw [CFieldSpec.isZero_iff] at hz
    exact hz
  · intro cv hcv hzero
    have hfalse := (List.all_eq_true.mp hargs) cv hcv
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff] at hfalse
    exact hfalse hzero

omit [CDiffFieldSpec α] in
/-- The coefficient-result checker accepts every denotational elementary antiderivative certificate. -/
theorem coefficientIntegralResultCheck_of_isCoefficientIntegralResult
    (c : α) (res : CoefficientIntegralResult α) (h : IsCoefficientIntegralResult c res) :
    coefficientIntegralResultCheck c res = true := by
  obtain ⟨hid, hconstants, hargs⟩ := h
  simp only [coefficientIntegralResultCheck, Bool.and_eq_true]
  constructor
  · constructor
    · rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero,
        CFieldSpec.toK_add, toK_coefficientLogDerivative]
      exact hid
    · apply List.all_eq_true.mpr
      intro cv hcv
      rw [CFieldSpec.isZero_iff]
      exact hconstants cv hcv
  · apply List.all_eq_true.mpr
    intro cv hcv
    cases hz : CCommRing.isZero cv.2 with
    | false => rfl
    | true =>
        have hzero : CFieldSpec.toK cv.2 = 0 := by
          rw [← CFieldSpec.isZero_iff]
          exact hz
        exact (hargs cv hcv hzero).elim

omit [CDiffFieldSpec α] in
/-- The executable coefficient-result checker exactly reflects its denotational contract. -/
theorem coefficientIntegralResultCheck_iff (c : α) (res : CoefficientIntegralResult α) :
    coefficientIntegralResultCheck c res = true ↔ IsCoefficientIntegralResult c res :=
  ⟨isCoefficientIntegralResult_of_check c res,
    coefficientIntegralResultCheck_of_isCoefficientIntegralResult c res⟩

/-- Certificate checking makes any recursive elementary candidate unconditionally lawful. -/
instance instLawfulCRecursiveElementaryIntegratorChecked
    (raw : CRecursiveElementaryIntegrator α) :
    LawfulCRecursiveElementaryIntegrator (checkedRecursiveElementaryIntegrator raw) where
  sound c res hrun := by
    simp only [checkedRecursiveElementaryIntegrator] at hrun
    cases hraw : raw.integrate c with
    | none => simp [hraw] at hrun
    | some candidate =>
        rw [hraw] at hrun
        simp only [Option.bind_some] at hrun
        split at hrun
        · rename_i hcheck
          simp only [Option.some.injEq] at hrun
          subst candidate
          exact isCoefficientIntegralResult_of_check c res hcheck
        · simp at hrun

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
