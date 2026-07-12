import DeepWiki.SymbolicIntegration.Engine.RecursiveCoefficient
import DeepWiki.SymbolicIntegration.Engine.Tower.Stage

/-! # Explicit-derivation recursive elementary coefficient stages

Recursive coefficient integration is a stage in its own right. This interface avoids the implicit
`CDiffField` instance by carrying the selected computable and semantic derivatives explicitly, then
exports accepted results through the common output-remainder contract.
-/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- A recursive elementary coefficient integrator selected for one explicit computable derivation. -/
structure CRecursiveElementaryIntegratorWith (α : Type u) [CField α]
    (derivation : CFieldDerivation α) where
  /-- Integrate a coefficient to a rational part plus lower-field logarithms, if possible. -/
  integrate : ℕ → α → Option (CoefficientIntegralResult α)

/-- The logarithmic derivative sum selected by an explicit coefficient derivation. -/
def coefficientLogSumWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (logs : List (α × α)) : CFieldSpec.K α :=
  (logs.map fun cv => CFieldSpec.toK cv.1 *
    (CFieldSpec.toK (derivation.cderiv cv.2) / CFieldSpec.toK cv.2)).sum

/-- A recursive elementary result is sound for the selected explicit coefficient differential. -/
def IsCoefficientIntegralResultWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (c : α) (res : CoefficientIntegralResult α) : Prop :=
  @Differential.deriv _ _ diffK (CFieldSpec.toK res.rational) +
      coefficientLogSumWith derivation res.logs = CFieldSpec.toK c ∧
    (∀ cv ∈ res.logs, @Differential.deriv _ _ diffK (CFieldSpec.toK cv.1) = 0) ∧
    (∀ cv ∈ res.logs, CFieldSpec.toK cv.2 ≠ 0)

/-- A coefficient admits an elementary antiderivative for an explicit derivative when it has a witness. -/
def IsCoefficientElementarilyIntegrableWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α)) (c : α) : Prop :=
  ∃ res : CoefficientIntegralResult α, IsCoefficientIntegralResultWith derivation diffK c res

/-- The computable logarithmic derivative sum selected by an explicit coefficient derivation. -/
def coefficientLogDerivativeWith {α : Type u} [CField α]
    (derivation : CFieldDerivation α) : List (α × α) → α
  | [] => CCommRing.zero
  | cv :: rest => CCommRing.add
      (CCommRing.mul cv.1 (CField.div (derivation.cderiv cv.2) cv.2))
      (coefficientLogDerivativeWith derivation rest)

/-- Check an explicit coefficient result using only computable field operations and the selected derivative. -/
def coefficientIntegralResultCheckWith {α : Type u} [CField α]
    (derivation : CFieldDerivation α) (c : α) (res : CoefficientIntegralResult α) : Bool :=
  CCommRing.isZero (CField.sub
      (CCommRing.add (derivation.cderiv res.rational)
        (coefficientLogDerivativeWith derivation res.logs)) c) &&
    res.logs.all (fun cv => CCommRing.isZero (derivation.cderiv cv.1)) &&
    res.logs.all (fun cv => !CCommRing.isZero cv.2)

/-- A certificate-checked explicit coefficient candidate. -/
def checkedRecursiveElementaryIntegratorWith {α : Type u} [CField α]
    (derivation : CFieldDerivation α)
    (raw : CRecursiveElementaryIntegratorWith α derivation) :
    CRecursiveElementaryIntegratorWith α derivation where
  integrate fuel c := raw.integrate fuel c |>.bind fun res =>
    if coefficientIntegralResultCheckWith derivation c res then some res else none

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]

/-- The selected computable logarithmic sum denotes its explicit semantic counterpart. -/
theorem toK_coefficientLogDerivativeWith
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK] (logs : List (α × α)) :
    CFieldSpec.toK (coefficientLogDerivativeWith derivation logs) =
      coefficientLogSumWith derivation logs := by
  induction logs with
  | nil => simp [coefficientLogDerivativeWith, coefficientLogSumWith, CFieldSpec.toK_zero]
  | cons cv rest ih =>
      simp [coefficientLogDerivativeWith, coefficientLogSumWith, CFieldSpec.toK_add,
        CFieldSpec.toK_mul, CFieldSpec.toK_div, ih, (LawfulCFieldDerivation.toK_cderiv cv.2)]

/-- A passed explicit coefficient-result check has its selected semantic meaning. -/
theorem isCoefficientIntegralResultWith_of_check
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK]
    (c : α) (res : CoefficientIntegralResult α)
    (hcheck : coefficientIntegralResultCheckWith derivation c res = true) :
    IsCoefficientIntegralResultWith derivation diffK c res := by
  simp only [coefficientIntegralResultCheckWith, Bool.and_eq_true] at hcheck
  obtain ⟨⟨hid, hconstants⟩, hargs⟩ := hcheck
  refine ⟨?_, ?_, ?_⟩
  · rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero,
      CFieldSpec.toK_add, toK_coefficientLogDerivativeWith derivation diffK] at hid
    simpa only [LawfulCFieldDerivation.toK_cderiv] using hid
  · intro cv hcv
    have hz := (List.all_eq_true.mp hconstants) cv hcv
    rw [CFieldSpec.isZero_iff] at hz
    simpa only [LawfulCFieldDerivation.toK_cderiv] using hz
  · intro cv hcv hzero
    have hfalse := (List.all_eq_true.mp hargs) cv hcv
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff] at hfalse
    exact hfalse hzero

/-- The explicit coefficient-result check accepts every selected semantic certificate. -/
theorem coefficientIntegralResultCheckWith_of_isCoefficientIntegralResultWith
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK]
    (c : α) (res : CoefficientIntegralResult α)
    (h : IsCoefficientIntegralResultWith derivation diffK c res) :
    coefficientIntegralResultCheckWith derivation c res = true := by
  obtain ⟨hid, hconstants, hargs⟩ := h
  simp only [coefficientIntegralResultCheckWith, Bool.and_eq_true]
  constructor
  · constructor
    · rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero,
        CFieldSpec.toK_add, toK_coefficientLogDerivativeWith derivation diffK]
      simpa only [LawfulCFieldDerivation.toK_cderiv] using hid
    · apply List.all_eq_true.mpr
      intro cv hcv
      rw [CFieldSpec.isZero_iff]
      simpa only [LawfulCFieldDerivation.toK_cderiv] using hconstants cv hcv
  · apply List.all_eq_true.mpr
    intro cv hcv
    cases hz : CCommRing.isZero cv.2 with
    | false => rfl
    | true =>
      have hzero : CFieldSpec.toK cv.2 = 0 := by
        rw [← CFieldSpec.isZero_iff]
        exact hz
      exact (hargs cv hcv hzero).elim

/-- The explicit coefficient-result check exactly reflects its selected semantic certificate. -/
theorem coefficientIntegralResultCheckWith_iff
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK]
    (c : α) (res : CoefficientIntegralResult α) :
    coefficientIntegralResultCheckWith derivation c res = true ↔
      IsCoefficientIntegralResultWith derivation diffK c res :=
  ⟨isCoefficientIntegralResultWith_of_check derivation diffK c res,
    coefficientIntegralResultCheckWith_of_isCoefficientIntegralResultWith derivation diffK c res⟩

/-- Soundness law for an explicit recursive elementary coefficient integrator. -/
class LawfulCRecursiveElementaryIntegratorWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (C : CRecursiveElementaryIntegratorWith α derivation) : Prop where
  /-- Every accepted result is an elementary antiderivative under the selected differential. -/
  sound : ∀ fuel c res, C.integrate fuel c = some res →
    IsCoefficientIntegralResultWith derivation diffK c res

/-- Certificate checking makes any explicit recursive coefficient candidate lawful. -/
instance instLawfulCRecursiveElementaryIntegratorWithChecked
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK]
    (raw : CRecursiveElementaryIntegratorWith α derivation) :
    LawfulCRecursiveElementaryIntegratorWith derivation diffK
      (checkedRecursiveElementaryIntegratorWith derivation raw) where
  sound fuel c res hrun := by
    simp only [checkedRecursiveElementaryIntegratorWith] at hrun
    cases hraw : raw.integrate fuel c with
    | none => simp [hraw] at hrun
    | some candidate =>
      rw [hraw] at hrun
      simp only [Option.bind_some] at hrun
      split at hrun
      · rename_i hcheck
        simp only [Option.some.injEq] at hrun
        subst candidate
        exact isCoefficientIntegralResultWith_of_check derivation diffK c res hcheck
      · simp at hrun

/-- Semantic input domain for explicit recursive elementary coefficient integration. -/
abbrev RecursiveElementaryDomainWith (α : Type u) := α → Prop

/-- Relative completeness law for an explicit recursive elementary coefficient integrator. -/
class CompleteCRecursiveElementaryIntegratorWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (C : CRecursiveElementaryIntegratorWith α derivation)
    (domain : RecursiveElementaryDomainWith α)
    [LawfulCRecursiveElementaryIntegratorWith derivation diffK C] : Prop where
  /-- Every in-domain coefficient with an elementary witness is eventually accepted. -/
  complete : ∀ c, domain c → IsCoefficientElementarilyIntegrableWith derivation diffK c →
    ∃ fuel res, C.integrate fuel c = some res

/-- The exact semantic acceptance domain of a checked explicit coefficient candidate. -/
def checkedRecursiveElementaryIntegratorWithDomain
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (raw : CRecursiveElementaryIntegratorWith α derivation) :
    RecursiveElementaryDomainWith α := fun c =>
  ∃ fuel res, raw.integrate fuel c = some res ∧
    IsCoefficientIntegralResultWith derivation diffK c res

/-- A checked explicit coefficient candidate is relatively complete on its exact certified domain. -/
instance instCompleteCRecursiveElementaryIntegratorWithChecked
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK]
    (raw : CRecursiveElementaryIntegratorWith α derivation) :
    @CompleteCRecursiveElementaryIntegratorWith α _ _ derivation diffK
      (checkedRecursiveElementaryIntegratorWith derivation raw)
      (checkedRecursiveElementaryIntegratorWithDomain derivation diffK raw)
      (instLawfulCRecursiveElementaryIntegratorWithChecked derivation diffK raw) where
  complete c hdomain _ := by
    obtain ⟨fuel, result, hrun, hresult⟩ := hdomain
    have hcheck := coefficientIntegralResultCheckWith_of_isCoefficientIntegralResultWith
      derivation diffK c result hresult
    refine ⟨fuel, result, ?_⟩
    simp [checkedRecursiveElementaryIntegratorWith, hrun, hcheck]

/-- Export an explicit recursive elementary coefficient solver as a common remainder stage. -/
noncomputable def CRecursiveElementaryIntegratorWith.asRemainderIntegrationStage
    {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (C : CRecursiveElementaryIntegratorWith α derivation)
    (domain : RecursiveElementaryDomainWith α)
    [LawfulCRecursiveElementaryIntegratorWith derivation diffK C]
    [CompleteCRecursiveElementaryIntegratorWith derivation diffK C domain] :
    RemainderIntegrationStage α (CoefficientIntegralResult α) Unit
      (IsCoefficientElementarilyIntegrableWith derivation diffK)
      (fun c result _ => IsCoefficientIntegralResultWith derivation diffK c result) :=
  { stage :=
      { run := fun fuel c => (C.integrate fuel c).map fun result => ⟨result, ()⟩
        domain := domain
        sound := by
          intro fuel c result _ hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact LawfulCRecursiveElementaryIntegratorWith.sound fuel c out hout
        complete := by
          intro c hdomain hintegrable
          obtain ⟨fuel, result, hrun⟩ :=
            CompleteCRecursiveElementaryIntegratorWith.complete
              (C := C) (domain := domain) c hdomain hintegrable
          exact ⟨fuel, ⟨result, ()⟩, by simp [hrun]⟩ } }

/-! ### Compatibility adapter for legacy coefficient recursion -/

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]
  [CDiffField α] [CDiffFieldSpec.{u,v} α]

/-- The legacy recursive elementary solver viewed through its explicit coefficient derivation. -/
@[reducible] noncomputable def CRecursiveElementaryIntegrator.asWith
    (C : CRecursiveElementaryIntegrator α) :
    CRecursiveElementaryIntegratorWith α (CFieldDerivation.ofCDiffField α) where
  integrate := C.integrate

omit [CDiffFieldSpec α] in
/-- The explicit and legacy coefficient logarithmic sums agree in the compatibility context. -/
theorem coefficientLogSumWith_ofCDiffField (logs : List (α × α)) :
    coefficientLogSumWith (CFieldDerivation.ofCDiffField α) logs = coefficientLogSum logs := by
  simp only [coefficientLogSumWith, CFieldDerivation.ofCDiffField, coefficientLogSum]

/-- The legacy elementary coefficient certificate is the explicit certificate in the compatibility context. -/
theorem isCoefficientIntegralResultWith_ofCDiffField_iff (c : α) (res : CoefficientIntegralResult α) :
    IsCoefficientIntegralResultWith (CFieldDerivation.ofCDiffField α) CDiffFieldSpec.diffK c res ↔
      IsCoefficientIntegralResult c res := by
  unfold IsCoefficientIntegralResultWith IsCoefficientIntegralResult
  rw [coefficientLogSumWith_ofCDiffField]
  simp only [CDiffFieldSpec.toK_cderiv]

/-- Promote a lawful legacy coefficient solver to the explicit-differential contract. -/
@[reducible] noncomputable def LawfulCRecursiveElementaryIntegratorWith.ofLegacy
    (C : CRecursiveElementaryIntegrator α) [LawfulCRecursiveElementaryIntegrator C] :
    LawfulCRecursiveElementaryIntegratorWith (CFieldDerivation.ofCDiffField α)
      CDiffFieldSpec.diffK C.asWith where
  sound fuel c res hrun :=
    (isCoefficientIntegralResultWith_ofCDiffField_iff c res).mpr
      (LawfulCRecursiveElementaryIntegrator.sound fuel c res hrun)

/-- Promote a complete legacy coefficient solver to the explicit-differential contract. -/
@[reducible] noncomputable def CompleteCRecursiveElementaryIntegratorWith.ofLegacy
    (C : CRecursiveElementaryIntegrator α) (domain : RecursiveElementaryDomain (α := α))
    [LawfulCRecursiveElementaryIntegrator C] [CompleteCRecursiveElementaryIntegrator C domain] :
    @CompleteCRecursiveElementaryIntegratorWith α _ _
      (CFieldDerivation.ofCDiffField α) CDiffFieldSpec.diffK C.asWith domain
      (@LawfulCRecursiveElementaryIntegratorWith.ofLegacy α _ _ _ _ C _) := by
  letI : LawfulCRecursiveElementaryIntegratorWith (CFieldDerivation.ofCDiffField α)
      CDiffFieldSpec.diffK C.asWith := LawfulCRecursiveElementaryIntegratorWith.ofLegacy C
  refine ⟨?_⟩
  intro c hdomain hintegrable
  obtain ⟨witness, hwitness⟩ := hintegrable
  obtain ⟨fuel, result, hrun⟩ := CompleteCRecursiveElementaryIntegrator.complete
    (C := C) (domain := domain) c hdomain
      ⟨witness, (isCoefficientIntegralResultWith_ofCDiffField_iff c witness).mp hwitness⟩
  exact ⟨fuel, result, hrun⟩

end DeepWiki.SymbolicIntegration
