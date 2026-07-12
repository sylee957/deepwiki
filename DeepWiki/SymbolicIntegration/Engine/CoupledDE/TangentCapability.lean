import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentReconstruct
import DeepWiki.SymbolicIntegration.Engine.MonomialCaseSparse
import DeepWiki.SymbolicIntegration.Engine.RischLevel
import DeepWiki.SymbolicIntegration.Engine.CheckIdentityCorrect

/-! # Tangent coupled-solver capability

The hypertangent monomial case reduces special integration to a coupled differential system. This module
isolates preparation and reconstruction behind explicit soundness and relative-completeness contracts. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

universe u

/-- Prop-free executable capability for the tangent coupled differential system over `ℚ(x)[t]`. -/
structure CTangentPolynomialCoupledSolver where
  /-- Solve the level-`n` tangent system with the supplied coefficient-degree bound. -/
  solve : ℕ → DensePoly ℚ → DensePoly ℚ → List (DensePoly ℚ) → List (DensePoly ℚ) → ℕ →
    Option (List (DensePoly ℚ) × List (DensePoly ℚ))

/-- Denotation-level soundness contract for a tangent coupled solver. -/
class LawfulCTangentPolynomialCoupledSolver (C : CTangentPolynomialCoupledSolver) : Prop where
  /-- Every returned pair solves the requested tangent system. -/
  sound : ∀ (dbound : ℕ) (b0 b2 : DensePoly ℚ) (c1 c2 q1 q2 : List (DensePoly ℚ)) (n : ℕ),
    C.solve dbound b0 b2 c1 c2 n = some (q1, q2) → TanSolves b0 b2 n c1 c2 q1 q2

/-- Semantic domain for relative completeness of a polynomial tangent coupled solver. -/
abbrev TangentPolynomialCoupledDomain := DensePoly ℚ → DensePoly ℚ →
  List (DensePoly ℚ) → List (DensePoly ℚ) → ℕ → Prop

/-- Relative-completeness contract for a polynomial tangent coupled solver on a selected domain. -/
class CompleteCTangentPolynomialCoupledSolver (C : CTangentPolynomialCoupledSolver)
    (domain : TangentPolynomialCoupledDomain)
    [LawfulCTangentPolynomialCoupledSolver C] : Prop where
  /-- Every solvable in-domain system is found at some finite coefficient-degree bound. -/
  complete : ∀ (b0 b2 : DensePoly ℚ) (c1 c2 : List (DensePoly ℚ)) (n : ℕ),
    domain b0 b2 c1 c2 n →
      (∃ q1 q2, TanSolves b0 b2 n c1 c2 q1 q2) →
        ∃ dbound q1 q2, C.solve dbound b0 b2 c1 c2 n = some (q1, q2)

/-- Exact executable-acceptance domain of a polynomial tangent coupled solver. -/
def tangentPolynomialCoupledAcceptanceDomain (C : CTangentPolynomialCoupledSolver) :
    TangentPolynomialCoupledDomain := fun b0 b2 c1 c2 n =>
  ∃ dbound q1 q2, C.solve dbound b0 b2 c1 c2 n = some (q1, q2)

/-- The existing degree-bounded tangent cancellation algorithm as a coupled-solver capability. -/
def tangentPolynomialCoupledSolver [CLinearSolve ℚ] : CTangentPolynomialCoupledSolver where
  solve := cCoupledDECancelTan

/-- The tangent cancellation algorithm realizes the coupled-solver soundness contract. -/
instance instLawfulCTangentPolynomialCoupledSolver [CLinearSolve ℚ] [LawfulCLinearSolve ℚ] :
    LawfulCTangentPolynomialCoupledSolver tangentPolynomialCoupledSolver where
  sound dbound b0 b2 c1 c2 q1 q2 n hrun :=
    DensePoly.reconstruct dbound b0 n b2 c1 c2 q1 q2 hrun

/-- The degree-bounded polynomial tangent solver is complete on its exact acceptance domain. -/
instance instCompleteCTangentPolynomialCoupledSolver [CLinearSolve ℚ] [LawfulCLinearSolve ℚ] :
    CompleteCTangentPolynomialCoupledSolver tangentPolynomialCoupledSolver
      (tangentPolynomialCoupledAcceptanceDomain tangentPolynomialCoupledSolver) where
  complete _ _ _ _ _ hdomain _ := hdomain

/-! ## Coefficient-field coupled-system boundary -/

/-- Prop-free coupled-system operation over the actual hypertangent coefficient field. -/
structure CTangentCoefficientSolver (α : Type u) [CField α] [CDiffField α] where
  /-- Attempt `Dc - coupling*d = a` and `Dd + coupling*c = b` at a finite search bound. -/
  solve : ℕ → α → α → α → Option (α × α)

variable {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec.{u,u} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Denotational soundness contract for a coefficient-field tangent coupled solver. -/
class LawfulCTangentCoefficientSolver (C : CTangentCoefficientSolver α) : Prop where
  /-- Every returned pair solves both coefficient-field differential equations. -/
  sound : ∀ (fuel : ℕ) (coupling a b c d : α), C.solve fuel coupling a b = some (c, d) →
    CFieldSpec.toK (CDiffField.cderiv c) - CFieldSpec.toK coupling * CFieldSpec.toK d =
        CFieldSpec.toK a ∧
      CFieldSpec.toK (CDiffField.cderiv d) + CFieldSpec.toK coupling * CFieldSpec.toK c =
        CFieldSpec.toK b

/-- Semantic domain for relative completeness of coefficient-field tangent coupled solving. -/
abbrev TangentCoefficientDomain := α → α → α → Prop

/-- A coefficient-field tangent coupled system has a denotational solution. -/
def IsTangentCoefficientSolvable (coupling a b : α) : Prop :=
  ∃ c d,
    CFieldSpec.toK (CDiffField.cderiv c) - CFieldSpec.toK coupling * CFieldSpec.toK d =
        CFieldSpec.toK a ∧
      CFieldSpec.toK (CDiffField.cderiv d) + CFieldSpec.toK coupling * CFieldSpec.toK c =
        CFieldSpec.toK b

/-- Domain-relative completeness for coefficient-field tangent coupled solving. -/
class CompleteCTangentCoefficientSolver (C : CTangentCoefficientSolver α)
    (domain : TangentCoefficientDomain (α := α)) [LawfulCTangentCoefficientSolver C] : Prop where
  /-- Every solvable in-domain system succeeds at some finite search bound. -/
  complete : ∀ (coupling a b : α), domain coupling a b →
    IsTangentCoefficientSolvable coupling a b →
      ∃ fuel c d, C.solve fuel coupling a b = some (c, d)

/-- Check both coefficient-field coupled equations before releasing a candidate. -/
def checkedTangentCoefficientSolver (raw : CTangentCoefficientSolver α) :
    CTangentCoefficientSolver α where
  solve fuel coupling a b := do
    let out ← raw.solve fuel coupling a b
    let row₁ := CField.sub
      (CField.sub (CDiffField.cderiv out.1) (CCommRing.mul coupling out.2)) a
    let row₂ := CField.sub
      (CCommRing.add (CDiffField.cderiv out.2) (CCommRing.mul coupling out.1)) b
    if CCommRing.isZero row₁ && CCommRing.isZero row₂ then some out else none

/-- The checked coefficient-field coupled operation is lawful without assumptions on its candidate generator. -/
instance instLawfulCTangentCoefficientSolverChecked (raw : CTangentCoefficientSolver α) :
    LawfulCTangentCoefficientSolver (checkedTangentCoefficientSolver raw) where
  sound fuel coupling a b c d hrun := by
    simp only [checkedTangentCoefficientSolver] at hrun
    rcases hraw : raw.solve fuel coupling a b with _ | out
    · simp [hraw] at hrun
    rw [hraw] at hrun
    change (if CCommRing.isZero
          (CField.sub (CField.sub (CDiffField.cderiv out.1)
            (CCommRing.mul coupling out.2)) a) &&
        CCommRing.isZero
          (CField.sub (CCommRing.add (CDiffField.cderiv out.2)
            (CCommRing.mul coupling out.1)) b)
      then some out else none) = some (c, d) at hrun
    split at hrun
    · rename_i hcheck
      have hout : out = (c, d) := Option.some.inj hrun
      subst out
      rw [Bool.and_eq_true] at hcheck
      obtain ⟨hrow₁, hrow₂⟩ := hcheck
      rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, CFieldSpec.toK_sub,
        CFieldSpec.toK_mul] at hrow₁
      rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, CFieldSpec.toK_add,
        CFieldSpec.toK_mul] at hrow₂
      change CFieldSpec.toK (CDiffField.cderiv c) -
        CFieldSpec.toK coupling * CFieldSpec.toK d - CFieldSpec.toK a = 0 at hrow₁
      change CFieldSpec.toK (CDiffField.cderiv d) +
        CFieldSpec.toK coupling * CFieldSpec.toK c - CFieldSpec.toK b = 0 at hrow₂
      exact ⟨sub_eq_zero.mp hrow₁, sub_eq_zero.mp hrow₂⟩
    · contradiction

/-- Exact executable acceptance domain of a checked coefficient-field coupled solver. -/
def checkedTangentCoefficientDomain (raw : CTangentCoefficientSolver α) :
    TangentCoefficientDomain (α := α) := fun coupling a b =>
  ∃ fuel c d, (checkedTangentCoefficientSolver raw).solve fuel coupling a b = some (c, d)

/-- A checked coefficient-field coupled solver is complete on its exact acceptance domain. -/
instance instCompleteCTangentCoefficientSolverChecked (raw : CTangentCoefficientSolver α) :
    CompleteCTangentCoefficientSolver (checkedTangentCoefficientSolver raw)
      (checkedTangentCoefficientDomain raw) where
  complete _ _ _ hdomain _ := hdomain

/-- Semantic domain on which a tangent special integrator is required to be complete. -/
abbrev TangentSpecialDomain (α : Type u) := DensePoly α → DensePoly α →
  DensePoly α → DensePoly α → Prop

/-- Prop-free recursive hypertangent special integrator parameterized by a coupled-system solver. -/
structure CTangentSpecialIntegrator (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate the polynomial and special-denominator parts, making as many coupled calls as required. -/
  integrate : CTangentCoefficientSolver α → ℕ → DensePoly α → DensePoly α →
    DensePoly α → DensePoly α →
      Option (IntegralResult α)

/-- Denotational soundness contract for a selected tangent special integrator and coupled solver. -/
class LawfulCTangentSpecialIntegrator (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) : Prop where
  /-- Every returned fraction differentiates to the requested polynomial and special parts. -/
  sound : ∀ (fuel : ℕ) (Dt fp b ds : DensePoly α) (res : IntegralResult α),
    T.integrate S fuel Dt fp b ds = some res →
      CPoly.toPoly res.rational.2 ≠ 0 ∧
        towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2) +
            logResidueSumP Dt res.logs =
          fieldFracP fp CPoly.one + fieldFracP b ds

/-- A lawful tangent special integrator whose successful logarithmic terms are genuine. -/
class LawfulGenuineCTangentSpecialIntegrator (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) [LawfulCTangentSpecialIntegrator S T] : Prop where
  /-- Every successful result has constant logarithmic coefficients. -/
  coefficients_constant : ∀ (fuel : ℕ) (Dt fp b ds : DensePoly α)
      (res : IntegralResult α),
    T.integrate S fuel Dt fp b ds = some res →
      ∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0
  /-- Every successful result has nonzero represented logarithm arguments. -/
  arguments_nonzero : ∀ (fuel : ℕ) (Dt fp b ds : DensePoly α)
      (res : IntegralResult α),
    T.integrate S fuel Dt fp b ds = some res →
      ∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0

/-- Relative-completeness contract for recursive tangent special integration. -/
class CompleteCTangentSpecialIntegrator (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) (domain : TangentSpecialDomain α)
    [LawfulCTangentSpecialIntegrator S T] : Prop where
  /-- Every domain input possessing a represented special antiderivative is accepted. -/
  complete : ∀ (Dt fp b ds : DensePoly α) (res : IntegralResult α),
    domain Dt fp b ds → CPoly.toPoly res.rational.2 ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2) +
        logResidueSumP Dt res.logs =
      fieldFracP fp CPoly.one + fieldFracP b ds →
    ∃ fuel out, T.integrate S fuel Dt fp b ds = some out

/-- Compose a tangent coupled solver and recursive special integrator into a monomial case. -/
def tangentMonomialCase (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α) :
    CMonomialCase DensePoly α where
  integrateSpecial fuel := T.integrate S fuel
  postprocessNormal _ before := some before

/-- A lawful recursive tangent special integrator makes the composed monomial case lawful. -/
instance instLawfulCMonomialCaseTangent (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [LawfulCTangentSpecialIntegrator S T] : LawfulCMonomialCase (tangentMonomialCase S T) where
  special_sound fuel Dt fp b ds res hrun :=
    LawfulCTangentSpecialIntegrator.sound fuel Dt fp b ds res hrun
  postprocessNormal_sound _ _ _ before after hbefore hrun := by
    change some before = some after at hrun
    have heq : before = after := Option.some.inj hrun
    subst after
    exact hbefore
  postprocessNormal_den_nonzero _ before after hden hrun := by
    change some before = some after at hrun
    have heq : before = after := Option.some.inj hrun
    subst after
    exact hden

/-- Genuine tangent-special results make the composed monomial stage genuinely lawful. -/
instance instLawfulGenuineCMonomialCaseTangent (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) [LawfulCTangentSpecialIntegrator S T]
    [LawfulGenuineCTangentSpecialIntegrator S T] :
    LawfulGenuineCMonomialCase (tangentMonomialCase S T) where
  special_coefficients_constant fuel Dt fp b ds res hrun :=
    LawfulGenuineCTangentSpecialIntegrator.coefficients_constant fuel Dt fp b ds res hrun
  special_arguments_nonzero fuel Dt fp b ds res hrun :=
    LawfulGenuineCTangentSpecialIntegrator.arguments_nonzero fuel Dt fp b ds res hrun
  postprocessNormal_coefficients_constant _ before after hconstants hrun := by
    change some before = some after at hrun
    have heq : before = after := Option.some.inj hrun
    subst after
    exact hconstants
  postprocessNormal_arguments_nonzero _ before after hargs hrun := by
    change some before = some after at hrun
    have heq : before = after := Option.some.inj hrun
    subst after
    exact hargs

/-- Complete recursive tangent integration makes the composed monomial case relatively complete. -/
instance instCompleteCMonomialCaseTangent (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    (domain : TangentSpecialDomain α) [LawfulCTangentSpecialIntegrator S T]
    [CompleteCTangentSpecialIntegrator S T domain] :
    CompleteCMonomialCase (tangentMonomialCase S T) domain where
  special_complete Dt fp b ds res hdomain hsden hderiv := by
    obtain ⟨fuel, out, hrun⟩ := CompleteCTangentSpecialIntegrator.complete
      (S := S) (T := T) (domain := domain) Dt fp b ds res hdomain hsden hderiv
    exact ⟨fuel, out, hrun⟩
  postprocess_complete _ _ _ before _ := ⟨before, rfl⟩

/-- Certificate-check every result returned by a tangent special integrator. -/
def checkedTangentSpecialIntegrator (T : CTangentSpecialIntegrator α) : CTangentSpecialIntegrator α where
  integrate S fuel Dt fp b ds := do
    let out ← T.integrate S fuel Dt fp b ds
    if CPolyEngine.cisZero ds then none
    else if CPolyEngine.cisZero out.rational.2 then none
    else if !out.logs.all (fun cv => !CPolyEngine.cisZero cv.2) then none
    else if !out.logs.all (fun cv => CCommRing.isZero (CDiffField.cderiv cv.1)) then none
    else
      if CPoly.checkIdentity Dt out (polynomialSpecialNumerator fp b ds) ds then some out else none

/-- The certificate-checked tangent special operation is lawful without assumptions on the raw integrator. -/
instance instLawfulCTangentSpecialIntegratorChecked (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) :
    LawfulCTangentSpecialIntegrator S (checkedTangentSpecialIntegrator T) where
  sound fuel Dt fp b ds res hrun := by
    simp only [checkedTangentSpecialIntegrator] at hrun
    change (T.integrate S fuel Dt fp b ds).bind
      (fun out =>
        if CPolyEngine.cisZero ds then none
        else if CPolyEngine.cisZero out.rational.2 then none
        else if !out.logs.all (fun cv => !CPolyEngine.cisZero cv.2) then none
        else if !out.logs.all (fun cv => CCommRing.isZero (CDiffField.cderiv cv.1)) then none
        else
          if CPoly.checkIdentity Dt out (polynomialSpecialNumerator fp b ds) ds then
            some out
          else none) = some res at hrun
    rcases hraw : T.integrate S fuel Dt fp b ds with _ | out
    · simp [hraw] at hrun
    rw [hraw] at hrun
    simp only [Option.bind_some] at hrun
    let hif := hrun
    split at hif
    · simp at hif
    rename_i hds
    simp at hif
    obtain ⟨hsden, hlogs, _hconstants, hcheck, hout⟩ := hif
    have hds' : CPoly.toPoly ds ≠ 0 :=
      CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (Bool.eq_false_iff.mpr hds)
    have houtRaw : CPoly.toPoly out.rational.2 ≠ 0 :=
      CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false hsden
    have hout' : CPoly.toPoly res.rational.2 ≠ 0 := by
      simpa [hout] using houtRaw
    have hargs : ∀ cv ∈ out.logs, CPoly.toPoly cv.2 ≠ 0 := by
      intro cv hcv
      apply CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false
      exact hlogs cv.1 cv.2 hcv
    have hid := field_identity_of_checkIdentityP Dt out (polynomialSpecialNumerator fp b ds) ds
      houtRaw hds' hargs hcheck
    refine ⟨hout', ?_⟩
    change (towerFractionFieldDerivP Dt)
      (fieldFracP out.rational.1 out.rational.2) + logResidueSumP Dt out.logs =
        fieldFracP (polynomialSpecialNumerator fp b ds) ds at hid
    rw [fieldFracP_polynomialSpecialNumerator fp b ds hds'] at hid
    simpa [hout] using hid

/-- The checked tangent special operation accepts only genuine logarithmic terms. -/
instance instLawfulGenuineCTangentSpecialIntegratorChecked (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) :
    LawfulGenuineCTangentSpecialIntegrator S (checkedTangentSpecialIntegrator T) where
  coefficients_constant fuel Dt fp b ds res hrun := by
    simp only [checkedTangentSpecialIntegrator] at hrun
    change (T.integrate S fuel Dt fp b ds).bind
      (fun out =>
        if CPolyEngine.cisZero ds then none
        else if CPolyEngine.cisZero out.rational.2 then none
        else if !out.logs.all (fun cv => !CPolyEngine.cisZero cv.2) then none
        else if !out.logs.all (fun cv => CCommRing.isZero (CDiffField.cderiv cv.1)) then none
        else if CPoly.checkIdentity Dt out (polynomialSpecialNumerator fp b ds) ds then some out
        else none) = some res at hrun
    rcases hraw : T.integrate S fuel Dt fp b ds with _ | out
    · simp [hraw] at hrun
    rw [hraw] at hrun
    split at hrun
    · contradiction
    rename_i hds
    simp at hrun
    obtain ⟨_hsden, _hargs, hconstants, _hcheck, hout⟩ := hrun
    subst res
    intro cv hcv
    exact (CFieldSpec.isZero_iff (CDiffField.cderiv cv.1)).mp (hconstants cv.1 cv.2 hcv)
  arguments_nonzero fuel Dt fp b ds res hrun := by
    simp only [checkedTangentSpecialIntegrator] at hrun
    change (T.integrate S fuel Dt fp b ds).bind
      (fun out =>
        if CPolyEngine.cisZero ds then none
        else if CPolyEngine.cisZero out.rational.2 then none
        else if !out.logs.all (fun cv => !CPolyEngine.cisZero cv.2) then none
        else if !out.logs.all (fun cv => CCommRing.isZero (CDiffField.cderiv cv.1)) then none
        else if CPoly.checkIdentity Dt out (polynomialSpecialNumerator fp b ds) ds then some out
        else none) = some res at hrun
    rcases hraw : T.integrate S fuel Dt fp b ds with _ | out
    · simp [hraw] at hrun
    rw [hraw] at hrun
    split at hrun
    · contradiction
    rename_i hds
    simp at hrun
    obtain ⟨_hsden, hargs, _hconstants, _hcheck, hout⟩ := hrun
    subst res
    intro cv hcv
    exact CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (hargs cv.1 cv.2 hcv)

/-- Install a certificate-checked tangent special operation as an ordinary monomial stage. -/
def checkedTangentMonomialCase (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α) :
    CMonomialCase DensePoly α :=
  tangentMonomialCase S (checkedTangentSpecialIntegrator T)

/-- The certificate-checked tangent monomial case is sound without a lawful raw-integrator assumption. -/
instance instLawfulCMonomialCaseCheckedTangent (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) : LawfulCMonomialCase (checkedTangentMonomialCase S T) := by
  unfold checkedTangentMonomialCase
  infer_instance

/-- The certificate-checked tangent monomial case emits only genuine logarithmic terms. -/
instance instLawfulGenuineCMonomialCaseCheckedTangent (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) :
    LawfulGenuineCMonomialCase (checkedTangentMonomialCase S T) := by
  unfold checkedTangentMonomialCase
  infer_instance

/-- The explicit certificate-acceptance domain for a checked tangent special stage. -/
def checkedTangentSpecialDomain (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α) :
    TangentSpecialDomain α := fun Dt fp b ds =>
  ∀ (res : IntegralResult α), CPoly.toPoly res.rational.2 ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2) +
        logResidueSumP Dt res.logs =
      fieldFracP fp CPoly.one + fieldFracP b ds →
    CPoly.toPoly ds ≠ 0 ∧
      ∃ fuel out, T.integrate S fuel Dt fp b ds = some out ∧ CPoly.toPoly out.rational.2 ≠ 0 ∧
        (∀ cv ∈ out.logs, CPoly.toPoly cv.2 ≠ 0) ∧
        (∀ cv ∈ out.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
        CPoly.checkIdentity Dt out (polynomialSpecialNumerator fp b ds) ds = true

/-- Certificate-checked tangent integration is complete on its explicit raw-acceptance domain. -/
instance instCompleteCTangentSpecialIntegratorChecked (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) :
    CompleteCTangentSpecialIntegrator S (checkedTangentSpecialIntegrator T)
      (checkedTangentSpecialDomain S T) where
  complete Dt fp b ds res hdomain hsden hderiv := by
    obtain ⟨hds, fuel, out, hraw, hout, hlogs, hconstants, hcheck⟩ :=
      hdomain res hsden hderiv
    have hdsBool : DensePoly.cisZero ds = false := by
      rw [Bool.eq_false_iff]
      intro hzero
      exact hds (by simpa only [toPoly_list_eq] using (cisZeroG_iff ds).mp hzero)
    have houtBool : DensePoly.cisZero out.rational.2 = false := by
      rw [Bool.eq_false_iff]
      intro hzero
      exact hout (by simpa only [toPoly_list_eq] using (cisZeroG_iff out.rational.2).mp hzero)
    have hlogsBool : out.logs.all (fun cv => !DensePoly.cisZero cv.2) = true :=
      List.all_eq_true.mpr fun cv hcv => by
        have hzfalse : DensePoly.cisZero cv.2 = false := by
          rw [Bool.eq_false_iff]
          intro hzero
          exact hlogs cv hcv (by
            simpa only [toPoly_list_eq] using (cisZeroG_iff cv.2).mp hzero)
        simpa using hzfalse
    have hconstantsBool :
        out.logs.all (fun cv => CCommRing.isZero (CDiffField.cderiv cv.1)) = true :=
      List.all_eq_true.mpr fun cv hcv =>
        (CFieldSpec.isZero_iff (CDiffField.cderiv cv.1)).mpr (hconstants cv hcv)
    refine ⟨fuel, out, ?_⟩
    simp [checkedTangentSpecialIntegrator, hraw, hdsBool, houtBool, hlogsBool,
      hconstantsBool, hcheck]

/-- Strengthen a raw tangent completeness domain with the required nonzero special denominator. -/
def checkedTangentSpecialCompleteDomain (domain : TangentSpecialDomain α) :
    TangentSpecialDomain α := fun Dt fp b ds => CPoly.toPoly ds ≠ 0 ∧ domain Dt fp b ds

/-- Lawful genuine raw completeness lifts through the final tangent certificate checker. -/
instance instCompleteCTangentSpecialIntegratorCheckedOfLawful
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    (domain : TangentSpecialDomain α) [LawfulCTangentSpecialIntegrator S T]
    [LawfulGenuineCTangentSpecialIntegrator S T]
    [CompleteCTangentSpecialIntegrator S T domain] :
    CompleteCTangentSpecialIntegrator S (checkedTangentSpecialIntegrator T)
      (checkedTangentSpecialCompleteDomain domain) where
  complete Dt fp b ds res hdomain hsden hderiv := by
    obtain ⟨hds, hrawDomain⟩ := hdomain
    obtain ⟨fuel, out, hraw⟩ := CompleteCTangentSpecialIntegrator.complete
      (S := S) (T := T) (domain := domain) Dt fp b ds res hrawDomain hsden hderiv
    obtain ⟨hout, houtIdentity⟩ := LawfulCTangentSpecialIntegrator.sound
      (S := S) (T := T) fuel Dt fp b ds out hraw
    have hargs : ∀ cv ∈ out.logs, CPoly.toPoly cv.2 ≠ 0 :=
      LawfulGenuineCTangentSpecialIntegrator.arguments_nonzero
        (S := S) (T := T) fuel Dt fp b ds out hraw
    have hconstants : ∀ cv ∈ out.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0 :=
      LawfulGenuineCTangentSpecialIntegrator.coefficients_constant
        (S := S) (T := T) fuel Dt fp b ds out hraw
    have hcheck : CPoly.checkIdentity Dt out (polynomialSpecialNumerator fp b ds) ds = true := by
      apply checkIdentityP_of_field_identity Dt out (polynomialSpecialNumerator fp b ds) ds
        hout hds hargs
      change towerFractionFieldDerivP Dt (fieldFracP out.rational.1 out.rational.2) +
          logResidueSumP Dt out.logs = fieldFracP (polynomialSpecialNumerator fp b ds) ds
      rw [fieldFracP_polynomialSpecialNumerator fp b ds hds]
      exact houtIdentity
    have hdsBool : DensePoly.cisZero ds = false := by
      rw [Bool.eq_false_iff]
      intro hzero
      exact hds (by simpa only [toPoly_list_eq] using (cisZeroG_iff ds).mp hzero)
    have houtBool : DensePoly.cisZero out.rational.2 = false := by
      rw [Bool.eq_false_iff]
      intro hzero
      exact hout (by
        simpa only [toPoly_list_eq] using (cisZeroG_iff out.rational.2).mp hzero)
    have hargsBool : out.logs.all (fun cv => !DensePoly.cisZero cv.2) = true :=
      List.all_eq_true.mpr fun cv hcv => by
        have hzfalse : DensePoly.cisZero cv.2 = false := by
          rw [Bool.eq_false_iff]
          intro hzero
          exact hargs cv hcv (by
            simpa only [toPoly_list_eq] using (cisZeroG_iff cv.2).mp hzero)
        simpa using hzfalse
    have hconstantsBool :
        out.logs.all (fun cv => CCommRing.isZero (CDiffField.cderiv cv.1)) = true :=
      List.all_eq_true.mpr fun cv hcv =>
        (CFieldSpec.isZero_iff (CDiffField.cderiv cv.1)).mpr (hconstants cv hcv)
    refine ⟨fuel, out, ?_⟩
    simp [checkedTangentSpecialIntegrator, hraw, hdsBool, houtBool, hargsBool,
      hconstantsBool, hcheck]

/-- The checked tangent monomial stage is complete on the raw-integrator acceptance domain. -/
instance instCompleteCMonomialCaseCheckedTangent (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) :
    CompleteCMonomialCase (checkedTangentMonomialCase S T)
      (checkedTangentSpecialDomain S T) := by
  unfold checkedTangentMonomialCase
  infer_instance

/-- Tangent normal reduction obtained by certificate-checking an arbitrary raw normal reducer. -/
def tangentNormalReduction (raw : CNormalReduction DensePoly α) :
    CNormalReduction DensePoly α :=
  checkedNormalReduction raw

/-- Universal soundness domain of certificate-checked tangent normal reduction. -/
def tangentNormalDomain : NormalReductionDomain DensePoly α :=
  checkedNormalReductionDomain

/-- The explicit certificate-acceptance domain of a checked tangent normal reduction. -/
def tangentNormalCompleteDomain (raw : CNormalReduction DensePoly α) :
    NormalReductionDomain DensePoly α :=
  checkedNormalReductionAcceptanceDomain raw

/-- Certificate-checked tangent normal reduction is lawful without a low-degree Hermite hypothesis. -/
instance instLawfulCNormalReductionTangent (raw : CNormalReduction DensePoly α) :
    LawfulCNormalReduction (tangentNormalReduction raw) tangentNormalDomain := by
  unfold tangentNormalReduction tangentNormalDomain
  infer_instance

/-- Certificate-checked tangent normal reduction emits only genuine logarithmic terms. -/
instance instLawfulGenuineCNormalReductionTangent (raw : CNormalReduction DensePoly α) :
    LawfulGenuineCNormalReduction (tangentNormalReduction raw) tangentNormalDomain := by
  unfold tangentNormalReduction tangentNormalDomain
  infer_instance

/-- Certificate-checked tangent normal reduction is lawful on its explicit acceptance domain. -/
instance instLawfulCNormalReductionTangentCompleteDomain
    (raw : CNormalReduction DensePoly α) :
    LawfulCNormalReduction (tangentNormalReduction raw) (tangentNormalCompleteDomain raw) := by
  unfold tangentNormalReduction tangentNormalCompleteDomain
  infer_instance

/-- The tangent normal stage remains genuinely lawful on its explicit acceptance domain. -/
instance instLawfulGenuineCNormalReductionTangentCompleteDomain
    (raw : CNormalReduction DensePoly α) :
    LawfulGenuineCNormalReduction (tangentNormalReduction raw) (tangentNormalCompleteDomain raw) := by
  unfold tangentNormalReduction tangentNormalCompleteDomain
  infer_instance

/-- Certificate-checked tangent normal reduction is complete on its explicit acceptance domain. -/
instance instCompleteCNormalReductionTangent (raw : CNormalReduction DensePoly α) :
    CompleteCNormalReduction (tangentNormalReduction raw) (tangentNormalCompleteDomain raw) := by
  unfold tangentNormalReduction tangentNormalCompleteDomain
  infer_instance

/-- Assemble a certificate-checked tangent Risch level from arbitrary coupled and special integrators. -/
def tangentRischLevel (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind) (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation DensePoly α] : CRischLevel DensePoly α :=
  oneLevelRisch R kind (tangentNormalReduction raw) (checkedTangentMonomialCase S T)

/-- The explicit stage-acceptance domain of a certificate-checked tangent Risch level. -/
def tangentRischLevelCompleteDomain (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation DensePoly α] : RischLevelDomain DensePoly α :=
  oneLevelRischCompleteDomain R kind polynomialDomain (tangentNormalCompleteDomain raw)
    (checkedTangentSpecialDomain S T)

/-- Certificate checks make the dense tangent Risch level sound without solver or bridge laws. -/
instance instLawfulCRischLevelTangent (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (tangentRischLevel R kind raw S T)
      (oneLevelRischSoundDomain tangentNormalDomain) := by
  unfold tangentRischLevel
  infer_instance

/-- Certificate checks make every successful dense tangent level a genuine elementary result. -/
instance instLawfulGenuineCRischLevelTangent (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulGenuineCRischLevel (tangentRischLevel R kind raw S T)
      (oneLevelRischSoundDomain tangentNormalDomain) := by
  unfold tangentRischLevel
  infer_instance

/-- The certificate-checked tangent level is lawful on its complete stage-acceptance domain. -/
instance instLawfulCRischLevelTangentCompleteDomain
    (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (tangentRischLevel R kind raw S T)
      (tangentRischLevelCompleteDomain R kind polynomialDomain raw S T) := by
  unfold tangentRischLevel tangentRischLevelCompleteDomain
  infer_instance

/-- The complete-stage tangent domain inherits genuine successful outputs. -/
instance instLawfulGenuineCRischLevelTangentCompleteDomain
    (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulGenuineCRischLevel (tangentRischLevel R kind raw S T)
      (tangentRischLevelCompleteDomain R kind polynomialDomain raw S T) := by
  unfold tangentRischLevel tangentRischLevelCompleteDomain
  infer_instance

/-- Complete polynomial, normal, and checked tangent stages compose to a relatively complete tangent level
on the explicit stage-acceptance domain. -/
instance instCompleteCRischLevelTangent (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CompleteCPolynomialReduction R polynomialDomain]
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    CompleteCRischLevel (tangentRischLevel R kind raw S T)
      (tangentRischLevelCompleteDomain R kind polynomialDomain raw S T) := by
  exact completeCRischLevel R kind polynomialDomain (tangentNormalReduction raw)
    (tangentNormalCompleteDomain raw) (checkedTangentMonomialCase S T)
    (checkedTangentSpecialDomain S T)

/-- Assemble a sparse tangent Risch level whose dense special result is certificate-checked. -/
def sparseTangentRischLevel (R : CPolynomialReduction CPoly.SparsePoly α)
    (kind : PolynomialReductionKind) (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α] :
    CRischLevel CPoly.SparsePoly α :=
  oneLevelRisch R kind (checkedNormalReduction raw)
    (denseMonomialCaseAsSparse (checkedTangentMonomialCase S T))

/-- Certificate checks preserve tangent soundness across the sparse representation boundary. -/
instance instLawfulCRischLevelSparseTangent
    (R : CPolynomialReduction CPoly.SparsePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := α)] :
    LawfulCRischLevel (sparseTangentRischLevel R kind raw S T)
      (oneLevelRischSoundDomain
        (checkedNormalReductionDomain (P := CPoly.SparsePoly) (α := α))) := by
  unfold sparseTangentRischLevel
  infer_instance

/-- Certificate checks preserve genuine tangent logarithms across the sparse representation boundary. -/
instance instLawfulGenuineCRischLevelSparseTangent
    (R : CPolynomialReduction CPoly.SparsePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := α)] :
    LawfulGenuineCRischLevel (sparseTangentRischLevel R kind raw S T)
      (oneLevelRischSoundDomain
        (checkedNormalReductionDomain (P := CPoly.SparsePoly) (α := α))) := by
  unfold sparseTangentRischLevel
  infer_instance

/-- The explicit special-stage domain obtained by transporting the checked dense tangent domain to sparse
polynomial inputs. -/
def sparseTangentSpecialDomain (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α) :
    MonomialSpecialDomain CPoly.SparsePoly α := fun Dt fp b ds =>
  checkedTangentSpecialDomain S T (CPolyEngine.convert Dt) (CPolyEngine.convert fp)
    (CPolyEngine.convert b) (CPolyEngine.convert ds)

/-- Checked tangent special completeness transports through the sparse monomial-case adapter. -/
instance instCompleteCMonomialCaseSparseCheckedTangent (S : CTangentCoefficientSolver α)
    (T : CTangentSpecialIntegrator α) :
    CompleteCMonomialCase (denseMonomialCaseAsSparse (checkedTangentMonomialCase S T))
      (sparseTangentSpecialDomain S T) := by
  unfold sparseTangentSpecialDomain
  infer_instance

/-- Certificate-checked sparse normal reduction is lawful on its explicit acceptance domain. -/
instance instLawfulCNormalReductionSparseTangentCompleteDomain
    (raw : CNormalReduction CPoly.SparsePoly α) :
    LawfulCNormalReduction (checkedNormalReduction raw)
      (checkedNormalReductionAcceptanceDomain raw) := by
  unfold checkedNormalReductionAcceptanceDomain
  infer_instance

/-- The explicit stage-acceptance domain of a sparse certificate-checked tangent Risch level. -/
def sparseTangentRischLevelCompleteDomain
    (R : CPolynomialReduction CPoly.SparsePoly α)
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain CPoly.SparsePoly α)
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α] :
    RischLevelDomain CPoly.SparsePoly α :=
  oneLevelRischCompleteDomain R kind polynomialDomain (checkedNormalReductionAcceptanceDomain raw)
    (sparseTangentSpecialDomain S T)

/-- The sparse checked tangent level is lawful on its complete stage-acceptance domain. -/
instance instLawfulCRischLevelSparseTangentCompleteDomain
    (R : CPolynomialReduction CPoly.SparsePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain CPoly.SparsePoly α)
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := α)] :
    LawfulCRischLevel (sparseTangentRischLevel R kind raw S T)
      (sparseTangentRischLevelCompleteDomain R kind polynomialDomain raw S T) := by
  unfold sparseTangentRischLevel sparseTangentRischLevelCompleteDomain sparseTangentSpecialDomain
  infer_instance

/-- The sparse complete-stage domain inherits genuine successful outputs. -/
instance instLawfulGenuineCRischLevelSparseTangentCompleteDomain
    (R : CPolynomialReduction CPoly.SparsePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain CPoly.SparsePoly α)
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := α)] :
    LawfulGenuineCRischLevel (sparseTangentRischLevel R kind raw S T)
      (sparseTangentRischLevelCompleteDomain R kind polynomialDomain raw S T) := by
  unfold sparseTangentRischLevel sparseTangentRischLevelCompleteDomain sparseTangentSpecialDomain
  infer_instance

/-- Complete polynomial, normal, and checked tangent stages compose to a relatively complete sparse tangent
level on the transported stage-acceptance domain. -/
instance instCompleteCRischLevelSparseTangent
    (R : CPolynomialReduction CPoly.SparsePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain CPoly.SparsePoly α)
    [CompleteCPolynomialReduction R polynomialDomain]
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α) (T : CTangentSpecialIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := α)] :
    CompleteCRischLevel (sparseTangentRischLevel R kind raw S T)
      (sparseTangentRischLevelCompleteDomain R kind polynomialDomain raw S T) := by
  exact completeCRischLevel R kind polynomialDomain (checkedNormalReduction raw)
    (checkedNormalReductionAcceptanceDomain raw)
    (denseMonomialCaseAsSparse (checkedTangentMonomialCase S T))
    (sparseTangentSpecialDomain S T)

end DeepWiki.SymbolicIntegration
