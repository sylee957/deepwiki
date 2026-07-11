import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentReconstruct
import DeepWiki.SymbolicIntegration.Engine.MonomialCaseSparse
import DeepWiki.SymbolicIntegration.Engine.RischLevel
import DeepWiki.SymbolicIntegration.Engine.CheckIdentityCorrect

/-! # Tangent coupled-solver capability

The hypertangent monomial case reduces special integration to a coupled differential system. This module
isolates preparation and reconstruction behind explicit soundness and relative-completeness contracts. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- Prop-free executable capability for the tangent coupled differential system over `ℚ(x)[t]`. -/
structure CTangentCoupledSolver where
  /-- Solve the level-`n` tangent system with the supplied coefficient-degree bound. -/
  solve : ℕ → DensePoly ℚ → DensePoly ℚ → List (DensePoly ℚ) → List (DensePoly ℚ) → ℕ →
    Option (List (DensePoly ℚ) × List (DensePoly ℚ))

/-- Denotation-level soundness contract for a tangent coupled solver. -/
class LawfulCTangentCoupledSolver (C : CTangentCoupledSolver) : Prop where
  /-- Every returned pair solves the requested tangent system. -/
  sound : ∀ (dbound : ℕ) (b0 b2 : DensePoly ℚ) (c1 c2 q1 q2 : List (DensePoly ℚ)) (n : ℕ),
    C.solve dbound b0 b2 c1 c2 n = some (q1, q2) → TanSolves b0 b2 n c1 c2 q1 q2

/-- Relative-completeness contract for a tangent coupled solver. -/
class CompleteCTangentCoupledSolver (C : CTangentCoupledSolver) : Prop where
  /-- Any solvable system is found at some finite coefficient-degree bound. -/
  complete : ∀ (b0 b2 : DensePoly ℚ) (c1 c2 : List (DensePoly ℚ)) (n : ℕ),
    (∃ q1 q2, TanSolves b0 b2 n c1 c2 q1 q2) →
      ∃ dbound q1 q2, C.solve dbound b0 b2 c1 c2 n = some (q1, q2)

/-- The existing degree-bounded tangent cancellation algorithm as a coupled-solver capability. -/
def tangentCoupledSolver [CLinearSolve ℚ] : CTangentCoupledSolver where
  solve := cCoupledDECancelTan

/-- The tangent cancellation algorithm realizes the coupled-solver soundness contract. -/
instance instLawfulCTangentCoupledSolver [CLinearSolve ℚ] [LawfulCLinearSolve ℚ] :
    LawfulCTangentCoupledSolver tangentCoupledSolver where
  sound dbound b0 b2 c1 c2 q1 q2 n hrun :=
    DensePoly.reconstruct dbound b0 n b2 c1 c2 q1 q2 hrun

/-- Semantic domain on which a tangent special integrator is required to be complete. -/
abbrev TangentSpecialDomain := DensePoly (DenseFrac ℚ) → DensePoly (DenseFrac ℚ) →
  DensePoly (DenseFrac ℚ) → DensePoly (DenseFrac ℚ) → Prop

/-- Prop-free recursive hypertangent special integrator parameterized by a coupled-system solver. -/
structure CTangentSpecialIntegrator where
  /-- Integrate the polynomial and special-denominator parts, making as many coupled calls as required. -/
  integrate : CTangentCoupledSolver → DensePoly (DenseFrac ℚ) → DensePoly (DenseFrac ℚ) →
    DensePoly (DenseFrac ℚ) → DensePoly (DenseFrac ℚ) →
      Option (DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ))

/-- Denotational soundness contract for a selected tangent special integrator and coupled solver. -/
class LawfulCTangentSpecialIntegrator (S : CTangentCoupledSolver)
    (T : CTangentSpecialIntegrator) : Prop where
  /-- Every returned fraction differentiates to the requested polynomial and special parts. -/
  sound : ∀ (Dt fp b ds snum sden : DensePoly (DenseFrac ℚ)),
    T.integrate S Dt fp b ds = some (snum, sden) →
      CPoly.toPoly sden ≠ 0 ∧
        towerFractionFieldDerivP Dt (fieldFracP snum sden) =
          fieldFracP fp CPoly.one + fieldFracP b ds

/-- Relative-completeness contract for recursive tangent special integration. -/
class CompleteCTangentSpecialIntegrator (S : CTangentCoupledSolver)
    (T : CTangentSpecialIntegrator) (domain : TangentSpecialDomain)
    [LawfulCTangentSpecialIntegrator S T] : Prop where
  /-- Every domain input possessing a represented special antiderivative is accepted. -/
  complete : ∀ (Dt fp b ds snum sden : DensePoly (DenseFrac ℚ)),
    domain Dt fp b ds → CPoly.toPoly sden ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP snum sden) =
      fieldFracP fp CPoly.one + fieldFracP b ds →
    ∃ out, T.integrate S Dt fp b ds = some out

/-- Compose a tangent coupled solver and recursive special integrator into a monomial case. -/
def tangentMonomialCase (S : CTangentCoupledSolver) (T : CTangentSpecialIntegrator) :
    CMonomialCase DensePoly (DenseFrac ℚ) where
  integrateSpecial := T.integrate S
  postprocessNormal _ before := some before

/-- A lawful recursive tangent special integrator makes the composed monomial case lawful. -/
instance instLawfulCMonomialCaseTangent (S : CTangentCoupledSolver) (T : CTangentSpecialIntegrator)
    [LawfulCTangentSpecialIntegrator S T] : LawfulCMonomialCase (tangentMonomialCase S T) where
  special_sound Dt fp b ds snum sden hrun :=
    LawfulCTangentSpecialIntegrator.sound Dt fp b ds snum sden hrun
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

/-- Complete recursive tangent integration makes the composed monomial case relatively complete. -/
instance instCompleteCMonomialCaseTangent (S : CTangentCoupledSolver) (T : CTangentSpecialIntegrator)
    (domain : TangentSpecialDomain) [LawfulCTangentSpecialIntegrator S T]
    [CompleteCTangentSpecialIntegrator S T domain] :
    CompleteCMonomialCase (tangentMonomialCase S T) domain where
  special_complete Dt fp b ds snum sden hdomain hsden hderiv := by
    obtain ⟨out, hrun⟩ := CompleteCTangentSpecialIntegrator.complete
      (S := S) (T := T) (domain := domain) Dt fp b ds snum sden hdomain hsden hderiv
    exact ⟨out, hrun⟩
  postprocess_complete _ _ _ before _ := ⟨before, rfl⟩

/-- Certificate-check a tangent special integrator's returned fraction before releasing it. -/
def checkedTangentMonomialCase (S : CTangentCoupledSolver) (T : CTangentSpecialIntegrator) :
    CMonomialCase DensePoly (DenseFrac ℚ) where
  integrateSpecial Dt fp b ds := do
    let out ← T.integrate S Dt fp b ds
    if CPolyEngine.cisZero ds then none
    else if CPolyEngine.cisZero out.2 then none
    else
      let result : IntegralResult (DenseFrac ℚ) := { rational := out, logs := [] }
      if CPoly.checkIdentity Dt result (polynomialSpecialNumerator fp b ds) ds then some out else none
  postprocessNormal _ before := some before

/-- The certificate-checked tangent monomial case is sound without a lawful integrator assumption. -/
instance instLawfulCMonomialCaseCheckedTangent (S : CTangentCoupledSolver)
    (T : CTangentSpecialIntegrator) : LawfulCMonomialCase (checkedTangentMonomialCase S T) where
  special_sound Dt fp b ds snum sden hrun := by
    simp only [checkedTangentMonomialCase] at hrun
    change (T.integrate S Dt fp b ds).bind
      (fun out =>
        if CPolyEngine.cisZero ds then none
        else if CPolyEngine.cisZero out.2 then none
        else
          let result : IntegralResult (DenseFrac ℚ) :=
            { rational := out, logs := [] }
          if CPoly.checkIdentity Dt result (polynomialSpecialNumerator fp b ds) ds then
            some out
          else none) = some (snum, sden) at hrun
    rcases hraw : T.integrate S Dt fp b ds with _ | out
    · simp [hraw] at hrun
    rw [hraw] at hrun
    simp only [Option.bind_some] at hrun
    let hif := hrun
    split at hif
    · simp at hif
    rename_i hds
    simp at hif
    obtain ⟨hsden, hcheck, hout⟩ := hif
    have hds' : CPoly.toPoly ds ≠ 0 :=
      CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (Bool.eq_false_iff.mpr hds)
    have houtRaw : CPoly.toPoly out.2 ≠ 0 :=
      CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false hsden
    have hout' : CPoly.toPoly sden ≠ 0 := by
      simpa [hout] using houtRaw
    let result : IntegralResult (DenseFrac ℚ) := { rational := out, logs := [] }
    have hid := field_identity_of_checkIdentityP Dt result (polynomialSpecialNumerator fp b ds) ds
      houtRaw hds' (by simp [result]) hcheck
    simp only [result, logResidueSumP, List.map_nil, List.sum_nil, add_zero] at hid
    refine ⟨hout', ?_⟩
    change (towerFractionFieldDerivP Dt)
      (fieldFracP out.1 out.2) =
        fieldFracP (polynomialSpecialNumerator fp b ds) ds at hid
    rw [fieldFracP_polynomialSpecialNumerator fp b ds hds'] at hid
    simpa [hout] using hid
  postprocessNormal_sound _ _ _ before after hbefore hrun := by
    change some before = some after at hrun
    have hEq : before = after := Option.some.inj hrun
    subst after
    exact hbefore
  postprocessNormal_den_nonzero _ before after hden hrun := by
    change some before = some after at hrun
    have hEq : before = after := Option.some.inj hrun
    subst after
    exact hden

/-- Tangent normal reduction obtained by certificate-checking an arbitrary raw normal reducer. -/
def tangentNormalReduction (raw : CNormalReduction DensePoly (DenseFrac ℚ)) :
    CNormalReduction DensePoly (DenseFrac ℚ) :=
  checkedNormalReduction raw

/-- Universal soundness domain of certificate-checked tangent normal reduction. -/
def tangentNormalDomain : NormalReductionDomain DensePoly (DenseFrac ℚ) :=
  checkedNormalReductionDomain

/-- Certificate-checked tangent normal reduction is lawful without a low-degree Hermite hypothesis. -/
instance instLawfulCNormalReductionTangent (raw : CNormalReduction DensePoly (DenseFrac ℚ)) :
    LawfulCNormalReduction (tangentNormalReduction raw) tangentNormalDomain := by
  unfold tangentNormalReduction tangentNormalDomain
  infer_instance

/-- Assemble a certificate-checked tangent Risch level from arbitrary coupled and special integrators. -/
def tangentRischLevel (R : CPolynomialReduction DensePoly (DenseFrac ℚ))
    (kind : PolynomialReductionKind) (raw : CNormalReduction DensePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (T : CTangentSpecialIntegrator)
    [CCanonicalRepresentation DensePoly (DenseFrac ℚ)] : CRischLevel DensePoly (DenseFrac ℚ) :=
  oneLevelRisch R kind (tangentNormalReduction raw) (checkedTangentMonomialCase S T)

/-- Certificate checks make the dense tangent Risch level sound without solver or bridge laws. -/
instance instLawfulCRischLevelTangent (R : CPolynomialReduction DensePoly (DenseFrac ℚ))
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction DensePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (T : CTangentSpecialIntegrator)
    [CCanonicalRepresentation DensePoly (DenseFrac ℚ)]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFrac ℚ)] :
    LawfulCRischLevel (tangentRischLevel R kind raw S T)
      (oneLevelRischSoundDomain tangentNormalDomain) := by
  unfold tangentRischLevel
  infer_instance

/-- Assemble a sparse tangent Risch level whose dense special result is certificate-checked. -/
def sparseTangentRischLevel (R : CPolynomialReduction CPoly.SparsePoly (DenseFrac ℚ))
    (kind : PolynomialReductionKind) (raw : CNormalReduction CPoly.SparsePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (T : CTangentSpecialIntegrator)
    [CCanonicalRepresentation CPoly.SparsePoly (DenseFrac ℚ)] :
    CRischLevel CPoly.SparsePoly (DenseFrac ℚ) :=
  oneLevelRisch R kind (checkedNormalReduction raw)
    (denseMonomialCaseAsSparse (checkedTangentMonomialCase S T))

/-- Certificate checks preserve tangent soundness across the sparse representation boundary. -/
instance instLawfulCRischLevelSparseTangent
    (R : CPolynomialReduction CPoly.SparsePoly (DenseFrac ℚ))
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction CPoly.SparsePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (T : CTangentSpecialIntegrator)
    [CCanonicalRepresentation CPoly.SparsePoly (DenseFrac ℚ)]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFrac ℚ)] :
    LawfulCRischLevel (sparseTangentRischLevel R kind raw S T)
      (oneLevelRischSoundDomain
        (checkedNormalReductionDomain (P := CPoly.SparsePoly) (α := DenseFrac ℚ))) := by
  unfold sparseTangentRischLevel
  infer_instance

end DeepWiki.SymbolicIntegration
