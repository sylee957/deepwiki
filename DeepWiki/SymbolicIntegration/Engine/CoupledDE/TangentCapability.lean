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

/-- Executable data for one tangent coupled-system call. -/
structure TangentCoupledProblem where
  /-- Coefficient-degree search bound. -/
  degreeBound : ℕ
  /-- Diagonal constant coefficient. -/
  diagonal : DensePoly ℚ
  /-- Off-diagonal coefficient. -/
  offDiagonal : DensePoly ℚ
  /-- First coupled right-hand side. -/
  rhs₁ : List (DensePoly ℚ)
  /-- Second coupled right-hand side. -/
  rhs₂ : List (DensePoly ℚ)
  /-- Tangent-system level. -/
  level : ℕ

/-- Prop-free boundary that prepares and reassembles the tangent coupled special problem. -/
structure CTangentSpecialBridge where
  /-- Translate a canonical special fraction into a coupled problem. -/
  prepare : DensePoly (DenseFrac ℚ) → DensePoly (DenseFrac ℚ) → DensePoly (DenseFrac ℚ) →
    DensePoly (DenseFrac ℚ) → Option TangentCoupledProblem
  /-- Reassemble a coupled solution as the represented special antiderivative. -/
  reassemble : TangentCoupledProblem → List (DensePoly ℚ) → List (DensePoly ℚ) →
    DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)

/-- Semantic reconstruction contract for the missing tangent special bridge. -/
class LawfulCTangentSpecialBridge (B : CTangentSpecialBridge) : Prop where
  /-- Preparing, solving, and reassembling yields the required special-part identity. -/
  sound : ∀ (Dt fp b ds : DensePoly (DenseFrac ℚ)) (p : TangentCoupledProblem)
      (q₁ q₂ : List (DensePoly ℚ)),
    B.prepare Dt fp b ds = some p →
    TanSolves p.diagonal p.offDiagonal p.level p.rhs₁ p.rhs₂ q₁ q₂ →
    let out := B.reassemble p q₁ q₂
    CPoly.toPoly out.2 ≠ 0 ∧
      towerFractionFieldDerivP Dt (fieldFracP out.1 out.2) =
        fieldFracP fp CPoly.one + fieldFracP b ds

/-- Relative-completeness contract connecting tangent preparation to a bounded coupled solver. -/
class CompleteCTangentSpecialBridge (S : CTangentCoupledSolver) (B : CTangentSpecialBridge) : Prop where
  /-- Every valid tangent special antiderivative prepares a problem at a successful solver bound. -/
  complete : ∀ (Dt fp b ds snum sden : DensePoly (DenseFrac ℚ)),
    CPoly.toPoly sden ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP snum sden) =
      fieldFracP fp CPoly.one + fieldFracP b ds →
    ∃ p q₁ q₂, B.prepare Dt fp b ds = some p ∧
      S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level = some (q₁, q₂)

/-- Compose a tangent coupled solver and special bridge into a monomial-case operation. -/
def tangentMonomialCase (S : CTangentCoupledSolver) (B : CTangentSpecialBridge) :
    CMonomialCase DensePoly (DenseFrac ℚ) where
  integrateSpecial Dt fp b ds := do
    let p ← B.prepare Dt fp b ds
    let (q₁, q₂) ← S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level
    some (B.reassemble p q₁ q₂)
  postprocessNormal _ before := some before

/-- Lawful coupled solving and reconstruction make the composed tangent monomial case lawful. -/
instance instLawfulCMonomialCaseTangent (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [LawfulCTangentCoupledSolver S] [LawfulCTangentSpecialBridge B] :
    LawfulCMonomialCase (tangentMonomialCase S B) where
  special_sound Dt fp b ds snum sden hrun := by
    simp only [tangentMonomialCase] at hrun
    rcases hprepare : B.prepare Dt fp b ds with _ | p
    · simp [hprepare] at hrun
    · rw [hprepare] at hrun
      change (S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level).bind
        (fun q => some (B.reassemble p q.1 q.2)) = some (snum, sden) at hrun
      rcases hsolve : S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level with
        _ | ⟨q₁, q₂⟩
      · simp [hsolve] at hrun
      · simp only [hsolve, Option.bind_some, Option.some.injEq] at hrun
        have hnum : (B.reassemble p q₁ q₂).1 = snum := congrArg Prod.fst hrun
        have hden : (B.reassemble p q₁ q₂).2 = sden := congrArg Prod.snd hrun
        rw [← hnum, ← hden]
        exact LawfulCTangentSpecialBridge.sound Dt fp b ds p q₁ q₂ hprepare
          (LawfulCTangentCoupledSolver.sound p.degreeBound p.diagonal p.offDiagonal
            p.rhs₁ p.rhs₂ q₁ q₂ p.level hsolve)
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

/-- Complete tangent preparation and bounded solving make the composed monomial case relatively complete. -/
instance instCompleteCMonomialCaseTangent (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [CompleteCTangentSpecialBridge S B] : CompleteCMonomialCase (tangentMonomialCase S B) where
  special_complete Dt fp b ds snum sden hsden hderiv := by
    obtain ⟨p, q₁, q₂, hprepare, hsolve⟩ :=
      CompleteCTangentSpecialBridge.complete (S := S) (B := B)
        Dt fp b ds snum sden hsden hderiv
    refine ⟨B.reassemble p q₁ q₂, ?_⟩
    simp [tangentMonomialCase, hprepare, hsolve]
  postprocess_complete _ _ _ before _ := ⟨before, rfl⟩

/-- Certificate-check a tangent bridge's reassembled special fraction before releasing it. -/
def checkedTangentMonomialCase (S : CTangentCoupledSolver) (B : CTangentSpecialBridge) :
    CMonomialCase DensePoly (DenseFrac ℚ) where
  integrateSpecial Dt fp b ds := do
    let p ← B.prepare Dt fp b ds
    let qs ← S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level
    let out := B.reassemble p qs.1 qs.2
    if CPolyEngine.cisZero ds then none
    else if CPolyEngine.cisZero out.2 then none
    else
      let result : IntegralResult (DenseFrac ℚ) := { rational := out, logs := [] }
      if DensePoly.checkIdentity Dt result (polynomialSpecialNumerator fp b ds) ds then some out else none
  postprocessNormal _ before := some before

/-- The certificate-checked tangent monomial case is sound without a lawful bridge assumption. -/
instance instLawfulCMonomialCaseCheckedTangent (S : CTangentCoupledSolver) (B : CTangentSpecialBridge) :
    LawfulCMonomialCase (checkedTangentMonomialCase S B) where
  special_sound Dt fp b ds snum sden hrun := by
    simp only [checkedTangentMonomialCase] at hrun
    rcases hprepare : B.prepare Dt fp b ds with _ | p
    · simp [hprepare] at hrun
    rw [hprepare] at hrun
    change (S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level).bind
      (fun qs =>
        if CPolyEngine.cisZero ds then none
        else if CPolyEngine.cisZero (B.reassemble p qs.1 qs.2).2 then none
        else
          let result : IntegralResult (DenseFrac ℚ) :=
            { rational := B.reassemble p qs.1 qs.2, logs := [] }
          if DensePoly.checkIdentity Dt result (polynomialSpecialNumerator fp b ds) ds then
            some (B.reassemble p qs.1 qs.2)
          else none) = some (snum, sden) at hrun
    rcases hsolve : S.solve p.degreeBound p.diagonal p.offDiagonal p.rhs₁ p.rhs₂ p.level with
      _ | qs
    · simp [hsolve] at hrun
    rw [hsolve] at hrun
    simp only [Option.bind_some] at hrun
    let hif := hrun
    split at hif
    · simp at hif
    rename_i hds
    simp at hif
    obtain ⟨hsden, hcheck, hout⟩ := hif
    have hds' : CPoly.toPoly ds ≠ 0 :=
      CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (Bool.eq_false_iff.mpr hds)
    have houtRaw : CPoly.toPoly (B.reassemble p qs.1 qs.2).2 ≠ 0 :=
      CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false hsden
    have hout' : CPoly.toPoly sden ≠ 0 := by
      simpa [hout] using houtRaw
    let result : IntegralResult (DenseFrac ℚ) := { rational := B.reassemble p qs.1 qs.2, logs := [] }
    have hid := field_identity_of_checkIdentityP Dt result (polynomialSpecialNumerator fp b ds) ds
      houtRaw hds' (by simp [result]) hcheck
    simp only [result, logResidueSumP, List.map_nil, List.sum_nil, add_zero] at hid
    refine ⟨hout', ?_⟩
    change (towerFractionFieldDerivP Dt)
      (fieldFracP (B.reassemble p qs.1 qs.2).1 (B.reassemble p qs.1 qs.2).2) =
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

/-- Assemble a tangent Risch level from polynomial, raw normal, coupled-solver, and bridge operations. -/
def tangentRischLevel (R : CPolynomialReduction DensePoly (DenseFrac ℚ))
    (kind : PolynomialReductionKind) (raw : CNormalReduction DensePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [CCanonicalRepresentation DensePoly (DenseFrac ℚ)] : CRischLevel DensePoly (DenseFrac ℚ) :=
  oneLevelRisch R kind (tangentNormalReduction raw) (tangentMonomialCase S B)

/-- Lawful tangent stages compose into a sound one-level Risch solver on the checked normal domain. -/
instance instLawfulCRischLevelTangent (R : CPolynomialReduction DensePoly (DenseFrac ℚ))
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction DensePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [LawfulCTangentCoupledSolver S] [LawfulCTangentSpecialBridge B]
    [CCanonicalRepresentation DensePoly (DenseFrac ℚ)]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFrac ℚ)] :
    LawfulCRischLevel (tangentRischLevel R kind raw S B)
      (oneLevelRischSoundDomain tangentNormalDomain) := by
  unfold tangentRischLevel
  infer_instance

/-- Assemble a certificate-checked tangent Risch level from arbitrary coupled and bridge operations. -/
def checkedTangentRischLevel (R : CPolynomialReduction DensePoly (DenseFrac ℚ))
    (kind : PolynomialReductionKind) (raw : CNormalReduction DensePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [CCanonicalRepresentation DensePoly (DenseFrac ℚ)] : CRischLevel DensePoly (DenseFrac ℚ) :=
  oneLevelRisch R kind (tangentNormalReduction raw) (checkedTangentMonomialCase S B)

/-- Certificate checks make the dense tangent Risch level sound without solver or bridge laws. -/
instance instLawfulCRischLevelCheckedTangent (R : CPolynomialReduction DensePoly (DenseFrac ℚ))
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction DensePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [CCanonicalRepresentation DensePoly (DenseFrac ℚ)]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := DenseFrac ℚ)] :
    LawfulCRischLevel (checkedTangentRischLevel R kind raw S B)
      (oneLevelRischSoundDomain tangentNormalDomain) := by
  unfold checkedTangentRischLevel
  infer_instance

/-- Assemble a sparse tangent Risch level using a sparse raw normal reducer and dense coupled bridge. -/
def sparseTangentRischLevel (R : CPolynomialReduction CPoly.SparsePoly (DenseFrac ℚ))
    (kind : PolynomialReductionKind) (raw : CNormalReduction CPoly.SparsePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [CCanonicalRepresentation CPoly.SparsePoly (DenseFrac ℚ)] :
    CRischLevel CPoly.SparsePoly (DenseFrac ℚ) :=
  oneLevelRisch R kind (checkedNormalReduction raw)
    (denseMonomialCaseAsSparse (tangentMonomialCase S B))

/-- Lawful tangent stages remain sound after transport through the sparse representation boundary. -/
instance instLawfulCRischLevelSparseTangent
    (R : CPolynomialReduction CPoly.SparsePoly (DenseFrac ℚ))
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction CPoly.SparsePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [LawfulCTangentCoupledSolver S] [LawfulCTangentSpecialBridge B]
    [CCanonicalRepresentation CPoly.SparsePoly (DenseFrac ℚ)]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFrac ℚ)] :
    LawfulCRischLevel (sparseTangentRischLevel R kind raw S B)
      (oneLevelRischSoundDomain
        (checkedNormalReductionDomain (P := CPoly.SparsePoly) (α := DenseFrac ℚ))) := by
  unfold sparseTangentRischLevel
  infer_instance

/-- Assemble a sparse tangent Risch level whose dense special result is certificate-checked. -/
def checkedSparseTangentRischLevel (R : CPolynomialReduction CPoly.SparsePoly (DenseFrac ℚ))
    (kind : PolynomialReductionKind) (raw : CNormalReduction CPoly.SparsePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [CCanonicalRepresentation CPoly.SparsePoly (DenseFrac ℚ)] :
    CRischLevel CPoly.SparsePoly (DenseFrac ℚ) :=
  oneLevelRisch R kind (checkedNormalReduction raw)
    (denseMonomialCaseAsSparse (checkedTangentMonomialCase S B))

/-- Certificate checks preserve tangent soundness across the sparse representation boundary. -/
instance instLawfulCRischLevelCheckedSparseTangent
    (R : CPolynomialReduction CPoly.SparsePoly (DenseFrac ℚ))
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (raw : CNormalReduction CPoly.SparsePoly (DenseFrac ℚ))
    (S : CTangentCoupledSolver) (B : CTangentSpecialBridge)
    [CCanonicalRepresentation CPoly.SparsePoly (DenseFrac ℚ)]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := DenseFrac ℚ)] :
    LawfulCRischLevel (checkedSparseTangentRischLevel R kind raw S B)
      (oneLevelRischSoundDomain
        (checkedNormalReductionDomain (P := CPoly.SparsePoly) (α := DenseFrac ℚ))) := by
  unfold checkedSparseTangentRischLevel
  infer_instance

end DeepWiki.SymbolicIntegration
