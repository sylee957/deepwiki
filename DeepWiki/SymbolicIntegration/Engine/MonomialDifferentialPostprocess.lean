import DeepWiki.SymbolicIntegration.Engine.MonomialDifferentialStage

/-! # Explicit-differential normal postprocessing

The monomial-specific correction applied after normal/Hermite reduction is a separate certified
stage.  Keeping it independent of special integration lets a selected differential compose normal
reduction, correction, and logarithmic reconstruction without reverting to `[CDiffField]`.
-/

namespace DeepWiki.SymbolicIntegration

universe u v

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]

/-- A certified normal result packaged for an explicit monomial-specific postprocessor. -/
structure DifferentialNormalPostprocessInput
    (C : MonomialDifferentialContext (P := P) α) where
  /-- Original normal rational input. -/
  source : NormalReductionInput P α
  /-- Result returned by explicit normal/Hermite reduction. -/
  normalResult : IntegralResult α P

/-- Prop-free monomial-specific correction of an explicit normal result. -/
class CDifferentialNormalPostprocessor
    (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] (derivation : CFieldDerivation α) where
  /-- Correct a normal result for the selected monomial case. -/
  postprocess : P α → IntegralResult α P → Option (IntegralResult α P)

/-- Soundness law for explicit normal postprocessing. -/
class LawfulCDifferentialNormalPostprocessor
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialNormalPostprocessor P α C.derivation] : Prop where
  /-- A successful correction preserves the explicit normal-result certificate. -/
  sound : ∀ (Dt a d : P α) (before after : IntegralResult α P),
    CertifiedDifferentialNormalResult C Dt a d before →
      CDifferentialNormalPostprocessor.postprocess C.derivation Dt before = some after →
        CertifiedDifferentialNormalResult C Dt a d after

/-- Relative completeness law for explicit normal postprocessing. -/
class CompleteCDifferentialNormalPostprocessor
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialNormalPostprocessor P α C.derivation]
    [LawfulCDifferentialNormalPostprocessor C] : Prop where
  /-- Every certified normal result admits a postprocessed result. -/
  complete : ∀ (Dt a d : P α) (before : IntegralResult α P),
    CertifiedDifferentialNormalResult C Dt a d before →
      ∃ after, CDifferentialNormalPostprocessor.postprocess C.derivation Dt before = some after

/-- Export explicit normal postprocessing through the common remainder-stage contract. -/
noncomputable def CDifferentialNormalPostprocessor.asRemainderIntegrationStage
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialNormalPostprocessor P α C.derivation]
    [LawfulCDifferentialNormalPostprocessor C]
    [CompleteCDifferentialNormalPostprocessor C] :
    RemainderIntegrationStage (DifferentialNormalPostprocessInput C) (IntegralResult α P) Unit
      (fun _ => True)
      (fun input result _ =>
        CertifiedDifferentialNormalResult C input.source.derivative input.source.numerator
          input.source.denominator result) :=
  { stage :=
      { run := fun _ input =>
          (CDifferentialNormalPostprocessor.postprocess C.derivation input.source.derivative
            input.normalResult).map fun result => ⟨result, ()⟩
        domain := fun input =>
          CertifiedDifferentialNormalResult C input.source.derivative input.source.numerator
            input.source.denominator input.normalResult
        sound := by
          intro _ input result hcertified hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact LawfulCDifferentialNormalPostprocessor.sound input.source.derivative
            input.source.numerator input.source.denominator input.normalResult out hcertified hout
        complete := by
          intro input hcertified _
          obtain ⟨out, hout⟩ := CompleteCDifferentialNormalPostprocessor.complete
            input.source.derivative input.source.numerator input.source.denominator input.normalResult
              hcertified
          exact ⟨0, ⟨out, ()⟩, by simp [hout]⟩ } }

/-! ### Compatibility adapter for existing monomial cases -/

variable [LawfulCPolyEngine.{u,v} P]
variable [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]

/-- The legacy monomial normal correction viewed as an explicit-differential operation. -/
@[reducible] noncomputable def CMonomialCase.asDifferentialNormalPostprocessor
    (M : CMonomialCase P α) :
    CDifferentialNormalPostprocessor P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation where
  postprocess := M.postprocessNormal

/-- Promote a lawful genuine legacy monomial case to explicit normal-postprocessing soundness. -/
@[reducible] noncomputable def LawfulCDifferentialNormalPostprocessor.ofLegacy
    (M : CMonomialCase P α) [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M] :
    @LawfulCDifferentialNormalPostprocessor P _ _ α _ _
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α))
      (CMonomialCase.asDifferentialNormalPostprocessor M) := by
  letI : CDifferentialNormalPostprocessor P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation :=
    CMonomialCase.asDifferentialNormalPostprocessor M
  refine ⟨?_⟩
  intro Dt a d before after hbefore hrun
  refine ⟨(isDifferentialIntegralResultP_ofCDiffField_iff Dt a d after).mpr
      (LawfulCMonomialCase.postprocessNormal_sound Dt a d before after
        ((isDifferentialIntegralResultP_ofCDiffField_iff Dt a d before).mp hbefore.integral) hrun),
    LawfulCMonomialCase.postprocessNormal_den_nonzero Dt before after hbefore.rationalDen_nonzero hrun,
    ?_, LawfulGenuineCMonomialCase.postprocessNormal_arguments_nonzero Dt before after
      hbefore.arguments_nonzero hrun⟩
  intro cv hcv
  change @Differential.deriv _ _ CDiffFieldSpec.diffK (CFieldSpec.toK cv.1) = 0
  rw [← CDiffFieldSpec.toK_cderiv]
  apply LawfulGenuineCMonomialCase.postprocessNormal_coefficients_constant Dt before after _ hrun cv hcv
  intro old hold
  rw [CDiffFieldSpec.toK_cderiv]
  exact hbefore.coefficients_constant old hold

/-- Promote a complete legacy monomial case to explicit normal-postprocessing completeness. -/
@[reducible] noncomputable def CompleteCDifferentialNormalPostprocessor.ofLegacy
    (M : CMonomialCase P α) (domain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M]
    [CompleteCMonomialCase M domain] :
    @CompleteCDifferentialNormalPostprocessor P _ _ α _ _
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α))
      (CMonomialCase.asDifferentialNormalPostprocessor M)
      (LawfulCDifferentialNormalPostprocessor.ofLegacy M) := by
  letI : CDifferentialNormalPostprocessor P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation :=
    CMonomialCase.asDifferentialNormalPostprocessor M
  letI : LawfulCDifferentialNormalPostprocessor
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)) :=
    LawfulCDifferentialNormalPostprocessor.ofLegacy M
  refine ⟨?_⟩
  intro Dt a d before hbefore
  have hlegacy : CertifiedNormalResult Dt a d before :=
    ⟨(isDifferentialIntegralResultP_ofCDiffField_iff Dt a d before).mp hbefore.integral,
      hbefore.rationalDen_nonzero,
      (by
        intro cv hcv
        rw [CDiffFieldSpec.toK_cderiv]
        exact hbefore.coefficients_constant cv hcv), hbefore.arguments_nonzero⟩
  exact CompleteCMonomialCase.postprocess_complete (C := M) domain Dt a d before hlegacy

end DeepWiki.SymbolicIntegration
