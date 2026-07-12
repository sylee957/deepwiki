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

/-- The typed handoff from explicit normal reduction to explicit normal postprocessing. -/
def IsDifferentialNormalPostprocessHandoff
    (C : MonomialDifferentialContext (P := P) α) (input : NormalReductionInput P α) (_ : Unit)
    (next : DifferentialNormalPostprocessInput C) : Prop :=
  CertifiedDifferentialNormalResult C input.derivative input.numerator input.denominator next.normalResult ∧
    next.source.derivative = input.derivative ∧ next.source.numerator = input.numerator ∧
      next.source.denominator = input.denominator

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

/-- Export explicit normal reduction with a typed remainder for the postprocessor. -/
noncomputable def CDifferentialNormalReduction.asPostprocessHandoffStage
    (C : MonomialDifferentialContext (P := P) α)
    (domain : DifferentialNormalReductionDomain P α)
    [CDifferentialNormalReduction P α C.derivation]
    [LawfulCDifferentialNormalReduction C domain]
    [CompleteCDifferentialNormalReduction C domain] :
    RemainderIntegrationStage (NormalReductionInput P α) Unit (DifferentialNormalPostprocessInput C)
      (fun input => IsDifferentialNormalPartIntegrable C input.derivative input.numerator input.denominator)
      (IsDifferentialNormalPostprocessHandoff C) :=
  { stage :=
      { run := fun _ input =>
          (CDifferentialNormalReduction.reduce C.derivation input.derivative input.numerator
            input.denominator).map fun out => ⟨(), ⟨input, out⟩⟩
        domain := fun input => domain input.derivative input.numerator input.denominator
        sound := by
          intro _ input result hdomain hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact ⟨LawfulCDifferentialNormalReduction.sound input.derivative input.numerator
            input.denominator out hdomain input.denominator_nonzero hout, rfl, rfl, rfl⟩
        complete := by
          intro input hdomain hintegrable
          obtain ⟨out, hout, _⟩ := CompleteCDifferentialNormalReduction.relative_complete
            (C := C) (domain := domain) input.derivative input.numerator input.denominator
              hdomain input.denominator_nonzero hintegrable
          exact ⟨0, ⟨(), ⟨input, out⟩⟩, by simp [hout]⟩ } }

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

/-- Compose explicit normal reduction and monomial-specific normal postprocessing. -/
noncomputable def CDifferentialNormalReduction.asPostprocessedRemainderStage
    (C : MonomialDifferentialContext (P := P) α)
    (normalDomain : DifferentialNormalReductionDomain P α)
    [CDifferentialNormalReduction P α C.derivation]
    [LawfulCDifferentialNormalReduction C normalDomain]
    [CompleteCDifferentialNormalReduction C normalDomain]
    [CDifferentialNormalPostprocessor P α C.derivation]
    [LawfulCDifferentialNormalPostprocessor C]
    [CompleteCDifferentialNormalPostprocessor C] :
    RemainderIntegrationStage (NormalReductionInput P α) (IntegralResult α P) Unit
      (fun input => IsDifferentialNormalPartIntegrable C input.derivative input.numerator input.denominator)
      (fun input result _ =>
        CertifiedDifferentialNormalResult C input.derivative input.numerator input.denominator result) := by
  let normal := CDifferentialNormalReduction.asPostprocessHandoffStage C normalDomain
  let postprocess := CDifferentialNormalPostprocessor.asRemainderIntegrationStage C
  let composed :
      RemainderIntegrationStage (NormalReductionInput P α) (Unit × IntegralResult α P) Unit
        (fun input => IsDifferentialNormalPartIntegrable C input.derivative input.numerator input.denominator)
        (fun input output _ =>
          CertifiedDifferentialNormalResult C input.derivative input.numerator input.denominator output.2) :=
    normal.compose postprocess
      (fun input => normalDomain input.derivative input.numerator input.denominator)
      (fun input => IsDifferentialNormalPartIntegrable C input.derivative input.numerator input.denominator)
      (by
        intro input hdomain
        exact hdomain)
      (by
        intro input _ next _ hhandoff
        rcases hhandoff with ⟨hcertified, hderivative, hnum, hden⟩
        change CertifiedDifferentialNormalResult C next.source.derivative next.source.numerator
          next.source.denominator next.normalResult
        simpa [hderivative, hnum, hden] using hcertified)
      (by
        intro input hintegrable
        exact ⟨hintegrable, fun _ _ _ => True.intro⟩)
      (by
        intro input _ next result _ hhandoff hpostprocess
        rcases hhandoff with ⟨_, hderivative, hnum, hden⟩
        simpa [hderivative, hnum, hden] using hpostprocess)
  exact composed.mapOutput Prod.snd (by
    intro input _ _ hcorrect
    exact hcorrect)

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
