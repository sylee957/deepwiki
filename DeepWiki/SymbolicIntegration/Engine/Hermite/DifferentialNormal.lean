import DeepWiki.SymbolicIntegration.Engine.Hermite.DifferentialStage
import DeepWiki.SymbolicIntegration.Engine.NormalReduction

/-! # Explicit-differential normal reduction

The normal rational-part stage is parameterized by the selected coefficient derivative rather than
the ambient `[CDiffField]` instance.  Its certificates state the rational reconstruction,
genuine-log conditions, and relative completeness in the same explicit differential context used
by the polynomial and coefficient stages.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CFrac

universe u v

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]

/-- The logarithmic residue sum induced by an explicitly selected monomial differential. -/
noncomputable def differentialLogResidueSum
    (C : MonomialDifferentialContext (P := P) α) (Dt : P α) (logs : List (α × P α)) :
    RatFunc (CFieldSpec.K α) :=
  (logs.map fun cv =>
    am α (Polynomial.C (CFieldSpec.toK cv.1)) *
      (C.fractionDeriv Dt (am α (CPoly.toPoly cv.2)) /
        am α (CPoly.toPoly cv.2))).sum

/-- The rational-and-logarithmic antiderivative identity under an explicit monomial differential. -/
def IsDifferentialIntegralResultP
    (C : MonomialDifferentialContext (P := P) α) (Dt anum aden : P α)
    (res : IntegralResult α P) : Prop :=
  C.fractionDeriv Dt
      (am α (CPoly.toPoly res.rational.1) / am α (CPoly.toPoly res.rational.2))
    + differentialLogResidueSum C Dt res.logs
      = am α (CPoly.toPoly anum) / am α (CPoly.toPoly aden)

/-- A normal reduction result certified for an explicit monomial differential. -/
structure CertifiedDifferentialNormalResult
    (C : MonomialDifferentialContext (P := P) α) (Dt a d : P α)
    (out : IntegralResult α P) : Prop where
  /-- The rational and logarithmic parts reconstruct the input fraction. -/
  integral : IsDifferentialIntegralResultP C Dt a d out
  /-- The stored rational denominator denotes a nonzero polynomial. -/
  rationalDen_nonzero : CPoly.toPoly out.rational.2 ≠ 0
  /-- Every logarithmic coefficient is constant for the selected coefficient differential. -/
  coefficients_constant : ∀ cv ∈ out.logs,
    @Differential.deriv _ _ C.differential (CFieldSpec.toK cv.1) = 0
  /-- Every represented logarithm argument denotes a nonzero polynomial. -/
  arguments_nonzero : ∀ cv ∈ out.logs, CPoly.toPoly cv.2 ≠ 0

/-- An input normal fraction has an elementary result under the selected explicit differential. -/
def IsDifferentialNormalPartIntegrable
    (C : MonomialDifferentialContext (P := P) α) (Dt a d : P α) : Prop :=
  ∃ out : IntegralResult α P, CertifiedDifferentialNormalResult C Dt a d out

/-- Prop-free normal-reduction operation selected for one computable coefficient derivative. -/
class CDifferentialNormalReduction
    (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] (derivation : CFieldDerivation α) where
  /-- Reduce a normal fraction to a rational part and logarithmic terms, if successful. -/
  reduce : P α → P α → P α → Option (IntegralResult α P)

/-- Semantic domain of an explicit-differential normal reduction operation. -/
abbrev DifferentialNormalReductionDomain (P : Type u → Type u) (α : Type u) := P α → P α → P α → Prop

/-- Soundness and genuine-log laws for an explicit-differential normal reducer. -/
class LawfulCDifferentialNormalReduction
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialNormalReduction P α C.derivation]
    (domain : DifferentialNormalReductionDomain P α) : Prop where
  /-- Every accepted in-domain result has the explicit reconstruction and genuine-log certificate. -/
  sound : ∀ (Dt a d : P α) (out : IntegralResult α P),
    domain Dt a d → CPoly.toPoly d ≠ 0 →
      CDifferentialNormalReduction.reduce C.derivation Dt a d = some out →
      CertifiedDifferentialNormalResult C Dt a d out

/-- Relative-completeness law for an explicit-differential normal reducer. -/
class CompleteCDifferentialNormalReduction
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialNormalReduction P α C.derivation]
    (domain : DifferentialNormalReductionDomain P α)
    [LawfulCDifferentialNormalReduction C domain] : Prop where
  /-- Every in-domain normal fraction with an explicit elementary witness is eventually accepted. -/
  relative_complete : ∀ (Dt a d : P α),
    domain Dt a d → CPoly.toPoly d ≠ 0 →
      IsDifferentialNormalPartIntegrable C Dt a d →
      ∃ out, CDifferentialNormalReduction.reduce C.derivation Dt a d = some out ∧
        CertifiedDifferentialNormalResult C Dt a d out

/-- Export an explicit-differential normal reducer through the common remainder-stage contract. -/
noncomputable def CDifferentialNormalReduction.asRemainderIntegrationStage
    (C : MonomialDifferentialContext (P := P) α)
    (domain : DifferentialNormalReductionDomain P α)
    [CDifferentialNormalReduction P α C.derivation]
    [LawfulCDifferentialNormalReduction C domain]
    [CompleteCDifferentialNormalReduction C domain] :
    RemainderIntegrationStage (NormalReductionInput P α) (IntegralResult α P) Unit
      (fun input => IsDifferentialNormalPartIntegrable C input.derivative input.numerator input.denominator)
      (fun input result _ =>
        CertifiedDifferentialNormalResult C input.derivative input.numerator input.denominator result) :=
  { stage :=
      { run := fun _ input =>
          (CDifferentialNormalReduction.reduce C.derivation input.derivative input.numerator
            input.denominator).map fun out => ⟨out, ()⟩
        domain := fun input => domain input.derivative input.numerator input.denominator
        sound := by
          intro _ input result hdomain hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact LawfulCDifferentialNormalReduction.sound input.derivative input.numerator
            input.denominator out hdomain input.denominator_nonzero hout
        complete := by
          intro input hdomain hintegrable
          obtain ⟨out, hrun, _⟩ := CompleteCDifferentialNormalReduction.relative_complete
            (C := C) (domain := domain) input.derivative input.numerator input.denominator
              hdomain input.denominator_nonzero hintegrable
          exact ⟨0, ⟨out, ()⟩, by simp [hrun]⟩ } }

/-! ### Compatibility adapter for existing normal reducers -/

variable [LawfulCPolyEngine.{u,v} P]
variable [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]

/-- The legacy normal reducer viewed as an explicit-differential operation. -/
@[reducible] noncomputable def CNormalReduction.asDifferential
    (N : CNormalReduction P α) :
    CDifferentialNormalReduction P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation where
  reduce := N.reduce

/-- The legacy and explicit logarithmic residue sums agree in the compatibility context. -/
theorem differentialLogResidueSum_ofCDiffField (Dt : P α) (logs : List (α × P α)) :
    differentialLogResidueSum (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)) Dt logs =
      logResidueSumP Dt logs := by
  change (logs.map fun cv =>
    am α (Polynomial.C (CFieldSpec.toK cv.1)) *
      (towerFractionFieldDerivP Dt (am α (CPoly.toPoly cv.2)) /
        am α (CPoly.toPoly cv.2))).sum = logResidueSumP Dt logs
  exact (logResidueSumP_eq_logDeriv_sum Dt logs).symm

/-- The legacy normal identity is the explicit identity in the compatibility context. -/
theorem isDifferentialIntegralResultP_ofCDiffField_iff (Dt a d : P α) (out : IntegralResult α P) :
    IsDifferentialIntegralResultP (MonomialDifferentialContext.ofCDiffField (P := P) (α := α))
      Dt a d out ↔ IsIntegralResultP Dt a d out := by
  rw [IsDifferentialIntegralResultP, differentialLogResidueSum_ofCDiffField]
  rfl

/-- Promote a lawful legacy normal reducer to the explicit-differential contract. -/
@[reducible] noncomputable def LawfulCDifferentialNormalReduction.ofLegacy
    (N : CNormalReduction P α) (domain : NormalReductionDomain P α)
    [LawfulCNormalReduction N domain] [LawfulGenuineCNormalReduction N domain] :
    @LawfulCDifferentialNormalReduction P _ _ α _ _
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α))
      (CNormalReduction.asDifferential N) domain := by
  letI : CDifferentialNormalReduction P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation :=
    CNormalReduction.asDifferential N
  refine ⟨?_⟩
  intro Dt a d out hdomain hd hrun
  have hlegacy := LawfulCNormalReduction.sound Dt a d out hdomain hd hrun
  refine ⟨(isDifferentialIntegralResultP_ofCDiffField_iff Dt a d out).mpr hlegacy, ?_, ?_, ?_⟩
  · exact LawfulCNormalReduction.rationalDen_nonzero Dt a d out hdomain hd hrun
  · intro cv hcv
    change @Differential.deriv _ _ CDiffFieldSpec.diffK (CFieldSpec.toK cv.1) = 0
    rw [← CDiffFieldSpec.toK_cderiv]
    exact LawfulGenuineCNormalReduction.coefficients_constant Dt a d out hdomain hd hrun cv hcv
  · exact LawfulGenuineCNormalReduction.arguments_nonzero Dt a d out hdomain hd hrun

/-- Promote a complete legacy normal reducer to the explicit-differential contract. -/
@[reducible] noncomputable def CompleteCDifferentialNormalReduction.ofLegacy
    (N : CNormalReduction P α) (domain : NormalReductionDomain P α)
    [LawfulCNormalReduction N domain] [LawfulGenuineCNormalReduction N domain]
    [CompleteCNormalReduction N domain] :
    @CompleteCDifferentialNormalReduction P _ _ α _ _
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α))
      (CNormalReduction.asDifferential N) domain
      (LawfulCDifferentialNormalReduction.ofLegacy N domain) := by
  letI : CDifferentialNormalReduction P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation :=
    CNormalReduction.asDifferential N
  letI : LawfulCDifferentialNormalReduction
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)) domain :=
    LawfulCDifferentialNormalReduction.ofLegacy N domain
  refine ⟨?_⟩
  intro Dt a d hdomain hd hintegrable
  obtain ⟨witness, hwitness⟩ := hintegrable
  have hlegacyWitness : IsNormalPartIntegrable Dt a d :=
    ⟨witness, (isDifferentialIntegralResultP_ofCDiffField_iff Dt a d witness).mp
      hwitness.integral, hwitness.rationalDen_nonzero,
      (by
        intro cv hcv
        rw [CDiffFieldSpec.toK_cderiv]
        exact hwitness.coefficients_constant cv hcv), hwitness.arguments_nonzero⟩
  obtain ⟨out, hout, hcertified⟩ := CompleteCNormalReduction.relative_complete
    (N := N) Dt a d hdomain hd hlegacyWitness
  refine ⟨out, hout, ?_⟩
  exact LawfulCDifferentialNormalReduction.ofLegacy N domain |>.sound Dt a d out hdomain hd hout

end DeepWiki.SymbolicIntegration
