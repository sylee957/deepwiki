import DeepWiki.SymbolicIntegration.Engine.DifferentialReconstruction
import DeepWiki.SymbolicIntegration.Engine.Tower.Compositional

/-! # Explicit-differential compositional one-level integration

The explicit canonical split, dynamic polynomial-special branch, and dynamic normal branch are
recombined into one certified integration stage.  Its invariant carries both the selected
differential identity and genuine logarithmic reconstruction data.
-/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial DynamicPolynomialReduction

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,u} α]

/-- The full explicit-differential one-level output certificate. -/
def IsGenuineDifferentialOneLevelResult
    (C : MonomialDifferentialContext (P := P) α) (input : OneLevelInput P α)
    (result : IntegralResult α P) : Prop :=
  IsDifferentialIntegralResultP C input.derivative input.numerator input.denominator result ∧
    (∀ cv ∈ result.logs,
      @Differential.deriv _ _ C.differential (CFieldSpec.toK cv.1) = 0) ∧
      ∀ cv ∈ result.logs, CPoly.toPoly cv.2 ≠ 0

/-- Relative integrability selected for a full explicit one-level input. -/
def IsDifferentialOneLevelIntegrable
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialCanonicalRepresentation P α C.derivation]
    [LawfulCDifferentialCanonicalRepresentation C]
    (kind : PolynomialReductionKind)
    (input : OneLevelInput P α) : Prop :=
  ((∃ out, IsDifferentialPolynomialReduction C.differential
      (differentialCanonicalOneLevelBranch C kind input).kind input.derivative
      (differentialCanonicalOneLevelBranch C kind input).polynomial out) ∧
    ∀ antiderivative next,
      IsDifferentialPolynomialSpecialHandoff C
        (differentialCanonicalOneLevelBranch C kind input).toPolynomialSpecialInput
          antiderivative next →
        ∃ result, IsDifferentialMonomialSpecialResult C next.derivative next.polynomial
          next.specialNum next.specialDen result) ∧
    IsDifferentialNormalPartIntegrable C input.derivative
      (differentialCanonicalOneLevelBranch C kind input).normalNum
      (differentialCanonicalOneLevelBranch C kind input).normalDen

omit [LawfulCPolyEngine P] in
/-- Explicit canonical decomposition reconstructs the original fraction. -/
theorem differentialCanonicalOneLevelBranch_reconstruction
    (C : MonomialDifferentialContext (P := P) α) (kind : PolynomialReductionKind)
    [CDifferentialCanonicalRepresentation P α C.derivation]
    [LawfulCDifferentialCanonicalRepresentation C]
    (input : OneLevelInput P α) :
    fieldFracP (differentialCanonicalOneLevelBranch C kind input).polynomial CPoly.one +
        fieldFracP (differentialCanonicalOneLevelBranch C kind input).specialNum
          (differentialCanonicalOneLevelBranch C kind input).specialDen +
        fieldFracP (differentialCanonicalOneLevelBranch C kind input).normalNum
          (differentialCanonicalOneLevelBranch C kind input).normalDen =
      fieldFracP input.numerator input.denominator := by
  exact LawfulCDifferentialCanonicalRepresentation.reconstruction input.derivative input.numerator
    input.denominator input.denominator_nonzero

/-- Dynamic polynomial-special and normal branch certificates reconstruct the selected differential identity. -/
theorem differentialOneLevelBranchAssembly_sound
    (C : MonomialDifferentialContext (P := P) α) (input : OneLevelBranchInput P α)
    (branches : (P α × IntegralResult α P) × IntegralResult α P)
    (hreconstruct :
      fieldFracP input.polynomial CPoly.one + fieldFracP input.specialNum input.specialDen +
          fieldFracP input.normalNum input.normalDen = fieldFracP input.numerator input.denominator)
    (hbranches :
      IsDifferentialPolynomialSpecialAssembly C input.toPolynomialSpecialInput branches.1.1 branches.1.2 ∧
        CertifiedDifferentialNormalResult C input.derivative input.normalNum input.normalDen branches.2) :
    IsDifferentialIntegralResultP C input.derivative input.numerator input.denominator
      (reconstructOneLevelBranches branches) := by
  obtain ⟨remainder, hreduce, hspecial⟩ := hbranches.1
  obtain ⟨hspecialDen, _hspecialConstants, _hspecialArguments, hspecialIdentity⟩ := hspecial
  have hpoly : C.fractionDeriv input.derivative (fieldFracP branches.1.1 CPoly.one) =
      fieldFracP input.polynomial CPoly.one - fieldFracP remainder CPoly.one :=
    differentialPolynomialReduction_antiderivative_sound C input.kind input.derivative input.polynomial
      branches.1.1 remainder hreduce
  have hone : CPoly.toPoly (CPoly.one : P α) ≠ 0 := by
    rw [CPoly.toPoly_one]
    exact one_ne_zero
  have hpolynomialSpecial : C.fractionDeriv input.derivative
      (fieldFracP (combineSN branches.1.1 CPoly.one branches.1.2).rational.1
        (combineSN branches.1.1 CPoly.one branches.1.2).rational.2) +
      differentialLogResidueSum C input.derivative (combineSN branches.1.1 CPoly.one branches.1.2).logs =
      fieldFracP input.polynomial CPoly.one + fieldFracP input.specialNum input.specialDen := by
    rw [differentialCombineSN_value C input.derivative branches.1.1 CPoly.one branches.1.2
      (fieldFracP input.polynomial CPoly.one - fieldFracP remainder CPoly.one)
      (fieldFracP remainder CPoly.one + fieldFracP input.specialNum input.specialDen)
      hone hspecialDen hpoly hspecialIdentity]
    ring
  have hleftDen : CPoly.toPoly (combineSN branches.1.1 CPoly.one branches.1.2).rational.2 ≠ 0 := by
    simp only [combineSN, combineRationalParts, LawfulCPolyEngine.toPoly_mul, CPoly.toPoly_one]
    exact mul_ne_zero one_ne_zero hspecialDen
  refine differentialCombineIntegralResults C input.derivative input.numerator input.denominator
    input.normalNum input.normalDen (combineSN branches.1.1 CPoly.one branches.1.2) branches.2
    (fieldFracP input.polynomial CPoly.one + fieldFracP input.specialNum input.specialDen)
    hleftDen hbranches.2.rationalDen_nonzero hpolynomialSpecial hbranches.2.integral ?_
  simpa only [add_assoc] using hreconstruct

omit [LawfulCPolyEngine P] in
/-- Genuine logarithmic coefficients and arguments survive explicit one-level reconstruction. -/
theorem differentialOneLevelBranchAssembly_logs_genuine
    (C : MonomialDifferentialContext (P := P) α) (input : OneLevelBranchInput P α)
    (branches : (P α × IntegralResult α P) × IntegralResult α P)
    (hbranches :
      IsDifferentialPolynomialSpecialAssembly C input.toPolynomialSpecialInput branches.1.1 branches.1.2 ∧
        CertifiedDifferentialNormalResult C input.derivative input.normalNum input.normalDen branches.2) :
    (∀ cv ∈ (reconstructOneLevelBranches branches).logs,
      @Differential.deriv _ _ C.differential (CFieldSpec.toK cv.1) = 0) ∧
      ∀ cv ∈ (reconstructOneLevelBranches branches).logs, CPoly.toPoly cv.2 ≠ 0 := by
  obtain ⟨_remainder, _hreduce, hspecial⟩ := hbranches.1
  obtain ⟨_hspecialDen, hspecialConstants, hspecialArguments, _hspecialIdentity⟩ := hspecial
  constructor
  · intro cv hcv
    change cv ∈ branches.1.2.logs ++ branches.2.logs at hcv
    rw [List.mem_append] at hcv
    exact hcv.elim (hspecialConstants cv) (hbranches.2.coefficients_constant cv)
  · intro cv hcv
    change cv ∈ branches.1.2.logs ++ branches.2.logs at hcv
    rw [List.mem_append] at hcv
    exact hcv.elim (hspecialArguments cv) (hbranches.2.arguments_nonzero cv)

/-- The complete explicit-differential one-level pipeline as one common remainder stage. -/
noncomputable def DynamicPolynomialReduction.CDifferentialPolynomialReduction.asOneLevelRemainderStage
    (C : MonomialDifferentialContext (P := P) α)
    (canonical : CDifferentialCanonicalRepresentation P α C.derivation)
    (kind : PolynomialReductionKind)
    (R : CDifferentialPolynomialReduction P α C.derivation)
    (polynomialDomain : DifferentialPolynomialReductionDomain P α)
    [LawfulCDifferentialPolynomialReduction C.derivation C.differential R]
    [CompleteCDifferentialPolynomialReduction C.derivation C.differential R polynomialDomain]
    (specialDomain : MonomialSpecialDomain P α)
    [CDifferentialMonomialSpecial P α C.derivation]
    [LawfulCDifferentialMonomialSpecial C]
    [CompleteCDifferentialMonomialSpecial C specialDomain]
    (normalDomain : DifferentialNormalReductionDomain P α)
    [CDifferentialNormalReduction P α C.derivation]
    [LawfulCDifferentialNormalReduction C normalDomain]
    [CompleteCDifferentialNormalReduction C normalDomain]
    [CDifferentialNormalPostprocessor P α C.derivation]
    [LawfulCDifferentialNormalPostprocessor C]
    [CompleteCDifferentialNormalPostprocessor C]
    [LawfulCDifferentialCanonicalRepresentation C] :
    RemainderIntegrationStage (OneLevelInput P α) (IntegralResult α P) (Unit × Unit)
      (IsDifferentialOneLevelIntegrable C kind)
      (fun input result _ => IsGenuineDifferentialOneLevelResult C input result) := by
  letI : CDifferentialCanonicalRepresentation P α C.derivation := canonical
  let branches := R.asCanonicalOneLevelBranchStage C canonical kind polynomialDomain specialDomain normalDomain
  exact branches.mapOutput reconstructOneLevelBranches (by
    intro input output _ hcorrect
    refine ⟨differentialOneLevelBranchAssembly_sound C
      (differentialCanonicalOneLevelBranch C kind input) output
      (differentialCanonicalOneLevelBranch_reconstruction C kind input) hcorrect,
      differentialOneLevelBranchAssembly_logs_genuine C
        (differentialCanonicalOneLevelBranch C kind input) output hcorrect⟩)

/-- Export the full explicit one-level pipeline at the proof-carrying tower input boundary. -/
noncomputable def DynamicPolynomialReduction.CDifferentialPolynomialReduction.asRischStageRemainderStage
    (C : MonomialDifferentialContext (P := P) α)
    (canonical : CDifferentialCanonicalRepresentation P α C.derivation)
    (kind : PolynomialReductionKind)
    (R : CDifferentialPolynomialReduction P α C.derivation)
    (polynomialDomain : DifferentialPolynomialReductionDomain P α)
    [LawfulCDifferentialPolynomialReduction C.derivation C.differential R]
    [CompleteCDifferentialPolynomialReduction C.derivation C.differential R polynomialDomain]
    (specialDomain : MonomialSpecialDomain P α)
    [CDifferentialMonomialSpecial P α C.derivation]
    [LawfulCDifferentialMonomialSpecial C]
    [CompleteCDifferentialMonomialSpecial C specialDomain]
    (normalDomain : DifferentialNormalReductionDomain P α)
    [CDifferentialNormalReduction P α C.derivation]
    [LawfulCDifferentialNormalReduction C normalDomain]
    [CompleteCDifferentialNormalReduction C normalDomain]
    [CDifferentialNormalPostprocessor P α C.derivation]
    [LawfulCDifferentialNormalPostprocessor C]
    [CompleteCDifferentialNormalPostprocessor C]
    [LawfulCDifferentialCanonicalRepresentation C] :
    RemainderIntegrationStage (RischStageInput P α) (IntegralResult α P) (Unit × Unit)
      (fun input => IsDifferentialOneLevelIntegrable C kind input.toOneLevelInput)
      (fun input result _ => IsGenuineDifferentialOneLevelResult C input.toOneLevelInput result) :=
  (R.asOneLevelRemainderStage C canonical kind polynomialDomain specialDomain normalDomain).precompose
    RischStageInput.toOneLevelInput

end DeepWiki.SymbolicIntegration
