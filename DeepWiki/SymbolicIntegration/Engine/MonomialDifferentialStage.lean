import DeepWiki.SymbolicIntegration.Engine.Assemble
import DeepWiki.SymbolicIntegration.Engine.Hermite.DifferentialNormal

/-! # Explicit-differential monomial-special stages

The polynomial/special branch is selected by an explicit coefficient differential.  Legacy
primitive, hyperexponential, and tangent solvers are certified adapters when that differential is
the legacy one, while mixed towers can supply their own selected operation and laws.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CFrac

universe u v

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]

/-- A special-branch result certified for an explicitly selected monomial differential. -/
def IsDifferentialMonomialSpecialResult
    (C : MonomialDifferentialContext (P := P) α) (Dt fp b ds : P α)
    (res : IntegralResult α P) : Prop :=
  CPoly.toPoly res.rational.2 ≠ 0 ∧
    (∀ cv ∈ res.logs,
      @Differential.deriv _ _ C.differential (CFieldSpec.toK cv.1) = 0) ∧
    (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0) ∧
    C.fractionDeriv Dt (fieldFracP res.rational.1 res.rational.2) +
        differentialLogResidueSum C Dt res.logs =
      fieldFracP fp CPoly.one + fieldFracP b ds

/-- Prop-free special integrator selected for one explicit coefficient derivation. -/
class CDifferentialMonomialSpecial (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] (derivation : CFieldDerivation α) where
  /-- Attempt to integrate the polynomial and special-denominator contribution. -/
  integrate : ℕ → P α → P α → P α → P α → Option (IntegralResult α P)

/-- Soundness and genuine-log laws for an explicit-differential special integrator. -/
class LawfulCDifferentialMonomialSpecial
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialMonomialSpecial P α C.derivation] : Prop where
  /-- Every accepted special result satisfies the explicit identity and genuine-log conditions. -/
  sound : ∀ (fuel : ℕ) (Dt fp b ds : P α) (res : IntegralResult α P),
    CDifferentialMonomialSpecial.integrate C.derivation fuel Dt fp b ds = some res →
      IsDifferentialMonomialSpecialResult C Dt fp b ds res

/-- Relative-completeness law for an explicit-differential special integrator. -/
class CompleteCDifferentialMonomialSpecial
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialMonomialSpecial P α C.derivation]
    (domain : MonomialSpecialDomain P α)
    [LawfulCDifferentialMonomialSpecial C] : Prop where
  /-- Every in-domain special input with an explicit certificate is eventually accepted. -/
  complete : ∀ (Dt fp b ds : P α), domain Dt fp b ds →
    (∃ res, IsDifferentialMonomialSpecialResult C Dt fp b ds res) →
      ∃ fuel out, CDifferentialMonomialSpecial.integrate C.derivation fuel Dt fp b ds = some out

/-- Export an explicit special integrator through the common output-remainder stage contract. -/
noncomputable def CDifferentialMonomialSpecial.asRemainderIntegrationStage
    (C : MonomialDifferentialContext (P := P) α)
    (domain : MonomialSpecialDomain P α)
    [CDifferentialMonomialSpecial P α C.derivation]
    [LawfulCDifferentialMonomialSpecial C]
    [CompleteCDifferentialMonomialSpecial C domain] :
    RemainderIntegrationStage (MonomialSpecialInput P α) (IntegralResult α P) Unit
      (fun input => ∃ result, IsDifferentialMonomialSpecialResult C input.derivative input.polynomial
        input.specialNum input.specialDen result)
      (fun input result _ => IsDifferentialMonomialSpecialResult C input.derivative input.polynomial
        input.specialNum input.specialDen result) :=
  { stage :=
      { run := fun fuel input =>
          (CDifferentialMonomialSpecial.integrate C.derivation fuel input.derivative input.polynomial
            input.specialNum input.specialDen).map fun out => ⟨out, ()⟩
        domain := fun input => domain input.derivative input.polynomial input.specialNum input.specialDen
        sound := by
          intro fuel input result _ hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact LawfulCDifferentialMonomialSpecial.sound fuel input.derivative input.polynomial
            input.specialNum input.specialDen out hout
        complete := by
          intro input hdomain hintegrable
          obtain ⟨fuel, out, hrun⟩ := CompleteCDifferentialMonomialSpecial.complete
            (C := C) (domain := domain) input.derivative input.polynomial input.specialNum
              input.specialDen hdomain hintegrable
          exact ⟨fuel, ⟨out, ()⟩, by simp [hrun]⟩ } }

/-! ### Compatibility adapter for existing special solvers -/

variable [LawfulCPolyEngine.{u,v} P]
variable [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]

/-- The legacy monomial special solver viewed as an explicit-differential operation. -/
@[reducible] noncomputable def CMonomialCase.asDifferentialSpecial
    (M : CMonomialCase P α) :
    CDifferentialMonomialSpecial P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation where
  integrate := M.integrateSpecial

/-- The legacy and explicit special identities agree in the compatibility context. -/
theorem differentialMonomialSpecialIdentity_ofCDiffField_iff
    (Dt fp b ds : P α) (res : IntegralResult α P) :
    (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).fractionDeriv Dt
        (fieldFracP res.rational.1 res.rational.2) +
      differentialLogResidueSum
        (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)) Dt res.logs =
        fieldFracP fp CPoly.one + fieldFracP b ds ↔
    towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2) +
      logResidueSumP Dt res.logs = fieldFracP fp CPoly.one + fieldFracP b ds := by
  rw [differentialLogResidueSum_ofCDiffField]
  rfl

/-- Promote a lawful genuine legacy special solver to the explicit-differential contract. -/
@[reducible] noncomputable def LawfulCDifferentialMonomialSpecial.ofLegacy
    (M : CMonomialCase P α) [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M] :
    @LawfulCDifferentialMonomialSpecial P _ _ α _ _
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α))
      (CMonomialCase.asDifferentialSpecial M) := by
  letI : CDifferentialMonomialSpecial P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation :=
    CMonomialCase.asDifferentialSpecial M
  refine ⟨?_⟩
  intro fuel Dt fp b ds res hrun
  obtain ⟨hden, hidentity⟩ := LawfulCMonomialCase.special_sound fuel Dt fp b ds res hrun
  refine ⟨hden, ?_, LawfulGenuineCMonomialCase.special_arguments_nonzero fuel Dt fp b ds res hrun,
    (differentialMonomialSpecialIdentity_ofCDiffField_iff Dt fp b ds res).mpr hidentity⟩
  intro cv hcv
  change @Differential.deriv _ _ CDiffFieldSpec.diffK (CFieldSpec.toK cv.1) = 0
  rw [← CDiffFieldSpec.toK_cderiv]
  exact LawfulGenuineCMonomialCase.special_coefficients_constant fuel Dt fp b ds res hrun cv hcv

/-- Promote a complete legacy special solver to the explicit-differential contract. -/
@[reducible] noncomputable def CompleteCDifferentialMonomialSpecial.ofLegacy
    (M : CMonomialCase P α) (domain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M]
    [CompleteCMonomialCase M domain] :
    @CompleteCDifferentialMonomialSpecial P _ _ α _ _
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α))
      (CMonomialCase.asDifferentialSpecial M) domain
      (LawfulCDifferentialMonomialSpecial.ofLegacy M) := by
  letI : CDifferentialMonomialSpecial P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation :=
    CMonomialCase.asDifferentialSpecial M
  letI : LawfulCDifferentialMonomialSpecial
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)) :=
    LawfulCDifferentialMonomialSpecial.ofLegacy M
  refine ⟨?_⟩
  intro Dt fp b ds hdomain hintegrable
  obtain ⟨result, hden, _hconstants, _harguments, hidentity⟩ := hintegrable
  obtain ⟨fuel, out, hrun⟩ := CompleteCMonomialCase.special_complete (C := M)
    Dt fp b ds result hdomain hden
      ((differentialMonomialSpecialIdentity_ofCDiffField_iff Dt fp b ds result).mp hidentity)
  exact ⟨fuel, out, hrun⟩

end DeepWiki.SymbolicIntegration
