import DeepWiki.SymbolicIntegration.Engine.MonomialDifferentialPostprocess
import DeepWiki.SymbolicIntegration.Engine.PolynomialAssembly
import DeepWiki.SymbolicIntegration.Engine.Tower.PolyPartDynamic

/-! # Explicit-differential one-level branch assembly

The polynomial-reduction and monomial-special branches compose through a typed remainder handoff.
This is the dynamic counterpart of the legacy one-level branch: all derivative-sensitive contracts
refer to one selected `MonomialDifferentialContext`.
-/

namespace DeepWiki.SymbolicIntegration

open DynamicPolynomialReduction

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {α : Type u} [CField α] [CFieldSpec.{u,u} α]

/-- The polynomial-reduction input induced by a one-level polynomial-special input. -/
def PolynomialSpecialInput.toDifferentialPolynomialReductionInput
    (input : PolynomialSpecialInput P α) : PolynomialReductionInput P α :=
  ⟨input.kind, input.derivative, input.polynomial⟩

/-- The special-solver input induced by an explicit polynomial-reduction remainder. -/
def PolynomialSpecialInput.toDifferentialMonomialSpecialInput
    (input : PolynomialSpecialInput P α) (remainder : P α) : MonomialSpecialInput P α :=
  ⟨input.derivative, remainder, input.specialNum, input.specialDen, input.specialDen_nonzero⟩

/-- The typed handoff from explicit polynomial reduction to explicit special integration. -/
def IsDifferentialPolynomialSpecialHandoff
    (C : MonomialDifferentialContext (P := P) α) (input : PolynomialSpecialInput P α)
    (antiderivative : P α) (next : MonomialSpecialInput P α) : Prop :=
  IsDifferentialPolynomialReduction (P := P) (α := α) C.differential
    input.kind input.derivative input.polynomial
      ⟨antiderivative, next.polynomial⟩ ∧
    next.derivative = input.derivative ∧ next.specialNum = input.specialNum ∧
      next.specialDen = input.specialDen

/-- The semantic contract of the composed explicit polynomial-special branch. -/
def IsDifferentialPolynomialSpecialAssembly
    (C : MonomialDifferentialContext (P := P) α) (input : PolynomialSpecialInput P α)
    (antiderivative : P α) (special : IntegralResult α P) : Prop :=
  ∃ remainder,
    IsDifferentialPolynomialReduction (P := P) (α := α) C.differential
      input.kind input.derivative input.polynomial
      ⟨antiderivative, remainder⟩ ∧
    IsDifferentialMonomialSpecialResult C input.derivative remainder input.specialNum input.specialDen
      special

/-- Domain for the typed explicit polynomial-to-special handoff. -/
def DifferentialPolynomialSpecialDomain
    (C : MonomialDifferentialContext (P := P) α)
    (polynomialDomain : DifferentialPolynomialReductionDomain P α)
    (specialDomain : MonomialSpecialDomain P α) (input : PolynomialSpecialInput P α) : Prop :=
  polynomialDomain input.kind input.derivative input.polynomial ∧
    ∀ antiderivative next,
      IsDifferentialPolynomialSpecialHandoff C input antiderivative next →
        specialDomain next.derivative next.polynomial next.specialNum next.specialDen

/-- Export explicit polynomial reduction as the typed handoff to special integration. -/
noncomputable def PolynomialSpecialInput.asDifferentialHandoffStage
    (C : MonomialDifferentialContext (P := P) α)
    (R : CDifferentialPolynomialReduction P α C.derivation)
    (polynomialDomain : DifferentialPolynomialReductionDomain P α)
    [LawfulCDifferentialPolynomialReduction (P := P) C.derivation C.differential R]
    [CompleteCDifferentialPolynomialReduction (P := P) C.derivation C.differential R polynomialDomain] :
    RemainderIntegrationStage (PolynomialSpecialInput P α) (P α) (MonomialSpecialInput P α)
      (fun input => ∃ out,
        IsDifferentialPolynomialReduction (P := P) (α := α) C.differential
          input.kind input.derivative input.polynomial out)
      (IsDifferentialPolynomialSpecialHandoff C) :=
  { stage :=
      { run := fun fuel input =>
          (R.reduce input.kind input.derivative fuel input.polynomial).map fun out =>
            ⟨out.antiderivative, input.toDifferentialMonomialSpecialInput out.remainder⟩
        domain := fun input => polynomialDomain input.kind input.derivative input.polynomial
        sound := by
          intro fuel input result hdomain hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact ⟨LawfulCDifferentialPolynomialReduction.sound input.kind input.derivative fuel
            input.polynomial out hout, rfl, rfl, rfl⟩
        complete := by
          intro input hdomain hintegrable
          obtain ⟨fuel, out, hout, _⟩ := CompleteCDifferentialPolynomialReduction.relative_complete
            (C := R) (domain := polynomialDomain) input.kind input.derivative input.polynomial
              hdomain hintegrable
          exact ⟨fuel, ⟨out.antiderivative, input.toDifferentialMonomialSpecialInput out.remainder⟩,
            by simp [hout]⟩ } }

/-- Compose explicit polynomial reduction and explicit special integration. -/
noncomputable def CDifferentialPolynomialReduction.asPolynomialSpecialRemainderStage
    (C : MonomialDifferentialContext (P := P) α)
    (R : CDifferentialPolynomialReduction P α C.derivation)
    (polynomialDomain : DifferentialPolynomialReductionDomain P α)
    [LawfulCDifferentialPolynomialReduction (P := P) C.derivation C.differential R]
    [CompleteCDifferentialPolynomialReduction (P := P) C.derivation C.differential R polynomialDomain]
    (specialDomain : MonomialSpecialDomain P α)
    [CDifferentialMonomialSpecial P α C.derivation]
    [LawfulCDifferentialMonomialSpecial C]
    [CompleteCDifferentialMonomialSpecial C specialDomain] :
    RemainderIntegrationStage (PolynomialSpecialInput P α) (P α × IntegralResult α P) Unit
      (fun input =>
        (∃ out, IsDifferentialPolynomialReduction (P := P) (α := α) C.differential input.kind input.derivative
          input.polynomial out) ∧
        ∀ antiderivative next, IsDifferentialPolynomialSpecialHandoff C input antiderivative next →
          ∃ result, IsDifferentialMonomialSpecialResult C next.derivative next.polynomial
            next.specialNum next.specialDen result)
      (fun input output _ =>
        IsDifferentialPolynomialSpecialAssembly C input output.1 output.2) := by
  let handoff := PolynomialSpecialInput.asDifferentialHandoffStage C R polynomialDomain
  let special := CDifferentialMonomialSpecial.asRemainderIntegrationStage C specialDomain
  exact handoff.compose special
    (DifferentialPolynomialSpecialDomain C polynomialDomain specialDomain)
    (fun input =>
      (∃ out, IsDifferentialPolynomialReduction (P := P) (α := α) C.differential input.kind input.derivative
        input.polynomial out) ∧
      ∀ antiderivative next, IsDifferentialPolynomialSpecialHandoff C input antiderivative next →
        ∃ result, IsDifferentialMonomialSpecialResult C next.derivative next.polynomial
          next.specialNum next.specialDen result)
    (by
      intro input hdomain
      exact hdomain.1)
    (by
      intro input _ next hdomain hhandoff
      exact hdomain.2 _ _ hhandoff)
    (by
      intro input hintegrable
      exact hintegrable)
    (by
      intro input antiderivative next specialResult _ hhandoff hspecial
      refine ⟨next.polynomial, hhandoff.1, ?_⟩
      simpa [hhandoff.2.1, hhandoff.2.2.1, hhandoff.2.2.2] using hspecial)

/-- Reindex the explicit polynomial-special branch to a complete one-level split. -/
noncomputable def CDifferentialPolynomialReduction.asOneLevelBranchStage
    (C : MonomialDifferentialContext (P := P) α)
    (R : CDifferentialPolynomialReduction P α C.derivation)
    (polynomialDomain : DifferentialPolynomialReductionDomain P α)
    [LawfulCDifferentialPolynomialReduction (P := P) C.derivation C.differential R]
    [CompleteCDifferentialPolynomialReduction (P := P) C.derivation C.differential R polynomialDomain]
    (specialDomain : MonomialSpecialDomain P α)
    [CDifferentialMonomialSpecial P α C.derivation]
    [LawfulCDifferentialMonomialSpecial C]
    [CompleteCDifferentialMonomialSpecial C specialDomain] :
    RemainderIntegrationStage (OneLevelBranchInput P α) (P α × IntegralResult α P) Unit
      (fun input =>
        (∃ out, IsDifferentialPolynomialReduction (P := P) (α := α) C.differential
          input.kind input.derivative input.polynomial out) ∧
        ∀ antiderivative next,
          IsDifferentialPolynomialSpecialHandoff C input.toPolynomialSpecialInput antiderivative next →
            ∃ result, IsDifferentialMonomialSpecialResult C next.derivative next.polynomial
              next.specialNum next.specialDen result)
      (fun input output _ =>
        IsDifferentialPolynomialSpecialAssembly C input.toPolynomialSpecialInput output.1 output.2) :=
  (CDifferentialPolynomialReduction.asPolynomialSpecialRemainderStage C R polynomialDomain
    specialDomain).precompose
    OneLevelBranchInput.toPolynomialSpecialInput

/-- Reindex the explicit normal branch to a complete one-level split. -/
noncomputable def CDifferentialNormalReduction.asOneLevelBranchStage
    (C : MonomialDifferentialContext (P := P) α)
    (normalDomain : DifferentialNormalReductionDomain P α)
    [CDifferentialNormalReduction P α C.derivation]
    [LawfulCDifferentialNormalReduction C normalDomain]
    [CompleteCDifferentialNormalReduction C normalDomain]
    [CDifferentialNormalPostprocessor P α C.derivation]
    [LawfulCDifferentialNormalPostprocessor C]
    [CompleteCDifferentialNormalPostprocessor C] :
    RemainderIntegrationStage (OneLevelBranchInput P α) (IntegralResult α P) Unit
      (fun input => IsDifferentialNormalPartIntegrable C input.derivative input.normalNum input.normalDen)
      (fun input result _ =>
        CertifiedDifferentialNormalResult C input.derivative input.normalNum input.normalDen result) :=
  (CDifferentialNormalReduction.asPostprocessedRemainderStage C normalDomain).precompose
    OneLevelBranchInput.toNormalReductionInput

/-- Run the explicit polynomial-special and postprocessed-normal branches independently. -/
noncomputable def CDifferentialPolynomialReduction.asParallelOneLevelBranchStage
    (C : MonomialDifferentialContext (P := P) α)
    (R : CDifferentialPolynomialReduction P α C.derivation)
    (polynomialDomain : DifferentialPolynomialReductionDomain P α)
    [LawfulCDifferentialPolynomialReduction (P := P) C.derivation C.differential R]
    [CompleteCDifferentialPolynomialReduction (P := P) C.derivation C.differential R polynomialDomain]
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
    [CompleteCDifferentialNormalPostprocessor C] :
    RemainderIntegrationStage (OneLevelBranchInput P α)
      ((P α × IntegralResult α P) × IntegralResult α P) (Unit × Unit)
      (fun input =>
        ((∃ out, IsDifferentialPolynomialReduction (P := P) (α := α) C.differential
          input.kind input.derivative input.polynomial out) ∧
          ∀ antiderivative next,
            IsDifferentialPolynomialSpecialHandoff C input.toPolynomialSpecialInput antiderivative next →
              ∃ result, IsDifferentialMonomialSpecialResult C next.derivative next.polynomial
                next.specialNum next.specialDen result) ∧
          IsDifferentialNormalPartIntegrable C input.derivative input.normalNum input.normalDen)
      (fun input output _ =>
        IsDifferentialPolynomialSpecialAssembly C input.toPolynomialSpecialInput output.1.1 output.1.2 ∧
          CertifiedDifferentialNormalResult C input.derivative input.normalNum input.normalDen output.2) := by
  let special := CDifferentialPolynomialReduction.asOneLevelBranchStage C R polynomialDomain specialDomain
  let normal := CDifferentialNormalReduction.asOneLevelBranchStage C normalDomain
  exact special.product normal

end DeepWiki.SymbolicIntegration
