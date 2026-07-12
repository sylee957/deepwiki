import DeepWiki.SymbolicIntegration.Engine.Hermite.DifferentialStage
import DeepWiki.SymbolicIntegration.Engine.PolynomialAssembly

/-! # Explicit-differential canonical decomposition

Canonical rational decomposition is selected by the same explicit coefficient differential as the
polynomial, normal, and special stages.  The resulting zero-fuel stage produces the typed branch
input consumed by the compositional one-level pipeline.
-/

namespace DeepWiki.SymbolicIntegration

universe u v

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]

/-- Prop-free canonical decomposition selected for one explicit coefficient derivation. -/
class CDifferentialCanonicalRepresentation
    (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] (derivation : CFieldDerivation α) where
  /-- Decompose a represented fraction into polynomial, special, and normal branches. -/
  compute : P α → P α → P α → CanonicalRepresentationResult P α

/-- Denotational laws for an explicit-differential canonical decomposition. -/
class LawfulCDifferentialCanonicalRepresentation
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialCanonicalRepresentation P α C.derivation] : Prop where
  /-- The three selected branches reconstruct the original fraction. -/
  reconstruction : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    let out := CDifferentialCanonicalRepresentation.compute C.derivation Dt a d
    fieldFracP out.polynomial CPoly.one + fieldFracP out.specialNum out.specialDen +
        fieldFracP out.normalNum out.normalDen = fieldFracP a d
  /-- A nonzero input denominator produces a nonzero special denominator. -/
  specialDen_nonzero : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    CPoly.toPoly (CDifferentialCanonicalRepresentation.compute C.derivation Dt a d).specialDen ≠ 0
  /-- A nonzero input denominator produces a nonzero normal denominator. -/
  normalDen_nonzero : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    CPoly.toPoly (CDifferentialCanonicalRepresentation.compute C.derivation Dt a d).normalDen ≠ 0

/-- The canonical split selected by an explicit coefficient differential. -/
abbrev differentialCanonicalResult
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialCanonicalRepresentation P α C.derivation] (Dt a d : P α) :
    CanonicalRepresentationResult P α :=
  CDifferentialCanonicalRepresentation.compute C.derivation Dt a d

/-- Build the typed one-level branch input selected by explicit canonical decomposition. -/
noncomputable def differentialCanonicalOneLevelBranch
    (C : MonomialDifferentialContext (P := P) α) (kind : PolynomialReductionKind)
    [CDifferentialCanonicalRepresentation P α C.derivation]
    [LawfulCDifferentialCanonicalRepresentation C]
    (input : OneLevelInput P α) : OneLevelBranchInput P α :=
  let split := differentialCanonicalResult C input.derivative input.numerator input.denominator
  ⟨input.numerator, input.denominator, input.denominator_nonzero, kind, input.derivative,
    split.polynomial, split.specialNum, split.specialDen, split.normalNum, split.normalDen,
    LawfulCDifferentialCanonicalRepresentation.specialDen_nonzero input.derivative input.numerator
      input.denominator input.denominator_nonzero,
    LawfulCDifferentialCanonicalRepresentation.normalDen_nonzero input.derivative input.numerator
      input.denominator input.denominator_nonzero⟩

/-- Explicit canonical decomposition is a certified zero-fuel remainder stage. -/
noncomputable def differentialCanonicalOneLevelRemainderStage
    (C : MonomialDifferentialContext (P := P) α) (kind : PolynomialReductionKind)
    [CDifferentialCanonicalRepresentation P α C.derivation]
    [LawfulCDifferentialCanonicalRepresentation C] :
    RemainderIntegrationStage (OneLevelInput P α) Unit (OneLevelBranchInput P α)
      (fun _ => True)
      (fun input output branch =>
        output = () ∧ branch = differentialCanonicalOneLevelBranch C kind input) :=
  { stage :=
      { run := fun _ input => some ⟨(), differentialCanonicalOneLevelBranch C kind input⟩
        domain := fun _ => True
        sound := by
          intro _ _ result _ hrun
          simp only [Option.some.injEq] at hrun
          subst result
          exact ⟨rfl, rfl⟩
        complete := by
          intro input _ _
          exact ⟨0, ⟨(), differentialCanonicalOneLevelBranch C kind input⟩, rfl⟩ } }

/-! ### Compatibility adapter for legacy canonical decompositions -/

variable [LawfulCPolyEngine.{u,v} P]
variable [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]

/-- The legacy canonical decomposition viewed as an explicit-differential operation. -/
@[reducible] noncomputable def CCanonicalRepresentation.asDifferential
    [CCanonicalRepresentation P α] :
    CDifferentialCanonicalRepresentation P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation where
  compute := CCanonicalRepresentation.compute

/-- Promote a lawful legacy canonical decomposition to the explicit-differential contract. -/
@[reducible] noncomputable def LawfulCDifferentialCanonicalRepresentation.ofLegacy
    [CCanonicalRepresentation P α] [LawfulCCanonicalRepresentation (P := P) (α := α)] :
    @LawfulCDifferentialCanonicalRepresentation P _ _ α _ _
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α))
      (CCanonicalRepresentation.asDifferential (P := P) (α := α)) := by
  letI : CDifferentialCanonicalRepresentation P α
      (MonomialDifferentialContext.ofCDiffField (P := P) (α := α)).derivation :=
    CCanonicalRepresentation.asDifferential (P := P) (α := α)
  refine ⟨?_, ?_, ?_⟩
  · intro Dt a d hd
    exact LawfulCCanonicalRepresentation.reconstruction Dt a d hd
  · intro Dt a d hd
    exact LawfulCCanonicalRepresentation.specialDen_nonzero Dt a d hd
  · intro Dt a d hd
    exact LawfulCCanonicalRepresentation.normalDen_nonzero Dt a d hd

end DeepWiki.SymbolicIntegration
