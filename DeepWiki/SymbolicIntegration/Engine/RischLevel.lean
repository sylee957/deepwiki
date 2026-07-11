import DeepWiki.SymbolicIntegration.Engine.PolynomialAssembly

/-! # Compositional Risch-level interface

`CRischLevel` is the representation-neutral public boundary for one step of a transcendental
Risch tower.  Its lawful contract separates an executable level solver from the semantic
soundness and relative-completeness statements that a concrete monomial realization must prove. -/

namespace DeepWiki.SymbolicIntegration

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec.{u,u} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Prop-free executable solver for one represented transcendental Risch level. -/
structure CRischLevel (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate `a/d` with the supplied search budget, or report that this level cannot do so. -/
  integrate : ℕ → P α → P α → P α → Option (IntegralResult α P)

/-- Semantic domain predicate for a represented one-level Risch solver. -/
abbrev RischLevelDomain (P : Type u → Type u) (α : Type u) := P α → P α → P α → Prop

/-- Genuine Liouville-form integrability at one represented Risch level. -/
def IsRischLevelIntegrable (Dt a d : P α) : Prop :=
  ∃ res : IntegralResult α P, IsIntegralResultP Dt a d res ∧
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
    (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0)

/-- Denotation-level soundness contract for a one-level Risch solver. -/
class LawfulCRischLevel (L : CRischLevel P α) (domain : RischLevelDomain P α) : Prop where
  /-- Every successful level solve is an integral-result certificate for its input. -/
  sound : ∀ (fuel : ℕ) (Dt a d : P α) (res : IntegralResult α P),
    domain Dt a d → CPoly.toPoly d ≠ 0 → L.integrate fuel Dt a d = some res →
      IsIntegralResultP Dt a d res

/-- Relative-completeness contract for a lawful one-level Risch solver. -/
class CompleteCRischLevel (L : CRischLevel P α) (domain : RischLevelDomain P α)
    [LawfulCRischLevel L domain] : Prop where
  /-- Any genuinely integrable input in this level's mathematical domain succeeds at some finite budget. -/
  relative_complete : ∀ (Dt a d : P α),
    domain Dt a d → CPoly.toPoly d ≠ 0 → IsRischLevelIntegrable Dt a d →
      ∃ fuel res, L.integrate fuel Dt a d = some res

/-- The generic Figure-5.1 composition with an explicit polynomial-reduction budget. -/
def oneLevelRischWithPolynomial (R : CPolynomialReduction P α) (kind : PolynomialReductionKind)
    (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [CHermiteReduction P α] [CResidueSource P α] [CResidueLogPart P α] : CRischLevel P α where
  integrate fuel Dt a d := assembleOneLevelWithPolynomial R kind fuel C Dt a d

/-- Domain of the Hermite-based assembler: monomial derivatives of degree at most one. -/
def lowDerivDegreeRischLevelDomain : RischLevelDomain P α :=
  fun Dt _ _ => (CPoly.toPoly Dt).natDegree ≤ 1

/-- The polynomial-aware packaged level inherits contract-only one-level soundness. -/
theorem oneLevelRischWithPolynomial_sound (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind) (fuel : ℕ)
    (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    [CHermiteReduction P α] [LawfulCHermiteReduction (P := P) (α := α)]
    [CResidueSource P α] [CResidueLogPart P α] [LawfulCResidueLogPart (P := P) (α := α)]
    (Dt a d : P α) (res : IntegralResult α P)
    (hd : CPoly.toPoly d ≠ 0) (hdomain : lowDerivDegreeRischLevelDomain Dt a d)
    (hrun : (oneLevelRischWithPolynomial R kind C).integrate fuel Dt a d = some res) :
    IsIntegralResultP Dt a d res :=
  assembleOneLevelWithPolynomial_sound R kind fuel C Dt a d res hd hdomain hrun

/-- The polynomial-aware contract composition is a lawful Risch level. -/
instance instLawfulCRischLevelOneLevelRischWithPolynomial (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    [CHermiteReduction P α] [LawfulCHermiteReduction (P := P) (α := α)]
    [CResidueSource P α] [CResidueLogPart P α]
    [LawfulCResidueLogPart (P := P) (α := α)] :
    LawfulCRischLevel (oneLevelRischWithPolynomial R kind C) lowDerivDegreeRischLevelDomain where
  sound fuel Dt a d res hdomain hd hrun :=
    oneLevelRischWithPolynomial_sound R kind fuel C Dt a d res hd hdomain hrun

/-- Domain where genuine integrability decomposes into explicit Figure-5.1 stage witnesses. -/
def polynomialRischLevelDomain (R : CPolynomialReduction P α) (kind : PolynomialReductionKind)
    [CCanonicalRepresentation P α] [CHermiteReduction P α] : RischLevelDomain P α :=
  fun Dt a d => lowDerivDegreeRischLevelDomain Dt a d ∧
    (IsRischLevelIntegrable Dt a d → PolynomialAssemblyWitness R kind Dt a d)

/-- The polynomial-aware level is lawful on the explicit stage-decomposition domain. -/
instance instLawfulCRischLevelPolynomialDomain (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    [CHermiteReduction P α] [LawfulCHermiteReduction (P := P) (α := α)]
    [CResidueSource P α] [CResidueLogPart P α]
    [LawfulCResidueLogPart (P := P) (α := α)] :
    LawfulCRischLevel (oneLevelRischWithPolynomial R kind C)
      (polynomialRischLevelDomain R kind) where
  sound fuel Dt a d res hdomain hd hrun :=
    oneLevelRischWithPolynomial_sound R kind fuel C Dt a d res hd hdomain.1 hrun

/-- Complete stage contracts make the polynomial-aware level relatively complete at some finite budget. -/
theorem completeCRischLevelWithPolynomial (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] [CompleteCPolynomialReduction R]
    (kind : PolynomialReductionKind) (C : CMonomialCase P α)
    [LawfulCMonomialCase C] [CompleteCMonomialCase C]
    [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)]
    [CHermiteReduction P α] [LawfulCHermiteReduction (P := P) (α := α)]
    [CResidueSource P α] [CResidueLogPart P α]
    [LawfulCResidueLogPart (P := P) (α := α)]
    [CompleteCResidueLogPart (P := P) (α := α)]
    (hsource : LawfulCResidueSource P α) :
    CompleteCRischLevel (oneLevelRischWithPolynomial R kind C)
      (polynomialRischLevelDomain R kind) := by
  constructor
  intro Dt a d hdomain hd hintegrable
  exact assembleOneLevelWithPolynomial_complete R kind C hsource Dt a d hd hdomain.1
    (hdomain.2 hintegrable)

end DeepWiki.SymbolicIntegration
