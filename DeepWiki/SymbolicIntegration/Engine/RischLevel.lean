import DeepWiki.SymbolicIntegration.Engine.PolynomialAssembly
import DeepWiki.SymbolicIntegration.Engine.RecursiveMonomialCase

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

/-- The generic Figure-5.1 composition from polynomial, normal, and monomial-case operations. -/
def oneLevelRisch (R : CPolynomialReduction P α) (kind : PolynomialReductionKind)
    (N : CNormalReduction P α) (C : CMonomialCase P α)
    [CCanonicalRepresentation P α] : CRischLevel P α where
  integrate fuel Dt a d := assembleOneLevel R kind N fuel C Dt a d

/-- The Figure-5.1 level with an explicit recursively supplied coefficient-field stage. -/
def oneLevelRischWithRecursiveCoefficient (R : CPolynomialReduction P α)
    (kind : PolynomialReductionKind) (C : CRecursiveMonomialCase P α)
    (N : CNormalReduction P α) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation P α] : CRischLevel P α :=
  oneLevelRisch R kind N (C.withCoefficient I)

/-- Soundness domain induced by a normal reducer after canonical decomposition. -/
def oneLevelRischSoundDomain (normalDomain : NormalReductionDomain P α)
    [CCanonicalRepresentation P α] : RischLevelDomain P α :=
  fun Dt a d => normalDomain Dt (canonicalResult Dt a d).normalNum
    (canonicalResult Dt a d).normalDen

/-- The packaged level inherits soundness solely from its stage contracts. -/
theorem oneLevelRisch_sound (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind) (fuel : ℕ)
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] (C : CMonomialCase P α)
    [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    (Dt a d : P α) (res : IntegralResult α P)
    (hd : CPoly.toPoly d ≠ 0) (hdomain : oneLevelRischSoundDomain normalDomain Dt a d)
    (hrun : (oneLevelRisch R kind N C).integrate fuel Dt a d = some res) :
    IsIntegralResultP Dt a d res :=
  assembleOneLevel_sound R kind fuel N normalDomain C Dt a d res hd hdomain hrun

/-- Contract composition is a lawful Risch level on the selected normal reducer's domain. -/
instance instLawfulCRischLevelOneLevelRisch (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] (C : CMonomialCase P α)
    [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    : LawfulCRischLevel (oneLevelRisch R kind N C)
      (oneLevelRischSoundDomain normalDomain) where
  sound fuel Dt a d res hdomain hd hrun :=
    oneLevelRisch_sound R kind fuel N normalDomain C Dt a d res hd hdomain hrun

/-- Domain where genuine integrability decomposes into explicit Figure-5.1 stage witnesses. -/
def oneLevelRischCompleteDomain (R : CPolynomialReduction P α) (kind : PolynomialReductionKind)
    (normalDomain : NormalReductionDomain P α)
    [CCanonicalRepresentation P α] : RischLevelDomain P α :=
  fun Dt a d => oneLevelRischSoundDomain normalDomain Dt a d ∧
    (IsRischLevelIntegrable Dt a d → OneLevelAssemblyWitness R kind normalDomain Dt a d)

/-- The composed level is lawful on its explicit stage-decomposition domain. -/
instance instLawfulCRischLevelCompleteDomain (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] (C : CMonomialCase P α)
    [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    : LawfulCRischLevel (oneLevelRisch R kind N C)
      (oneLevelRischCompleteDomain R kind normalDomain) where
  sound fuel Dt a d res hdomain hd hrun :=
    oneLevelRisch_sound R kind fuel N normalDomain C Dt a d res hd hdomain.1 hrun

/-- Complete stage contracts make the composed level relatively complete at some finite budget. -/
theorem completeCRischLevel (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] [CompleteCPolynomialReduction R]
    (kind : PolynomialReductionKind) (N : CNormalReduction P α)
    (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] [CompleteCNormalReduction N normalDomain]
    (C : CMonomialCase P α)
    [LawfulCMonomialCase C] [CompleteCMonomialCase C]
    [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] :
    CompleteCRischLevel (oneLevelRisch R kind N C)
      (oneLevelRischCompleteDomain R kind normalDomain) := by
  constructor
  intro Dt a d hdomain hd hintegrable
  exact assembleOneLevel_complete R kind N normalDomain C Dt a d hd
    (hdomain.2 hintegrable)

end DeepWiki.SymbolicIntegration
