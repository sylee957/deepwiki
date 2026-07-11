import DeepWiki.SymbolicIntegration.Engine.Assemble

/-! # Compositional Risch-level interface

`CRischLevel` is the representation-neutral public boundary for one step of a transcendental
Risch tower.  Its lawful contract separates an executable level solver from the semantic
soundness and relative-completeness statements that a concrete monomial realization must prove. -/

namespace DeepWiki.SymbolicIntegration

universe u v

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Prop-free executable solver for one represented transcendental Risch level. -/
structure CRischLevel (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate the represented rational function `a/d`, or report that this level cannot do so. -/
  integrate : P α → P α → P α → Option (IntegralResult α P)

/-- Semantic domain predicate for a represented one-level Risch solver. -/
abbrev RischLevelDomain (P : Type u → Type u) (α : Type u) := P α → P α → P α → Prop

/-- Genuine Liouville-form integrability at one represented Risch level. -/
def IsRischLevelIntegrable (Dt a d : P α) : Prop :=
  ∃ res : IntegralResult α P, IsIntegralResultP Dt a d res ∧
    (∀ cv ∈ res.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
    (∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0)

/-- Denotation-level soundness and relative-completeness contract for a one-level Risch solver. -/
class LawfulCRischLevel (L : CRischLevel P α) (domain : RischLevelDomain P α) : Prop where
  /-- Every successful level solve is an integral-result certificate for its input. -/
  sound : ∀ (Dt a d : P α) (res : IntegralResult α P),
    CPoly.toPoly d ≠ 0 → L.integrate Dt a d = some res → IsIntegralResultP Dt a d res
  /-- Any genuinely integrable input in this level's mathematical domain produces an output. -/
  relative_complete : ∀ (Dt a d : P α),
    domain Dt a d → CPoly.toPoly d ≠ 0 → IsRischLevelIntegrable Dt a d →
      ∃ res, L.integrate Dt a d = some res

/-- The generic Figure-5.1 one-level composition, packaged as a `CRischLevel` operation. -/
def oneLevelRisch (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [CHermiteReduction P α] [CResidueSource P α] [CResidueLogPart P α] : CRischLevel P α where
  integrate Dt a d := assembleOneLevel C Dt a d

/-- Low-derivation-degree domain of the generic Hermite-based one-level assembler. -/
def oneLevelRischDomain : RischLevelDomain P α :=
  fun Dt _ _ => (CPoly.toPoly Dt).natDegree ≤ 1

/-- The packaged generic level inherits the one-level assembler's soundness theorem. -/
theorem oneLevelRisch_sound (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    [CHermiteReduction P α] [LawfulCHermiteReduction (P := P) (α := α)]
    [CResidueSource P α] [CResidueLogPart P α] [LawfulCResidueLogPart (P := P) (α := α)]
    (Dt a d : P α) (res : IntegralResult α P)
    (hd : CPoly.toPoly d ≠ 0) (hdomain : oneLevelRischDomain Dt a d)
    (hrun : (oneLevelRisch C).integrate Dt a d = some res) :
    IsIntegralResultP Dt a d res :=
  assembleOneLevel_sound C Dt a d res hd hdomain hrun

end DeepWiki.SymbolicIntegration
