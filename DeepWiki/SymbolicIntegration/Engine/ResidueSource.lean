import DeepWiki.ComputableAlgebra.PolyReprDenote
import DeepWiki.ComputableAlgebra.Field
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv

/-! # Representation-independent residue candidate sources

Residue sources enumerate coefficient-field candidates for roots of a Rothstein-Trager resultant. The
operation is Prop-free; `LawfulCResidueSource` separately states constant-root completeness. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Prop-free source of residue candidates for a represented resultant polynomial. -/
class CResidueSource (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] where
  /-- Enumerate candidate roots of a represented residue resultant. -/
  candidates : P α → List α

/-- Completeness contract for a residue candidate source over the constant field. -/
class LawfulCResidueSource (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
    [CResidueSource P α] : Prop where
  /-- Every enumerated candidate belongs to the constant field. -/
  candidates_constant : ∀ (R : P α) (c : α), c ∈ CResidueSource.candidates R →
    CFieldSpec.toK (CDiffField.cderiv c) = 0
  /-- Every constant coefficient-field root of the resultant is enumerated. -/
  candidates_complete : ∀ (R : P α) (c : α),
    CFieldSpec.toK (CDiffField.cderiv c) = 0 →
    (CPoly.toPoly R).eval (CFieldSpec.toK c) = 0 →
    c ∈ CResidueSource.candidates R

/-- Prop-free enumeration of a coefficient field's differential constants. -/
class CConstantEnumerator (α : Type u) [CField α] where
  /-- Enumerate every coefficient represented as a differential constant. -/
  constants : List α

/-- Denotational completeness contract for a finite differential-constant enumerator. -/
class LawfulCConstantEnumerator (α : Type u) [CField α] [CFieldSpec.{u,v} α]
    [CDiffField α] [CDiffFieldSpec.{u,v} α] [CConstantEnumerator α] : Prop where
  /-- Every enumerated coefficient is constant. -/
  constants_constant : ∀ (c : α), c ∈ CConstantEnumerator.constants →
    CFieldSpec.toK (CDiffField.cderiv c) = 0
  /-- Every represented differential constant is enumerated. -/
  constants_complete : ∀ (c : α), CFieldSpec.toK (CDiffField.cderiv c) = 0 →
    c ∈ CConstantEnumerator.constants

/-- Residue source obtained by filtering a finite enumeration of coefficient-field constants. -/
@[reducible] def finiteConstantResidueSource (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CConstantEnumerator α] : CResidueSource P α where
  candidates R := CConstantEnumerator.constants.filter fun c =>
    CCommRing.isZero (CPolyEngine.eval R c)

/-- Select the finite-constant residue source whenever the coefficient field provides one. -/
instance instCResidueSourceFiniteConstants (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CConstantEnumerator α] : CResidueSource P α :=
  finiteConstantResidueSource P

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
  {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]

/-- A lawful finite constant enumerator yields a lawful represented residue source. -/
instance instLawfulCResidueSourceFiniteConstants [CConstantEnumerator α]
    [LawfulCConstantEnumerator α] : LawfulCResidueSource P α where
  candidates_constant R c hc := by
    change c ∈ CConstantEnumerator.constants.filter (fun c =>
      CCommRing.isZero (CPolyEngine.eval R c)) at hc
    exact LawfulCConstantEnumerator.constants_constant c (List.mem_filter.mp hc).1
  candidates_complete R c hconstant hroot := by
    apply List.mem_filter.mpr
    refine ⟨LawfulCConstantEnumerator.constants_complete c hconstant, ?_⟩
    rw [CFieldSpec.isZero_iff]
    change CRingSpec.toR (CPolyEngine.eval R c) = 0
    rw [LawfulCPolyEngine.toR_eval]
    exact hroot

/-- Rational `p/q` in any computable field, using the field's integer and natural casts. -/
def cRat (p : ℤ) (q : ℕ) {α : Type u} [CField α] : α :=
  CField.div (if p < 0 then CCommRing.neg (CField.natCast p.natAbs) else CField.natCast p.natAbs)
    (CField.natCast q)

/-- Bounded rational sweep `{p/q : |p| ≤ bound, 1 ≤ q ≤ bound}` in a computable field. -/
def defaultResidueCandidates (bound : ℕ) {α : Type u} [CField α] : List α :=
  (List.range (2 * bound + 1)).flatMap (fun i =>
    (List.range bound).map (fun j => cRat ((i : ℤ) - (bound : ℤ)) (j + 1)))

/-- Bounded rational residue source; it has no lawful completeness instance because the sweep is finite. -/
@[reducible] def boundedRationalResidueSource {P : Type u → Type u} [CPoly P]
    {α : Type u} [CField α] (bound : ℕ) : CResidueSource P α where
  candidates _ := defaultResidueCandidates bound

end DeepWiki.SymbolicIntegration
