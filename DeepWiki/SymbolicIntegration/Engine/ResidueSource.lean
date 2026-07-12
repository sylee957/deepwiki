import DeepWiki.ComputableAlgebra.PolyReprDenote
import DeepWiki.ComputableAlgebra.Field
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
