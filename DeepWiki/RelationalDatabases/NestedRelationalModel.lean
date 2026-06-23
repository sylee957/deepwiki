import Mathlib.Data.Finset.Basic

/-! # The nested relational model
The nested (non-first-normal-form) model relaxes the flat-table assumption: a value may itself be
a relation. The carrier is the recursive *nested value* type (Def 7.4): an atomic value, or a
nested relation — a collection of tuples, each a map from attributes to nested values. Attributes
and atomic values are taken in `Type` to keep the recursive definition monomorphic.

The nested algebra (nest/unnest and the lifted relational operators), nested functional and
multivalued dependencies, and the expressiveness results are layered on this carrier later. -/

namespace DeepWiki

/-- A *nested value* (Def 7.4): either an atomic value, or a nested relation — a list of tuples,
each a map from attributes to nested values. -/
inductive NestedValue (Att : Type) (V : Type) : Type where
  /-- An atomic value. -/
  | atom : V → NestedValue Att V
  /-- A nested relation: a list of tuples (attribute-to-nested-value maps). -/
  | rel : List (Att → NestedValue Att V) → NestedValue Att V

/-- Whether a nested value is atomic (an `atom`) rather than a nested relation. -/
def NestedValue.isAtom {Att V : Type} : NestedValue Att V → Bool
  | .atom _ => true
  | .rel _ => false

@[simp] theorem NestedValue.isAtom_atom {Att V : Type} (v : V) :
    (NestedValue.atom (Att := Att) v).isAtom = true := rfl

@[simp] theorem NestedValue.isAtom_rel {Att V : Type} (l : List (Att → NestedValue Att V)) :
    (NestedValue.rel l).isAtom = false := rfl

/-- The atomic embedding is injective. -/
theorem NestedValue.atom_inj {Att V : Type} {v w : V}
    (h : (NestedValue.atom (Att := Att) v) = NestedValue.atom w) : v = w := by
  injection h

end DeepWiki
