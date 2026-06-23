import Mathlib.Data.List.Basic

/-! # The nested relational model
The nested (non-first-normal-form) model relaxes the flat-table assumption: a value may itself be
a relation. The carrier is the recursive *nested value* type (Def 7.4): an atomic value, or a
nested relation — a collection of tuples, each a map from attributes to nested values.

**Representation note.** A tuple is encoded as an *association list* `List (Att × NestedValue …)`
and a nested relation as a `List` of such tuples, rather than as a function `Att → NestedValue …`.
The function encoding is more faithful to "a tuple assigns a value to each attribute", but Lean
cannot recurse *through* a function-valued field (`t a` has no size measure), which makes `map`,
`depth`, and the nest/unnest operators undefinable. The list encoding is structurally recursable
(recursive functions are written as `mutual` blocks over value / relation / tuple); the set/map
semantics — order and duplicates being immaterial — is imposed by the operations, not the carrier.
Attributes and atomic values are taken in `Type` to keep the recursion monomorphic. -/

namespace DeepWiki

/-- A *nested value* (Def 7.4): either an atomic value, or a nested relation — a list of tuples,
each an association list of attribute–nested-value pairs. -/
inductive NestedValue (Att : Type) (V : Type) : Type where
  /-- An atomic value. -/
  | atom : V → NestedValue Att V
  /-- A nested relation: a list of tuples (association lists of attribute–value pairs). -/
  | rel : List (List (Att × NestedValue Att V)) → NestedValue Att V

/-- A *nested tuple*: an association list of attribute–nested-value pairs. -/
abbrev NestedTuple (Att V : Type) : Type := List (Att × NestedValue Att V)

/-- A *nested relation* (the payload of `NestedValue.rel`): a list of nested tuples. -/
abbrev NestedRel (Att V : Type) : Type := List (NestedTuple Att V)

variable {Att V W : Type}

/-- Whether a nested value is atomic (an `atom`) rather than a nested relation. -/
def NestedValue.isAtom : NestedValue Att V → Bool
  | .atom _ => true
  | .rel _ => false

@[simp] theorem NestedValue.isAtom_atom (v : V) :
    (NestedValue.atom (Att := Att) v).isAtom = true := rfl

@[simp] theorem NestedValue.isAtom_rel (l : NestedRel Att V) :
    (NestedValue.rel l).isAtom = false := rfl

/-- The atomic embedding is injective. -/
theorem NestedValue.atom_inj {v w : V}
    (h : (NestedValue.atom (Att := Att) v) = NestedValue.atom w) : v = w := by
  injection h

mutual
/-- Functorial map of `g : V → W` over the atoms of a nested value (and, mutually, over a nested
relation and over a tuple), recursing into every nesting level. -/
def NestedValue.map (g : V → W) : NestedValue Att V → NestedValue Att W
  | .atom v => .atom (g v)
  | .rel rows => .rel (NestedValue.mapRel g rows)
/-- `NestedValue.map` lifted over a nested relation (list of tuples). -/
def NestedValue.mapRel (g : V → W) : NestedRel Att V → NestedRel Att W
  | [] => []
  | row :: rest => NestedValue.mapTuple g row :: NestedValue.mapRel g rest
/-- `NestedValue.map` lifted over a nested tuple (association list). -/
def NestedValue.mapTuple (g : V → W) : NestedTuple Att V → NestedTuple Att W
  | [] => []
  | p :: rest => (p.1, NestedValue.map g p.2) :: NestedValue.mapTuple g rest
end

@[simp] theorem NestedValue.map_atom (g : V → W) (v : V) :
    (NestedValue.atom (Att := Att) v).map g = .atom (g v) := rfl

@[simp] theorem NestedValue.map_rel (g : V → W) (rows : NestedRel Att V) :
    (NestedValue.rel rows).map g = .rel (NestedValue.mapRel g rows) := rfl

mutual
/-- The *nesting depth* of a nested value: `0` for an atom, one more than the deepest value in any
of its tuples for a relation. -/
def NestedValue.depth : NestedValue Att V → Nat
  | .atom _ => 0
  | .rel rows => 1 + NestedValue.depthRel rows
/-- The maximum depth among the values of a nested relation. -/
def NestedValue.depthRel : NestedRel Att V → Nat
  | [] => 0
  | row :: rest => Nat.max (NestedValue.depthTuple row) (NestedValue.depthRel rest)
/-- The maximum depth among the values of a nested tuple. -/
def NestedValue.depthTuple : NestedTuple Att V → Nat
  | [] => 0
  | p :: rest => Nat.max p.2.depth (NestedValue.depthTuple rest)
end

@[simp] theorem NestedValue.depth_atom (v : V) :
    (NestedValue.atom (Att := Att) v).depth = 0 := rfl

/-- A nested relation has depth at least `1`. -/
theorem NestedValue.one_le_depth_rel (rows : NestedRel Att V) :
    1 ≤ (NestedValue.rel rows).depth := by
  simp only [NestedValue.depth]; omega

end DeepWiki
