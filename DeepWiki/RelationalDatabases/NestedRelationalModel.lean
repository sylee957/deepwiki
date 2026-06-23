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

variable {Att V W X : Type}

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

mutual
/-- Functor identity law: mapping the identity is the identity. -/
theorem NestedValue.map_id : ∀ x : NestedValue Att V, x.map id = x
  | .atom _ => rfl
  | .rel rows => by simp only [NestedValue.map, NestedValue.mapRel_id rows]
/-- Identity law lifted to a nested relation. -/
theorem NestedValue.mapRel_id : ∀ rows : NestedRel Att V, NestedValue.mapRel id rows = rows
  | [] => rfl
  | row :: rest => by
      simp only [NestedValue.mapRel, NestedValue.mapTuple_id row, NestedValue.mapRel_id rest]
/-- Identity law lifted to a nested tuple. -/
theorem NestedValue.mapTuple_id : ∀ row : NestedTuple Att V, NestedValue.mapTuple id row = row
  | [] => rfl
  | p :: rest => by
      simp only [NestedValue.mapTuple, NestedValue.map_id p.2, NestedValue.mapTuple_id rest]
end

mutual
/-- Functor composition law: `(x.map f).map g = x.map (g ∘ f)`. -/
theorem NestedValue.map_map (f : V → W) (g : W → X) :
    ∀ x : NestedValue Att V, (x.map f).map g = x.map (fun v => g (f v))
  | .atom _ => rfl
  | .rel rows => by simp only [NestedValue.map, NestedValue.mapRel_map f g rows]
/-- Composition law lifted to a nested relation. -/
theorem NestedValue.mapRel_map (f : V → W) (g : W → X) :
    ∀ rows : NestedRel Att V,
      NestedValue.mapRel g (NestedValue.mapRel f rows) = NestedValue.mapRel (fun v => g (f v)) rows
  | [] => rfl
  | row :: rest => by
      simp only [NestedValue.mapRel, NestedValue.mapTuple_map f g row, NestedValue.mapRel_map f g rest]
/-- Composition law lifted to a nested tuple. -/
theorem NestedValue.mapTuple_map (f : V → W) (g : W → X) :
    ∀ row : NestedTuple Att V,
      NestedValue.mapTuple g (NestedValue.mapTuple f row) = NestedValue.mapTuple (fun v => g (f v)) row
  | [] => rfl
  | p :: rest => by
      simp only [NestedValue.mapTuple, NestedValue.map_map f g p.2, NestedValue.mapTuple_map f g rest]
end

mutual
/-- `map` preserves nesting depth (it only relabels atoms). -/
theorem NestedValue.depth_map (g : V → W) : ∀ x : NestedValue Att V, (x.map g).depth = x.depth
  | .atom _ => rfl
  | .rel rows => by simp only [NestedValue.map, NestedValue.depth, NestedValue.depthRel_map g rows]
/-- Depth preservation lifted to a nested relation. -/
theorem NestedValue.depthRel_map (g : V → W) :
    ∀ rows : NestedRel Att V,
      NestedValue.depthRel (NestedValue.mapRel g rows) = NestedValue.depthRel rows
  | [] => rfl
  | row :: rest => by
      simp only [NestedValue.mapRel, NestedValue.depthRel, NestedValue.depthTuple_map g row,
        NestedValue.depthRel_map g rest]
/-- Depth preservation lifted to a nested tuple. -/
theorem NestedValue.depthTuple_map (g : V → W) :
    ∀ row : NestedTuple Att V,
      NestedValue.depthTuple (NestedValue.mapTuple g row) = NestedValue.depthTuple row
  | [] => rfl
  | p :: rest => by
      simp only [NestedValue.mapTuple, NestedValue.depthTuple, NestedValue.depth_map g p.2,
        NestedValue.depthTuple_map g rest]
end

/-- A nested value is *flat* (in first normal form) when its nesting depth is at most one — an atom,
or a relation all of whose tuple values are atomic. -/
def NestedValue.isFlat (x : NestedValue Att V) : Prop := x.depth ≤ 1

/-- Atoms are flat. -/
theorem NestedValue.isFlat_atom (v : V) : (NestedValue.atom (Att := Att) v).isFlat := by
  simp [NestedValue.isFlat]

/-- Flatness is preserved by `map`. -/
theorem NestedValue.isFlat.map {x : NestedValue Att V} (g : V → W) (h : x.isFlat) :
    (x.map g).isFlat := by
  simp only [NestedValue.isFlat, NestedValue.depth_map]; exact h

/-! ## The unnest operator (§7.2) -/

variable [DecidableEq Att]

/-- Look up the value of attribute `a` in a nested tuple (the first matching pair). -/
def NestedTuple.lookup (a : Att) (t : NestedTuple Att V) : Option (NestedValue Att V) :=
  (t.find? (fun p => decide (p.1 = a))).map Prod.snd

/-- Drop every pair for attribute `a` from a nested tuple. -/
def NestedTuple.eraseKey (a : Att) (t : NestedTuple Att V) : NestedTuple Att V :=
  t.filter (fun p => decide (p.1 ≠ a))

/-- Unnest a single tuple on a relation-valued attribute `a`: replace it by one tuple per sub-row,
each the tuple (minus `a`) extended with that sub-row. A non-relation value leaves the tuple as is;
an empty sub-relation makes the tuple vanish. -/
def NestedRel.unnestTuple (a : Att) (t : NestedTuple Att V) : NestedRel Att V :=
  match NestedTuple.lookup a t with
  | some (.rel sub) => sub.map (fun s => NestedTuple.eraseKey a t ++ s)
  | _ => [t]

/-- **Unnest** `μ_a` (§7.2): flatten a nested relation on the relation-valued attribute `a`. -/
def NestedValue.unnest (a : Att) : NestedValue Att V → NestedValue Att V
  | .atom v => .atom v
  | .rel rows => .rel (rows.flatMap (NestedRel.unnestTuple a))

@[simp] theorem NestedValue.unnest_atom (a : Att) (v : V) :
    (NestedValue.atom (Att := Att) v).unnest a = .atom v := rfl

@[simp] theorem NestedValue.unnest_rel (a : Att) (rows : NestedRel Att V) :
    (NestedValue.rel rows).unnest a = .rel (rows.flatMap (NestedRel.unnestTuple a)) := rfl

open NestedValue in
example : (rel [[("A", atom 1), ("B", rel [[("C", atom 2)], [("C", atom 3)]])]]).unnest "B"
    = rel [[("A", atom 1), ("C", atom 2)], [("A", atom 1), ("C", atom 3)]] := rfl

/-! ## The renaming operator (§7.2) -/

/-- Rename attribute `a` to `b` in a nested tuple (top-level keys only). -/
def NestedTuple.renameKey (a b : Att) (t : NestedTuple Att V) : NestedTuple Att V :=
  t.map (fun p => if p.1 = a then (b, p.2) else p)

/-- **Renaming** `ρ_{a→b}` (§7.2): rename a top-level attribute `a` to `b` throughout a nested
relation. Nested sub-relations keep their own schemes and are untouched. -/
def NestedValue.rename (a b : Att) : NestedValue Att V → NestedValue Att V
  | .atom v => .atom v
  | .rel rows => .rel (rows.map (NestedTuple.renameKey a b))

@[simp] theorem NestedValue.rename_atom (a b : Att) (v : V) :
    (NestedValue.atom (Att := Att) v).rename a b = .atom v := rfl

@[simp] theorem NestedValue.rename_rel (a b : Att) (rows : NestedRel Att V) :
    (NestedValue.rel rows).rename a b = .rel (rows.map (NestedTuple.renameKey a b)) := rfl

open NestedValue in
example : (rel [[("A", atom 1), ("B", atom 2)]]).rename "A" "Z"
    = rel [[("Z", atom 1), ("B", atom 2)]] := rfl

end DeepWiki
