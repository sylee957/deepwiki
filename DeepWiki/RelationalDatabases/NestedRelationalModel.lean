import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup

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
/-- Boolean equality of nested values (and, mutually, of relations and tuples). `deriving
DecidableEq` does not apply to this nested carrier, so equality is built by hand. -/
def NestedValue.beq [DecidableEq Att] [DecidableEq V] :
    NestedValue Att V → NestedValue Att V → Bool
  | .atom v, .atom w => decide (v = w)
  | .rel r1, .rel r2 => NestedValue.beqRel r1 r2
  | .atom _, .rel _ => false
  | .rel _, .atom _ => false
/-- Boolean equality lifted to nested relations. -/
def NestedValue.beqRel [DecidableEq Att] [DecidableEq V] :
    NestedRel Att V → NestedRel Att V → Bool
  | [], [] => true
  | t1 :: r1, t2 :: r2 => NestedValue.beqTuple t1 t2 && NestedValue.beqRel r1 r2
  | [], _ :: _ => false
  | _ :: _, [] => false
/-- Boolean equality lifted to nested tuples. -/
def NestedValue.beqTuple [DecidableEq Att] [DecidableEq V] :
    NestedTuple Att V → NestedTuple Att V → Bool
  | [], [] => true
  | p1 :: t1, p2 :: t2 =>
      decide (p1.1 = p2.1) && NestedValue.beq p1.2 p2.2 && NestedValue.beqTuple t1 t2
  | [], _ :: _ => false
  | _ :: _, [] => false
end

mutual
/-- Correctness of `beq`: it decides equality of nested values. -/
theorem NestedValue.beq_iff [DecidableEq Att] [DecidableEq V] :
    ∀ a b : NestedValue Att V, NestedValue.beq a b = true ↔ a = b
  | .atom _, .atom _ => by simp [NestedValue.beq]
  | .rel r1, .rel r2 => by
      simp only [NestedValue.beq, NestedValue.beqRel_iff r1 r2, NestedValue.rel.injEq]
  | .atom _, .rel _ => by simp [NestedValue.beq]
  | .rel _, .atom _ => by simp [NestedValue.beq]
/-- Correctness of `beqRel`. -/
theorem NestedValue.beqRel_iff [DecidableEq Att] [DecidableEq V] :
    ∀ r1 r2 : NestedRel Att V, NestedValue.beqRel r1 r2 = true ↔ r1 = r2
  | [], [] => by simp [NestedValue.beqRel]
  | t1 :: r1, t2 :: r2 => by
      simp only [NestedValue.beqRel, Bool.and_eq_true, NestedValue.beqTuple_iff t1 t2,
        NestedValue.beqRel_iff r1 r2, List.cons.injEq]
  | [], _ :: _ => by simp [NestedValue.beqRel]
  | _ :: _, [] => by simp [NestedValue.beqRel]
/-- Correctness of `beqTuple`. -/
theorem NestedValue.beqTuple_iff [DecidableEq Att] [DecidableEq V] :
    ∀ t1 t2 : NestedTuple Att V, NestedValue.beqTuple t1 t2 = true ↔ t1 = t2
  | [], [] => by simp [NestedValue.beqTuple]
  | p1 :: t1, p2 :: t2 => by
      simp only [NestedValue.beqTuple, Bool.and_eq_true, decide_eq_true_eq,
        NestedValue.beq_iff p1.2 p2.2, NestedValue.beqTuple_iff t1 t2, List.cons.injEq, Prod.ext_iff]
  | [], _ :: _ => by simp [NestedValue.beqTuple]
  | _ :: _, [] => by simp [NestedValue.beqTuple]
end

/-- Decidable equality of nested values (from `beq` and its correctness). -/
instance [DecidableEq Att] [DecidableEq V] : DecidableEq (NestedValue Att V) :=
  fun a b => decidable_of_iff _ (NestedValue.beq_iff a b)

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

/-! ## The nest operator (§7.2) -/

/-- Keep only the pairs of a nested tuple whose attribute lies in `X`. -/
def NestedTuple.projTo (X : List Att) (t : NestedTuple Att V) : NestedTuple Att V :=
  t.filter (fun p => decide (p.1 ∈ X))

/-- Drop the pairs of a nested tuple whose attribute lies in `X` (the complementary projection). -/
def NestedTuple.dropKeys (X : List Att) (t : NestedTuple Att V) : NestedTuple Att V :=
  t.filter (fun p => decide (p.1 ∉ X))

variable [DecidableEq V]

/-- **Nest** `ν_{X→B}` (§7.2): group the rows of a nested relation by their values *outside* `X`,
and for each group emit one row — the common outside-`X` part extended with a new attribute `B`
whose value is the relation of the group's `X`-projections. Dual to `unnest`. -/
def NestedValue.nest (X : List Att) (B : Att) : NestedValue Att V → NestedValue Att V
  | .atom v => .atom v
  | .rel rows =>
    let rests := (rows.map (NestedTuple.dropKeys X)).dedup
    .rel (rests.map (fun rest =>
      rest ++ [(B, .rel ((rows.filter (fun t => decide (NestedTuple.dropKeys X t = rest))).map
        (NestedTuple.projTo X)))]))

@[simp] theorem NestedValue.nest_atom (X : List Att) (B : Att) (v : V) :
    (NestedValue.atom (Att := Att) v).nest X B = .atom v := rfl

open NestedValue in
example : (rel [[("A", atom 1), ("C", atom 2)], [("A", atom 1), ("C", atom 3)],
      [("A", atom 5), ("C", atom 6)]]).nest ["C"] "D"
    = rel [[("A", atom 1), ("D", rel [[("C", atom 2)], [("C", atom 3)]])],
      [("A", atom 5), ("D", rel [[("C", atom 6)]])]] := by decide

/-! ## The set operators, projection and selection (§7.2) -/

/-- **Union** `∪` (§7.2): set union of two nested relations (deduplicated append). Non-relations
return the left operand. -/
def NestedValue.union : NestedValue Att V → NestedValue Att V → NestedValue Att V
  | .rel r1, .rel r2 => .rel (r1 ++ r2).dedup
  | a, _ => a

/-- **Difference** `−` (§7.2): the rows of the left relation not in the right. -/
def NestedValue.diff : NestedValue Att V → NestedValue Att V → NestedValue Att V
  | .rel r1, .rel r2 => .rel (r1.filter (fun t => decide (t ∉ r2)))
  | a, _ => a

/-- **Intersection** `∩` (§7.2): the rows in both relations. -/
def NestedValue.inter : NestedValue Att V → NestedValue Att V → NestedValue Att V
  | .rel r1, .rel r2 => .rel (r1.filter (fun t => decide (t ∈ r2)))
  | a, _ => a

/-- **Projection** `π_X` (§7.2): project every tuple onto the attributes `X` (deduplicated). -/
def NestedValue.proj (X : List Att) : NestedValue Att V → NestedValue Att V
  | .atom v => .atom v
  | .rel rows => .rel ((rows.map (NestedTuple.projTo X)).dedup)

/-- **Selection** `σ_P` (§7.2): keep the tuples satisfying the Boolean condition `P`. -/
def NestedValue.sel (P : NestedTuple Att V → Bool) : NestedValue Att V → NestedValue Att V
  | .atom v => .atom v
  | .rel rows => .rel (rows.filter P)

@[simp] theorem NestedValue.proj_atom (X : List Att) (v : V) :
    (NestedValue.atom (Att := Att) v).proj X = .atom v := rfl

omit [DecidableEq Att] [DecidableEq V] in
@[simp] theorem NestedValue.sel_atom (P : NestedTuple Att V → Bool) (v : V) :
    (NestedValue.atom (Att := Att) v).sel P = .atom v := rfl

open NestedValue in
example : (rel [[("A", atom 1), ("B", atom 2)], [("A", atom 1), ("B", atom 3)]]).proj ["A"]
    = rel [[("A", atom 1)]] := by decide

/-- **Cartesian product** `×` (§7.2): every row of the left concatenated with every row of the
right (deduplicated). -/
def NestedValue.product : NestedValue Att V → NestedValue Att V → NestedValue Att V
  | .rel r1, .rel r2 => .rel ((r1.flatMap (fun t1 => r2.map (fun t2 => t1 ++ t2))).dedup)
  | a, _ => a

/-! ## Nested algebra expressions (§7.2, Definition 7.8) -/

/-- **Definition 7.8** (§7.2): a *nested algebra expression* — the syntax of the nested relational
algebra over base relations: union, difference, intersection, cartesian product, projection,
selection, nest, unnest and renaming. -/
inductive NestedAlgExpr (Att V : Type) where
  /-- A base (constant) nested relation. -/
  | base : NestedValue Att V → NestedAlgExpr Att V
  /-- Union of two expressions. -/
  | union : NestedAlgExpr Att V → NestedAlgExpr Att V → NestedAlgExpr Att V
  /-- Difference of two expressions. -/
  | diff : NestedAlgExpr Att V → NestedAlgExpr Att V → NestedAlgExpr Att V
  /-- Intersection of two expressions. -/
  | inter : NestedAlgExpr Att V → NestedAlgExpr Att V → NestedAlgExpr Att V
  /-- Cartesian product of two expressions. -/
  | product : NestedAlgExpr Att V → NestedAlgExpr Att V → NestedAlgExpr Att V
  /-- Projection onto a set of attributes. -/
  | proj : List Att → NestedAlgExpr Att V → NestedAlgExpr Att V
  /-- Selection by a Boolean condition. -/
  | sel : (NestedTuple Att V → Bool) → NestedAlgExpr Att V → NestedAlgExpr Att V
  /-- Nest a set of attributes under a new relation-valued attribute. -/
  | nest : List Att → Att → NestedAlgExpr Att V → NestedAlgExpr Att V
  /-- Unnest a relation-valued attribute. -/
  | unnest : Att → NestedAlgExpr Att V → NestedAlgExpr Att V
  /-- Rename an attribute. -/
  | rename : Att → Att → NestedAlgExpr Att V → NestedAlgExpr Att V

/-- The value of a nested algebra expression (its denotational semantics). -/
def NestedAlgExpr.eval : NestedAlgExpr Att V → NestedValue Att V
  | .base r => r
  | .union e₁ e₂ => (e₁.eval).union e₂.eval
  | .diff e₁ e₂ => (e₁.eval).diff e₂.eval
  | .inter e₁ e₂ => (e₁.eval).inter e₂.eval
  | .product e₁ e₂ => (e₁.eval).product e₂.eval
  | .proj X e => e.eval.proj X
  | .sel P e => e.eval.sel P
  | .nest X B e => e.eval.nest X B
  | .unnest a e => e.eval.unnest a
  | .rename a b e => e.eval.rename a b

@[simp] theorem NestedAlgExpr.eval_base (r : NestedValue Att V) :
    (NestedAlgExpr.base r).eval = r := rfl

open NestedValue in
/-- **Nest and unnest are not mutually inverse** (§7.2): unnesting an *empty* relation-valued
attribute drops the row entirely, and re-nesting cannot bring it back — so `ν ∘ μ` is not the
identity in general. -/
theorem nest_unnest_not_inverse :
    ¬ ∀ (r : NestedValue String ℕ) (X : List String) (B : String), (r.unnest B).nest X B = r :=
  fun h => absurd (h (rel [[("A", atom 1), ("B", rel [])]]) ["C"] "B") (by decide)

end DeepWiki
