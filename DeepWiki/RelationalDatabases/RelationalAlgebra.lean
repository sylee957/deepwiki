import DeepWiki.RelationalDatabases.RelationalModel
import Mathlib.Data.Set.Image
import Mathlib.Data.Finset.Lattice.Basic

/-! # The relational algebra
The operators of the relational algebra at the row level: projection, selection, join, union,
difference and intersection, acting on *tables* (sets of rows over an attribute set). The
operators follow the book's instance-level semantics: projection restricts every row, the join
pairs rows agreeing on the common attributes, and union/difference/intersection are the
set-theoretic operations on tables over equal attributes.

Tables are sets of raw rows `Tuple Ω Val`; the per-attribute domains of a view scheme are
bookkeeping handled at the scheme level and are not needed for the instance-level operators.
Intersection is shown to be expressible from difference (`inter_eq_diff_diff`), the first step
of the "generating part" being expressively complete. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v}

/-- Restrict a row over `Ω` to a smaller attribute set `Ω₁ ⊆ Ω` (the book's `t[Ω₁]`). -/
def Tuple.restrict {Ω Ω₁ : Finset Att} (t : Tuple Ω Val) (h : Ω₁ ⊆ Ω) : Tuple Ω₁ Val :=
  fun a => t ⟨a.val, h a.property⟩

/-- A *table* over `Ω`: a set of rows over `Ω` — a relation or view instance at the row level. -/
abbrev Table (Ω : Finset Att) (Val : Type v) : Type _ := Set (Tuple Ω Val)

/-- **Projection** `Π(v; Ω₁)`: the rows of `v` restricted to `Ω₁ ⊆ Ω`. -/
def project {Ω Ω₁ : Finset Att} (h : Ω₁ ⊆ Ω) (v : Table Ω Val) : Table Ω₁ Val :=
  (fun t => t.restrict h) '' v

/-- **Selection** `σ(v; P)`: the rows of `v` satisfying the condition `P`. -/
def select {Ω : Finset Att} (P : Tuple Ω Val → Prop) (v : Table Ω Val) : Table Ω Val :=
  {t ∈ v | P t}

/-- **Join** `v ⋈ v'`: the rows over `Ω ∪ Ω'` whose `Ω`-part lies in `v` and `Ω'`-part in `v'`
(the cartesian product when `Ω` and `Ω'` are disjoint). -/
def join [DecidableEq Att] {Ω Ω' : Finset Att} (v : Table Ω Val) (v' : Table Ω' Val) :
    Table (Ω ∪ Ω') Val :=
  {t | t.restrict Finset.subset_union_left ∈ v ∧ t.restrict Finset.subset_union_right ∈ v'}

/-- **Union** `v ∪ v'` of two tables over the same attribute set. -/
def union {Ω : Finset Att} (v v' : Table Ω Val) : Table Ω Val := v ∪ v'

/-- **Difference** `v − v'` of two tables over the same attribute set. -/
def diff {Ω : Finset Att} (v v' : Table Ω Val) : Table Ω Val := v \ v'

/-- **Intersection** `v ∩ v'` of two tables over the same attribute set. -/
def inter {Ω : Finset Att} (v v' : Table Ω Val) : Table Ω Val := v ∩ v'

@[simp] theorem mem_project {Ω Ω₁ : Finset Att} (h : Ω₁ ⊆ Ω) (v : Table Ω Val)
    (s : Tuple Ω₁ Val) : s ∈ project h v ↔ ∃ t ∈ v, t.restrict h = s := by
  simp [project, Set.mem_image]

@[simp] theorem mem_select {Ω : Finset Att} (P : Tuple Ω Val → Prop) (v : Table Ω Val)
    (t : Tuple Ω Val) : t ∈ select P v ↔ t ∈ v ∧ P t := Iff.rfl

@[simp] theorem mem_join [DecidableEq Att] {Ω Ω' : Finset Att} (v : Table Ω Val)
    (v' : Table Ω' Val) (t : Tuple (Ω ∪ Ω') Val) :
    t ∈ join v v' ↔
      t.restrict Finset.subset_union_left ∈ v ∧ t.restrict Finset.subset_union_right ∈ v' :=
  Iff.rfl

@[simp] theorem mem_union {Ω : Finset Att} (v v' : Table Ω Val) (t : Tuple Ω Val) :
    t ∈ union v v' ↔ t ∈ v ∨ t ∈ v' := Iff.rfl

@[simp] theorem mem_diff {Ω : Finset Att} (v v' : Table Ω Val) (t : Tuple Ω Val) :
    t ∈ diff v v' ↔ t ∈ v ∧ t ∉ v' := Iff.rfl

@[simp] theorem mem_inter {Ω : Finset Att} (v v' : Table Ω Val) (t : Tuple Ω Val) :
    t ∈ inter v v' ↔ t ∈ v ∧ t ∈ v' := Iff.rfl

/-- Intersection is expressible from difference: `v ∩ v' = v − (v − v')` — the first reduction
showing the generating part is expressively complete. -/
theorem inter_eq_diff_diff {Ω : Finset Att} (v v' : Table Ω Val) :
    inter v v' = diff v (diff v v') := by
  ext t
  simp only [mem_inter, mem_diff, not_and, not_not]
  constructor
  · rintro ⟨hv, hv'⟩; exact ⟨hv, fun _ => hv'⟩
  · rintro ⟨hv, h⟩; exact ⟨hv, h hv⟩

/-- Selecting twice is selecting on the conjunction: `σ(σ(v; P); Q) = σ(v; P ∧ Q)`. -/
theorem select_select {Ω : Finset Att} (P Q : Tuple Ω Val → Prop) (v : Table Ω Val) :
    select Q (select P v) = select (fun t => P t ∧ Q t) v := by
  ext t; simp only [mem_select]; tauto

/-- Projection is transitive: `Π(Π(v; Ω₁); Ω₂) = Π(v; Ω₂)` for `Ω₂ ⊆ Ω₁ ⊆ Ω`. -/
theorem project_project {Ω Ω₁ Ω₂ : Finset Att} (h₁ : Ω₁ ⊆ Ω) (h₂ : Ω₂ ⊆ Ω₁)
    (v : Table Ω Val) : project h₂ (project h₁ v) = project (h₂.trans h₁) v := by
  ext s
  simp only [mem_project]
  constructor
  · rintro ⟨t', ⟨t, ht, rfl⟩, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t.restrict h₁, ⟨t, ht, rfl⟩, rfl⟩

end DeepWiki
