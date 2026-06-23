import DeepWiki.RelationalDatabases.RelationalModel
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Finprod

/-! # Worked example databases (Chapter 1 exercises): concrete schemes and constraints
Concrete instances of the relational model for the book's running examples, with their
constraints written as relation constraints (boolean functions on instances). Attributes are
strings and values are integers (booleans encoded as `0`/`1`, identifiers as integers); the
domains are left total (`Set.univ`) since the exercises constrain only the contents.

The informal clauses are not modelled: Ex 1.1's "the `A`-value is the first letter of the
English word for the `B`-value" (no formal object for "the English word for an integer") and
Ex 1.12's convex non-intersecting quadrilaterals (a geometry development out of scope here). -/

namespace DeepWiki

/-! ## Example 1.6 — `ROOMMAIDS` (Exercise 1.2) -/

/-- The `ROOMMAIDS` primitive relation scheme: attributes `RMN` (roommaid number) and `RN`
(room number). -/
abbrev roommaidsScheme : PrimRelScheme String ℤ := ⟨{"RMN", "RN"}, fun _ => Set.univ⟩

/-- The roommaid-number component of a `ROOMMAIDS` tuple. -/
def rmn (t : TupleOf roommaidsScheme) : ℤ := t.val ⟨"RMN", by decide⟩

/-- The room-number component of a `ROOMMAIDS` tuple. -/
def rn (t : TupleOf roommaidsScheme) : ℤ := t.val ⟨"RN", by decide⟩

/-- **Exercise 1.2**, first constraint: every roommaid is responsible for exactly four rooms. -/
def roommaids_fourRooms : RelConstraint roommaidsScheme :=
  fun r => ∀ t ∈ r, {t' | t' ∈ r ∧ rmn t' = rmn t}.ncard = 4

/-- **Exercise 1.2**, second constraint: no two different roommaids are responsible for the same
room. -/
def roommaids_uniqueRoom : RelConstraint roommaidsScheme :=
  fun r => ∀ t₁ ∈ r, ∀ t₂ ∈ r, rn t₁ = rn t₂ → rmn t₁ = rmn t₂

/-! ## Example 1.5 — `ABSTRACT` (Exercise 1.1) -/

/-- The `ABSTRACT` primitive relation scheme with attributes `A`, `B`, `C`. -/
abbrev abstractScheme : PrimRelScheme String ℤ := ⟨{"A", "B", "C"}, fun _ => Set.univ⟩

/-- The `B`-component of an `ABSTRACT` tuple. -/
def bval (t : TupleOf abstractScheme) : ℤ := t.val ⟨"B", by decide⟩

/-- The `C`-component of an `ABSTRACT` tuple. -/
def cval (t : TupleOf abstractScheme) : ℤ := t.val ⟨"C", by decide⟩

/-- **Exercise 1.1**, constraint: every tuple's `B`-value is smaller than its `C`-value. -/
def abstract_bLtC : RelConstraint abstractScheme := fun r => ∀ t ∈ r, bval t < cval t

/-- **Exercise 1.1**, constraint: no two different tuples have the same `B`-value. -/
def abstract_uniqueB : RelConstraint abstractScheme :=
  fun r => ∀ t₁ ∈ r, ∀ t₂ ∈ r, bval t₁ = bval t₂ → t₁ = t₂

/-- **Exercise 1.1**, constraint: for each tuple, the sum of the `B`-values of all tuples sharing
its `C`-value exceeds that `C`-value. (The fourth constraint — `A` is the first letter of the
English word for `B` — is informal and not modelled.) -/
def abstract_sumB : RelConstraint abstractScheme :=
  fun r => ∀ t ∈ r, cval t < ∑ᶠ t' ∈ {t' | t' ∈ r ∧ cval t' = cval t}, bval t'

/-! ## Example 1.2 — `ROOMS` and the `noremove` dynamic constraint (Exercise 1.3) -/

/-- The `ROOMS` primitive relation scheme: room number, number of beds, a bath flag (`0`/`1`),
floor and rate. -/
abbrev roomsScheme : PrimRelScheme String ℤ :=
  ⟨{"RN", "NOB", "BATH", "FLOOR", "RATE"}, fun _ => Set.univ⟩

/-- The `ROOMS` relation scheme (no static constraints attached here). -/
abbrev roomsRel : RelScheme String ℤ := ⟨roomsScheme, ∅⟩

/-- The room-number component of a `ROOMS` tuple. -/
def roomNum (t : TupleOf roomsScheme) : ℤ := t.val ⟨"RN", by decide⟩

/-- The bath flag of a `ROOMS` tuple (`1` = has a bath). -/
def bath (t : TupleOf roomsScheme) : ℤ := t.val ⟨"BATH", by decide⟩

/-- **Exercise 1.3**: the `noremove` dynamic relation constraint — a bath is never removed from a
room. If a room with a bath persists to the next instance, it still has a bath. -/
def rooms_noremove : DynRelConstraint roomsRel :=
  fun seq => ∀ n, ∀ t ∈ seq n, ∀ t' ∈ seq (n + 1), roomNum t = roomNum t' → bath t = 1 → bath t' = 1

/-! ## Exercise 1.8 — a database constraint not equivalent to relation constraints -/

/-- A database constraint is *equivalent to relation constraints* when it factors as a
conjunction of one relation constraint per relation scheme — its truth depends on each relation
separately. -/
def IsRelationConstraintEquiv {ι : Type} [Fintype ι] {Att Val : Type}
    (P : PrimDbScheme ι Att Val) (c : DbConstraint P) : Prop :=
  ∃ rc : (i : ι) → RelConstraint (P.scheme i).prim, ∀ d, c d ↔ ∀ i, rc i (d i)

/-- The single-attribute scheme used for both relations of the Exercise 1.8 database. -/
abbrev ex18Scheme : PrimRelScheme String ℤ := ⟨{"A"}, fun _ => Set.univ⟩

/-- The Exercise 1.8 relation scheme. -/
abbrev ex18Rel : RelScheme String ℤ := ⟨ex18Scheme, ∅⟩

/-- A two-relation database (`false` = R, `true` = S), both relations over the attribute `A`. -/
abbrev ex18Db : PrimDbScheme Bool String ℤ :=
  { scheme := fun _ => ex18Rel, compat := fun _ _ _ _ _ => rfl }

/-- The `A`-value of an Exercise-1.8 tuple. -/
def aOf18 (t : TupleOf ex18Scheme) : ℤ := t.val ⟨"A", by decide⟩

/-- The tuple over `ex18Scheme` with `A`-value `v`. -/
def tupA (v : ℤ) : TupleOf ex18Scheme := ⟨fun _ => v, fun _ => Set.mem_univ _⟩

@[simp] theorem aOf18_tupA (v : ℤ) : aOf18 (tupA v) = v := rfl

/-- The inclusion database constraint `R.A ⊆ S.A`. -/
def ex18Incl : DbConstraint ex18Db := fun d => ∀ t ∈ d false, ∃ t' ∈ d true, aOf18 t = aOf18 t'

/-- **Exercise 1.8**: the inclusion database constraint is *not* equivalent to relation
constraints. It genuinely relates the two relations, so its model set is not closed under mixing
components — taking R from one satisfying instance and S from another can violate it. (This is
why some database constraints cannot be expressed by constraints on the individual relations.) -/
theorem ex18_not_relationConstraintEquiv : ¬ IsRelationConstraintEquiv ex18Db ex18Incl := by
  rintro ⟨rc, h⟩
  have hc1 : ex18Incl (fun _ => {tupA 1}) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨tupA 1, Set.mem_singleton_iff.mpr rfl, rfl⟩
  have hc2 : ex18Incl (fun _ => {tupA 2}) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨tupA 2, Set.mem_singleton_iff.mpr rfl, rfl⟩
  -- the mixed instance: R = {tupA 1}, S = {tupA 2}
  have hmix : ∀ i,
      rc i ((fun b => bif b then ({tupA 2} : Set (TupleOf ex18Scheme)) else {tupA 1}) i) := by
    intro i
    cases i with
    | false => exact (h _).mp hc1 false
    | true => exact (h _).mp hc2 true
  have hc3 := (h _).mpr hmix
  obtain ⟨t', ht', heq⟩ := hc3 (tupA 1) (Set.mem_singleton_iff.mpr rfl)
  have ht'' : t' = tupA 2 := ht'
  subst ht''
  exact absurd heq (by decide)

end DeepWiki
