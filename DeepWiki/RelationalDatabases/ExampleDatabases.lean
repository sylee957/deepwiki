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

/-! ## Exercise 1.9 — a dynamic relation constraint not equivalent to relation constraints -/

/-- A dynamic relation constraint is *equivalent to relation constraints* when it factors as a
per-instance relation constraint holding at every step — its truth ignores the relationship
between consecutive instances. -/
def IsRelationConstraintEquivDyn {Att Val : Type} (R : RelScheme Att Val)
    (dc : DynRelConstraint R) : Prop :=
  ∃ rc : RelConstraint R.prim, ∀ seq, dc seq ↔ ∀ n, rc (seq n)

/-- The *monotone* dynamic relation constraint on `ex18Rel`: the relation only grows over time. -/
def ex18DynMono : DynRelConstraint ex18Rel := fun seq => ∀ n, seq n ⊆ seq (n + 1)

/-- **Exercise 1.9**: the monotone dynamic relation constraint is *not* equivalent to relation
constraints. It relates consecutive instances, so it cannot factor as a per-instance condition:
the growing sequence `∅, {a}, {a}, …` satisfies it, while the reordered `{a}, ∅, ∅, …` — built from
the same instances — does not, so no per-instance constraint could separate them. -/
theorem ex18DynMono_not_relationConstraintEquiv :
    ¬ IsRelationConstraintEquivDyn ex18Rel ex18DynMono := by
  rintro ⟨rc, h⟩
  set s1 : ℕ → Set (TupleOf ex18Scheme) := fun n => if n = 0 then ∅ else {tupA 1} with hs1
  set s2 : ℕ → Set (TupleOf ex18Scheme) := fun n => if n = 0 then {tupA 1} else ∅ with hs2
  have hmono1 : ex18DynMono s1 := by intro n; cases n <;> simp [hs1]
  have hall1 := (h s1).mp hmono1
  have hrcE : rc ∅ := by have := hall1 0; simpa [hs1] using this
  have hrcT : rc {tupA 1} := by have := hall1 1; simpa [hs1] using this
  have hall2 : ∀ n, rc (s2 n) := by
    intro n; cases n with
    | zero => simpa [hs2] using hrcT
    | succ m => simpa [hs2] using hrcE
  have hmono2 := (h s2).mpr hall2
  have hmem := hmono2 0 (show tupA 1 ∈ s2 0 by simp [hs2])
  simp [hs2] at hmem

/-! ## Exercise 1.10 — the `THIRSTY` database and its seven constraints
The classification of each constraint (to which of `SC_L`, `SC_V`, `SC_S`, `SDC` it belongs) is
recorded in each docstring. `SC_L` is empty: none of the seven constrain `LIKES` alone. -/

/-- Attributes of `LIKES`: a drinker and a beer he likes. -/
abbrev likesAttrs : Finset String := {"L-DRINKER", "L-BEER"}

/-- Attributes of `VISITS`: a drinker and a bar he visits. -/
abbrev visitsAttrs : Finset String := {"V-DRINKER", "V-BAR"}

/-- Attributes of `SERVES`: a bar and a beer it serves. -/
abbrev servesAttrs : Finset String := {"S-BAR", "S-BEER"}

/-- A `THIRSTY` database instance: the three relations `LIKES`, `VISITS`, `SERVES`. -/
structure ThirstyInst where
  /-- The `LIKES` relation: drinkers and the beers they like. -/
  likes : Set (Tuple likesAttrs String)
  /-- The `VISITS` relation: drinkers and the bars they visit. -/
  visits : Set (Tuple visitsAttrs String)
  /-- The `SERVES` relation: bars and the beers they serve. -/
  serves : Set (Tuple servesAttrs String)

/-- Drinker of a `LIKES` tuple. -/
def lDrinker (t : Tuple likesAttrs String) : String := t ⟨"L-DRINKER", by decide⟩

/-- Beer of a `LIKES` tuple. -/
def lBeer (t : Tuple likesAttrs String) : String := t ⟨"L-BEER", by decide⟩

/-- Drinker of a `VISITS` tuple. -/
def vDrinker (t : Tuple visitsAttrs String) : String := t ⟨"V-DRINKER", by decide⟩

/-- Bar of a `VISITS` tuple. -/
def vBar (t : Tuple visitsAttrs String) : String := t ⟨"V-BAR", by decide⟩

/-- Bar of a `SERVES` tuple. -/
def sBar (t : Tuple servesAttrs String) : String := t ⟨"S-BAR", by decide⟩

/-- Beer of a `SERVES` tuple. -/
def sBeer (t : Tuple servesAttrs String) : String := t ⟨"S-BEER", by decide⟩

/-- **Exercise 1.10**, constraint 1 (`SDC`): every drinker visits only bars where some beer he
likes is served. -/
def thirsty_c1 (db : ThirstyInst) : Prop :=
  ∀ v ∈ db.visits, ∃ l ∈ db.likes, ∃ s ∈ db.serves,
    lDrinker l = vDrinker v ∧ sBar s = vBar v ∧ lBeer l = sBeer s

/-- **Exercise 1.10**, constraint 2 (`SC_S`): each bar serves at least one beer. -/
def thirsty_c2 (bars : Set String) (db : ThirstyInst) : Prop :=
  ∀ bar ∈ bars, ∃ s ∈ db.serves, sBar s = bar

/-- **Exercise 1.10**, constraint 3 (`SC_V`): each bar has at least one visitor. -/
def thirsty_c3 (bars : Set String) (db : ThirstyInst) : Prop :=
  ∀ bar ∈ bars, ∃ v ∈ db.visits, vBar v = bar

/-- **Exercise 1.10**, constraint 4 (`SDC`): each bar only serves beers that are liked by some of
its visitors. -/
def thirsty_c4 (db : ThirstyInst) : Prop :=
  ∀ s ∈ db.serves, ∃ v ∈ db.visits, ∃ l ∈ db.likes,
    vBar v = sBar s ∧ vDrinker v = lDrinker l ∧ lBeer l = sBeer s

/-- **Exercise 1.10**, constraint 5 (`SDC`): if two drinkers visit the same bar, some beer is
liked by both of them and served at the bar. -/
def thirsty_c5 (db : ThirstyInst) : Prop :=
  ∀ v₁ ∈ db.visits, ∀ v₂ ∈ db.visits, vBar v₁ = vBar v₂ →
    ∃ beer : String, (∃ l₁ ∈ db.likes, lDrinker l₁ = vDrinker v₁ ∧ lBeer l₁ = beer) ∧
      (∃ l₂ ∈ db.likes, lDrinker l₂ = vDrinker v₂ ∧ lBeer l₂ = beer) ∧
      (∃ s ∈ db.serves, sBar s = vBar v₁ ∧ sBeer s = beer)

/-- **Exercise 1.10**, constraint 6 (`SDC`): if a drinker does not visit a bar, the bar serves at
least one beer he does not like. -/
def thirsty_c6 (drinkers bars : Set String) (db : ThirstyInst) : Prop :=
  ∀ d ∈ drinkers, ∀ bar ∈ bars,
    (¬ ∃ v ∈ db.visits, vDrinker v = d ∧ vBar v = bar) →
    ∃ s ∈ db.serves, sBar s = bar ∧ ¬ ∃ l ∈ db.likes, lDrinker l = d ∧ lBeer l = sBeer s

/-- **Exercise 1.10**, constraint 7 (`SDC`): if a drinker likes a beer served in a bar visited by
another drinker, then the two drinkers visit a common bar. -/
def thirsty_c7 (db : ThirstyInst) : Prop :=
  ∀ l ∈ db.likes, ∀ s ∈ db.serves, ∀ v ∈ db.visits,
    lBeer l = sBeer s → sBar s = vBar v →
    ∃ v₁ ∈ db.visits, ∃ v₂ ∈ db.visits,
      vDrinker v₁ = lDrinker l ∧ vDrinker v₂ = vDrinker v ∧ vBar v₁ = vBar v₂

/-! ## Example 1.8 — `SDYDC` dynamic database constraints (Exercise 1.4)
The four dynamic database constraints of `DYHOTELDB = (HOTELDB, SDYDC)`, as predicates on a
database evolution (a sequence of instances). Only the components each constraint mentions are
read; values are integers (dates, room and visitor numbers; the `PAID?` flag is `1` = paid). -/

/-- Attributes of `VISITORS`. -/
abbrev visitorsAttrs : Finset String :=
  {"VIS-NUMBER", "VIS-NAME", "VIS-STREET", "VIS-CITY", "VIS-COUNTRY"}

/-- Attributes of `STAYS`. -/
abbrev staysAttrs : Finset String :=
  {"VIS-NUMBER", "ARRIV-DATE", "LEAV-DATE", "ROOM-STAY", "NUMBER-OF-ACCOMP-PERSONS", "BILL"}

/-- Attributes of `PHONE-BILLS`. -/
abbrev phoneBillsAttrs : Finset String :=
  {"ROOM-NB", "TIME", "DATE", "DESTINATION", "PHBILL", "PAID?"}

/-- Attributes of `ROOMS` (raw-tuple form for the hotel database bundle). -/
abbrev hotelRoomsAttrs : Finset String := {"RN", "NOB", "BATH", "FLOOR", "RATE"}

/-- Visitor number of a `VISITORS` tuple. -/
def visNum (t : Tuple visitorsAttrs ℤ) : ℤ := t ⟨"VIS-NUMBER", by decide⟩

/-- Visitor number of a `STAYS` tuple. -/
def stayVisNum (t : Tuple staysAttrs ℤ) : ℤ := t ⟨"VIS-NUMBER", by decide⟩

/-- Leave date of a `STAYS` tuple. -/
def leavDate (t : Tuple staysAttrs ℤ) : ℤ := t ⟨"LEAV-DATE", by decide⟩

/-- Room of a `STAYS` tuple. -/
def roomStay (t : Tuple staysAttrs ℤ) : ℤ := t ⟨"ROOM-STAY", by decide⟩

/-- Room number of a `PHONE-BILLS` tuple. -/
def pbRoom (t : Tuple phoneBillsAttrs ℤ) : ℤ := t ⟨"ROOM-NB", by decide⟩

/-- Paid flag of a `PHONE-BILLS` tuple (`1` = paid). -/
def pbPaid (t : Tuple phoneBillsAttrs ℤ) : ℤ := t ⟨"PAID?", by decide⟩

/-- Room number of a `ROOMS` tuple. -/
def hrRoomNum (t : Tuple hotelRoomsAttrs ℤ) : ℤ := t ⟨"RN", by decide⟩

/-- Bath flag of a `ROOMS` tuple (`1` = has a bath). -/
def hrBath (t : Tuple hotelRoomsAttrs ℤ) : ℤ := t ⟨"BATH", by decide⟩

/-- Attributes of `EMPLOYEES`. -/
abbrev employeesAttrs : Finset String := {"EMPLOYEE-NUMBER", "EMPLOYEE-NAME", "JOB", "SALARY"}

/-- Attributes of `ROOMMAIDS` (full-name form for the hotel database bundle). -/
abbrev hotelRoommaidsAttrs : Finset String := {"ROOMMAID-NUMBER", "ROOM-NUMBER"}

/-- City of a `VISITORS` tuple. -/
def visCity (t : Tuple visitorsAttrs ℤ) : ℤ := t ⟨"VIS-CITY", by decide⟩

/-- Country of a `VISITORS` tuple. -/
def visCountry (t : Tuple visitorsAttrs ℤ) : ℤ := t ⟨"VIS-COUNTRY", by decide⟩

/-- Arrival date of a `STAYS` tuple. -/
def arrivDate (t : Tuple staysAttrs ℤ) : ℤ := t ⟨"ARRIV-DATE", by decide⟩

/-- Time of a `PHONE-BILLS` tuple. -/
def pbTime (t : Tuple phoneBillsAttrs ℤ) : ℤ := t ⟨"TIME", by decide⟩

/-- Date of a `PHONE-BILLS` tuple. -/
def pbDate (t : Tuple phoneBillsAttrs ℤ) : ℤ := t ⟨"DATE", by decide⟩

/-- Number of an `EMPLOYEES` tuple. -/
def empNum (t : Tuple employeesAttrs ℤ) : ℤ := t ⟨"EMPLOYEE-NUMBER", by decide⟩

/-- Job of an `EMPLOYEES` tuple. -/
def empJob (t : Tuple employeesAttrs ℤ) : ℤ := t ⟨"JOB", by decide⟩

/-- Roommaid number of a `ROOMMAIDS` tuple. -/
def rmNum (t : Tuple hotelRoommaidsAttrs ℤ) : ℤ := t ⟨"ROOMMAID-NUMBER", by decide⟩

/-- Room number of a `ROOMMAIDS` tuple. -/
def rmRoom (t : Tuple hotelRoommaidsAttrs ℤ) : ℤ := t ⟨"ROOM-NUMBER", by decide⟩

/-- A `HOTELDB` database instance: its six relations. -/
structure HotelDbInst where
  /-- The `ROOMS` relation. -/
  rooms : Set (Tuple hotelRoomsAttrs ℤ)
  /-- The `ROOMMAIDS` relation. -/
  roommaids : Set (Tuple hotelRoommaidsAttrs ℤ)
  /-- The `VISITORS` relation. -/
  visitors : Set (Tuple visitorsAttrs ℤ)
  /-- The `STAYS` relation. -/
  stays : Set (Tuple staysAttrs ℤ)
  /-- The `PHONE-BILLS` relation. -/
  phoneBills : Set (Tuple phoneBillsAttrs ℤ)
  /-- The `EMPLOYEES` relation. -/
  employees : Set (Tuple employeesAttrs ℤ)

/-- **Exercise 1.4**, SDYDC constraint 1: no visitor may be deleted while `STAYS` still holds
information about him — a deleted visitor has no remaining stay. -/
def sdydc_noDeleteWithStay (seq : ℕ → HotelDbInst) : Prop :=
  ∀ n, ∀ vis ∈ (seq n).visitors,
    (∀ vis' ∈ (seq (n + 1)).visitors, visNum vis' ≠ visNum vis) →
    (∀ stay ∈ (seq (n + 1)).stays, stayVisNum stay ≠ visNum vis)

/-- **Exercise 1.4**, SDYDC constraint 2: all the phone bills of a visitor must be paid when he
leaves — when a stay is removed, every phone bill for that room is paid. -/
def sdydc_billsPaidOnLeave (seq : ℕ → HotelDbInst) : Prop :=
  ∀ n, ∀ stay ∈ (seq n).stays, stay ∉ (seq (n + 1)).stays →
    ∀ pb ∈ (seq n).phoneBills, pbRoom pb = roomStay stay → pbPaid pb = 1

/-- **Exercise 1.4**, SDYDC constraint 3: a bath must not be removed from a room (rooms may,
however, be annulled). -/
def sdydc_noBathRemoval (seq : ℕ → HotelDbInst) : Prop :=
  ∀ n, ∀ room ∈ (seq n).rooms, ∀ room' ∈ (seq (n + 1)).rooms,
    hrRoomNum room = hrRoomNum room' → hrBath room = 1 → hrBath room' = 1

/-- **Exercise 1.4**, SDYDC constraint 4: only the stay with the oldest `LEAV-DATE` may be removed
from `STAYS` — a removed stay has the minimum leave date. -/
def sdydc_onlyOldestRemoved (seq : ℕ → HotelDbInst) : Prop :=
  ∀ n, ∀ stay ∈ (seq n).stays, stay ∉ (seq (n + 1)).stays →
    ∀ stay' ∈ (seq n).stays, leavDate stay ≤ leavDate stay'

/-! ## Exercise 1.11 — consequences among the `THIRSTY` constraints
Two consequences are established below: `c2` follows from `c1 ∧ c3`, and dually `c3` from
`c2 ∧ c4`. (Constraints 5, 6, 7 are not derived from the others here.) -/

/-- **Exercise 1.11**: constraint 2 is a consequence of constraints 1 and 3. If every bar has a
visitor (`c3`) and every visitor likes some beer served at the bar he visits (`c1`), then every
bar serves a beer (`c2`). -/
theorem thirsty_c2_of_c1_c3 {bars : Set String} {db : ThirstyInst}
    (h1 : thirsty_c1 db) (h3 : thirsty_c3 bars db) : thirsty_c2 bars db := by
  intro bar hbar
  obtain ⟨v, hv, hvbar⟩ := h3 bar hbar
  obtain ⟨_, _, s, hs, _, hsbar, _⟩ := h1 v hv
  exact ⟨s, hs, hsbar.trans hvbar⟩

/-- **Exercise 1.11**: constraint 3 is a consequence of constraints 2 and 4. If every bar serves a
beer (`c2`) and every served beer is liked by some visitor of the bar (`c4`), then every bar has a
visitor (`c3`). -/
theorem thirsty_c3_of_c2_c4 {bars : Set String} {db : ThirstyInst}
    (h2 : thirsty_c2 bars db) (h4 : thirsty_c4 db) : thirsty_c3 bars db := by
  intro bar hbar
  obtain ⟨s, hs, hsbar⟩ := h2 bar hbar
  obtain ⟨v, hv, _, _, hvbar, _, _⟩ := h4 s hs
  exact ⟨v, hv, hvbar.trans hsbar⟩

/-! ## Example 1.10 — `HOTELDB` constraints (Exercise 1.6)
Boolean functions for every constraint set of `HOTELDB`. `SC_C` (`ROOMMAIDS`) is Exercise 1.2 and
`SDYDC` is Exercise 1.4 above; the remaining sets `SC_R`, `SC_V`, `SC_S`, `SC_P`, `SC_E` and `SDC`
follow. Per Example 1.9, the `SC_R` floor-digit, floor-2-bath and bath-cost constraints are tuple
constraints; uniqueness, the per-floor count and the bed average are not. -/

/-- First (most significant) decimal digit of a natural number. -/
def firstDigit : ℕ → ℕ
  | n => if h : n < 10 then n else firstDigit (n / 10)
  decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Number of beds of a `ROOMS` tuple. -/
def hrBeds (t : Tuple hotelRoomsAttrs ℤ) : ℤ := t ⟨"NOB", by decide⟩

/-- Floor of a `ROOMS` tuple. -/
def hrFloor (t : Tuple hotelRoomsAttrs ℤ) : ℤ := t ⟨"FLOOR", by decide⟩

/-- Rate of a `ROOMS` tuple. -/
def hrRate (t : Tuple hotelRoomsAttrs ℤ) : ℤ := t ⟨"RATE", by decide⟩

/-- **Exercise 1.6**, `SC_R`/1: every room has a different room number. -/
def rooms_uniqueNumber (r : Set (Tuple hotelRoomsAttrs ℤ)) : Prop :=
  ∀ t₁ ∈ r, ∀ t₂ ∈ r, hrRoomNum t₁ = hrRoomNum t₂ → t₁ = t₂

/-- **Exercise 1.6**, `SC_R`/2 (tuple constraint): there are only eight floors and the first digit
of the room number indicates the floor. -/
def rooms_floorDigit (r : Set (Tuple hotelRoomsAttrs ℤ)) : Prop :=
  ∀ t ∈ r, 1 ≤ hrFloor t ∧ hrFloor t ≤ 8 ∧ hrFloor t = (firstDigit (hrRoomNum t).toNat : ℤ)

/-- **Exercise 1.6**, `SC_R`/3 (tuple constraint): every room on floor 2 has a bath. -/
def rooms_floor2Bath (r : Set (Tuple hotelRoomsAttrs ℤ)) : Prop :=
  ∀ t ∈ r, hrFloor t = 2 → hrBath t = 1

/-- **Exercise 1.6**, `SC_R`/4 (tuple constraint): a room with a bath costs over 150. -/
def rooms_bathRate (r : Set (Tuple hotelRoomsAttrs ℤ)) : Prop :=
  ∀ t ∈ r, hrBath t = 1 → 150 < hrRate t

/-- **Exercise 1.6**, `SC_R`/5: no floor has more than 20 rooms. -/
def rooms_floorCount (r : Set (Tuple hotelRoomsAttrs ℤ)) : Prop :=
  ∀ fl : ℤ, {t | t ∈ r ∧ hrFloor t = fl}.ncard ≤ 20

/-- **Exercise 1.6**, `SC_R`/6: the average number of beds per room is at least `1.60`
(`5 · Σ beds ≥ 8 · #rooms`, the division-free form of `Σ beds / #rooms ≥ 8/5`). -/
def rooms_bedAverage (r : Set (Tuple hotelRoomsAttrs ℤ)) : Prop :=
  8 * (r.ncard : ℤ) ≤ 5 * ∑ᶠ t ∈ r, hrBeds t

/-- **Exercise 1.6**, `SC_V`/1: every visitor has a different number. -/
def visitors_uniqueNumber (r : Set (Tuple visitorsAttrs ℤ)) : Prop :=
  ∀ t₁ ∈ r, ∀ t₂ ∈ r, visNum t₁ = visNum t₂ → t₁ = t₂

/-- **Exercise 1.6**, `SC_V`/2: if two visitors live in the same city, they live in the same
country. -/
def visitors_cityCountry (r : Set (Tuple visitorsAttrs ℤ)) : Prop :=
  ∀ t₁ ∈ r, ∀ t₂ ∈ r, visCity t₁ = visCity t₂ → visCountry t₁ = visCountry t₂

/-- **Exercise 1.6**, `SC_S`/1: a visitor leaves on a later date than his arrival. -/
def stays_leaveAfterArrival (r : Set (Tuple staysAttrs ℤ)) : Prop :=
  ∀ t ∈ r, arrivDate t < leavDate t

/-- **Exercise 1.6**, `SC_S`/2: a visitor cannot arrive a second time while he is still staying —
two stays of one visitor whose arrivals fall within one another coincide. -/
def stays_noSecondArrival (r : Set (Tuple staysAttrs ℤ)) : Prop :=
  ∀ t₁ ∈ r, ∀ t₂ ∈ r, stayVisNum t₁ = stayVisNum t₂ →
    arrivDate t₁ ≤ arrivDate t₂ → arrivDate t₂ < leavDate t₁ → t₁ = t₂

/-- **Exercise 1.6**, `SC_P`: no two different phone bills agree on room number, time and date. -/
def phoneBills_key (r : Set (Tuple phoneBillsAttrs ℤ)) : Prop :=
  ∀ t₁ ∈ r, ∀ t₂ ∈ r,
    pbRoom t₁ = pbRoom t₂ → pbTime t₁ = pbTime t₂ → pbDate t₁ = pbDate t₂ → t₁ = t₂

/-- **Exercise 1.6**, `SC_E`: all employees have a different number. -/
def employees_uniqueNumber (r : Set (Tuple employeesAttrs ℤ)) : Prop :=
  ∀ t₁ ∈ r, ∀ t₂ ∈ r, empNum t₁ = empNum t₂ → t₁ = t₂

/-- **Exercise 1.6**, `SDC`/1: just one roommaid is responsible for each room of the hotel. -/
def sdc_oneRoommaidPerRoom (db : HotelDbInst) : Prop :=
  ∀ room ∈ db.rooms, ∃ rm ∈ db.roommaids, rmRoom rm = hrRoomNum room ∧
    ∀ rm' ∈ db.roommaids, rmRoom rm' = hrRoomNum room → rmNum rm' = rmNum rm

/-- **Exercise 1.6**, `SDC`/2: the rooms where visitors stay are rooms of the hotel. -/
def sdc_staysRoomsAreHotel (db : HotelDbInst) : Prop :=
  ∀ s ∈ db.stays, ∃ room ∈ db.rooms, hrRoomNum room = roomStay s

/-- **Exercise 1.6**, `SDC`/3: the room numbers occurring in `PHONE-BILLS` are rooms of the
hotel. -/
def sdc_phoneRoomsAreHotel (db : HotelDbInst) : Prop :=
  ∀ pb ∈ db.phoneBills, ∃ room ∈ db.rooms, hrRoomNum room = pbRoom pb

/-- **Exercise 1.6**, `SDC`/4: if there is a phone call from a room then that room was occupied on
that date. -/
def sdc_phoneImpliesOccupied (db : HotelDbInst) : Prop :=
  ∀ pb ∈ db.phoneBills, ∃ s ∈ db.stays,
    roomStay s = pbRoom pb ∧ arrivDate s ≤ pbDate pb ∧ pbDate pb ≤ leavDate s

/-- **Exercise 1.6**, `SDC`/5: each roommaid in `ROOMMAIDS` is an employee whose job
(`roommaidJob`) is roommaid. -/
def sdc_roommaidIsEmployee (roommaidJob : ℤ) (db : HotelDbInst) : Prop :=
  ∀ rm ∈ db.roommaids, ∃ e ∈ db.employees, empNum e = rmNum rm ∧ empJob e = roommaidJob

end DeepWiki
