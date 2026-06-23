import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # Null-extended values and the information order
Incomplete information at the value level: a *null-extended tuple* (a Codd / V-table row) carries,
for each attribute, either a definite value or `none` (a null — "no information"). The *information
order* compares rows by definedness: `nt'` is at least as informative as `nt` when it is definite,
with the same value, wherever `nt` is. A definite tuple is a maximal (fully informative) row.

The representation of a null-table as the set of its definite completions, certain/possible answers,
and the Codd / V- / C-table systems (Thm 6.1–6.9) are layered on this carrier. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} {Ω : Finset Att}

/-- A *null-extended tuple* (Codd / V-table row): each attribute carries a value or `none` (null). -/
abbrev NullTuple (Ω : Finset Att) (Val : Type v) : Type _ := Tuple Ω (Option Val)

/-- A *null-extended table*: a set of null-extended tuples. -/
abbrev NullTable (Ω : Finset Att) (Val : Type v) : Type _ := Set (NullTuple Ω Val)

/-- The *information order*: `nt'` is at least as informative as `nt` — definite, with the same
value, wherever `nt` is definite. -/
def MoreInfo (nt nt' : NullTuple Ω Val) : Prop := ∀ a (v : Val), nt a = some v → nt' a = some v

/-- The information order is reflexive. -/
theorem MoreInfo.refl (nt : NullTuple Ω Val) : MoreInfo nt nt := fun _ _ h => h

/-- The information order is transitive. -/
theorem MoreInfo.trans {nt nt' nt'' : NullTuple Ω Val} (h₁ : MoreInfo nt nt')
    (h₂ : MoreInfo nt' nt'') : MoreInfo nt nt'' := fun a v h => h₂ a v (h₁ a v h)

/-- The information order is antisymmetric: rows informative in both directions are equal. -/
theorem MoreInfo.antisymm {nt nt' : NullTuple Ω Val} (h₁ : MoreInfo nt nt')
    (h₂ : MoreInfo nt' nt) : nt = nt' := by
  funext a
  rcases hv : nt a with _ | v
  · rcases hv' : nt' a with _ | w
    · rfl
    · exact absurd (h₂ a w hv') (by rw [hv]; simp)
  · exact (h₁ a v hv).symm

/-- The total (null-free) null-tuple of a definite tuple. -/
def toNull (t : Tuple Ω Val) : NullTuple Ω Val := fun a => some (t a)

/-- A definite tuple's total row is maximally informative: nothing is strictly more informative —
any more-informative null-tuple equals it. -/
theorem moreInfo_toNull_iff (t : Tuple Ω Val) (nt : NullTuple Ω Val) :
    MoreInfo (toNull t) nt ↔ nt = toNull t := by
  constructor
  · intro h; funext a; exact h a (t a) rfl
  · rintro rfl; exact MoreInfo.refl _

/-- The *representation* of a null-table (its set of possible definite worlds): the definite tables
obtained by completing each null row to a definite tuple (filling its nulls), then taking the image.
This is the possible-worlds semantics underlying Def 6.1's representation systems. -/
def rep (T : NullTable Ω Val) : Set (Table Ω Val) :=
  {r | ∃ f : NullTuple Ω Val → Tuple Ω Val,
    (∀ nt ∈ T, MoreInfo nt (toNull (f nt))) ∧ r = f '' T}

/-- A *possible answer*: a tuple present in some possible world. -/
def PossibleAnswer (T : NullTable Ω Val) (t : Tuple Ω Val) : Prop := ∃ r ∈ rep T, t ∈ r

/-- A *certain answer*: a tuple present in every possible world. -/
def CertainAnswer (T : NullTable Ω Val) (t : Tuple Ω Val) : Prop := ∀ r ∈ rep T, t ∈ r

/-- The representation is nonempty: filling every null with a default value gives a possible
world. -/
theorem rep_nonempty [Inhabited Val] (T : NullTable Ω Val) : (rep T).Nonempty := by
  refine ⟨_, (fun nt a => (nt a).getD default), ?_, rfl⟩
  intro nt _ a v h
  simp [toNull, h]

/-- Every certain answer is a possible answer (the representation being nonempty). -/
theorem certainAnswer_imp_possibleAnswer [Inhabited Val] {T : NullTable Ω Val} {t : Tuple Ω Val}
    (h : CertainAnswer T t) : PossibleAnswer T t := by
  obtain ⟨r, hr⟩ := rep_nonempty T
  exact ⟨r, hr, h r hr⟩

/-- The null-table of a definite table (every row total). -/
def toNullTable (r : Table Ω Val) : NullTable Ω Val := toNull '' r

/-- `toNull` is injective. -/
theorem toNull_injective : Function.Injective (toNull : Tuple Ω Val → NullTuple Ω Val) :=
  fun _ _ h => funext fun a => Option.some_injective _ (congrFun h a)

/-- A definite table represents exactly itself: its only possible world is itself — the null-free
embedding is faithful. -/
theorem rep_toNullTable [Inhabited Val] (r : Table Ω Val) : rep (toNullTable r) = {r} := by
  ext r'
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    ext t
    simp only [toNullTable, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨t₀, ht₀, rfl⟩, rfl⟩
      rwa [toNull_injective ((moreInfo_toNull_iff t₀ _).mp (hf (toNull t₀) ⟨t₀, ht₀, rfl⟩))]
    · intro ht
      exact ⟨toNull t, ⟨t, ht, rfl⟩,
        toNull_injective ((moreInfo_toNull_iff t _).mp (hf (toNull t) ⟨t, ht, rfl⟩))⟩
  · rintro rfl
    refine ⟨fun nt a => (nt a).getD default, fun nt _ a v h => by simp [toNull, h], ?_⟩
    ext t
    simp only [toNullTable, Set.mem_image]
    constructor
    · intro ht
      exact ⟨toNull t, ⟨t, ht, rfl⟩, by funext a; simp [toNull]⟩
    · rintro ⟨_, ⟨t₀, ht₀, rfl⟩, rfl⟩
      simpa [toNull] using ht₀

/-- **Codd-table representation** (Theorem 6.1): the instances `r` in which every null row of `T`
has a refinement — a more-informative definite row `t ∈ r`. This is the open-world possible-worlds
semantics the book uses for `Rep`. -/
def coddRep (T : NullTable Ω Val) : Set (Table Ω Val) :=
  {r | ∀ nt ∈ T, ∃ t ∈ r, MoreInfo nt (toNull t)}

/-- Every closed possible world is a Codd-table world: a completion `f '' T` refines every row. -/
theorem rep_subset_coddRep (T : NullTable Ω Val) : rep T ⊆ coddRep T := by
  rintro r ⟨f, hf, rfl⟩
  intro nt hnt
  exact ⟨f nt, ⟨nt, hnt, rfl⟩, hf nt hnt⟩

/-- **Selection rule for Codd tables** (Theorem 6.3, the `σ`-rule): keep a null row only when the
condition is *certainly* true — true on every definite refinement (every way of filling its
nulls). -/
def selectCertain (P : Tuple Ω Val → Prop) (T : NullTable Ω Val) : NullTable Ω Val :=
  {nt ∈ T | ∀ t, MoreInfo nt (toNull t) → P t}

/-- Certain-selection only removes rows. -/
theorem selectCertain_subset (P : Tuple Ω Val → Prop) (T : NullTable Ω Val) :
    selectCertain P T ⊆ T := fun _ h => h.1

/-- A definite (null-free) row kept by certain-selection satisfies the condition. -/
theorem selectCertain_definite {P : Tuple Ω Val → Prop} {T : NullTable Ω Val} {t : Tuple Ω Val}
    (h : toNull t ∈ selectCertain P T) : P t :=
  h.2 t (MoreInfo.refl _)

end DeepWiki
