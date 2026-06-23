import DeepWiki.RelationalDatabases.RelationalAlgebra
import Mathlib.Data.Set.Lattice

/-! # Null-extended values and the information order
Incomplete information at the value level: a *null-extended tuple* (a Codd / V-table row) carries,
for each attribute, either a definite value or `none` (a null — "no information"). The *information
order* compares rows by definedness: `nt'` is at least as informative as `nt` when it is definite,
with the same value, wherever `nt` is. A definite tuple is a maximal (fully informative) row.

The representation of a null-table as the set of its definite completions, certain/possible answers,
and the Codd / V- / C-table systems (Thm 6.1–6.9) are layered on this carrier. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} {Ω Ω' : Finset Att}

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

/-- **Definition 6.2** (f-information): the tuples `f` certainly produces across a set of possible
instances — `X^f = ⋂_{r ∈ X} f r`, the certain answers of `f`. -/
def infoF (f : Table Ω Val → Table Ω' Val) (X : Set (Table Ω Val)) : Table Ω' Val :=
  ⋂ r ∈ X, f r

/-- A tuple is in the f-information iff it lies in `f r` for every possible world `r`. -/
theorem mem_infoF {f : Table Ω Val → Table Ω' Val} {X : Set (Table Ω Val)} {t : Tuple Ω' Val} :
    t ∈ infoF f X ↔ ∀ r ∈ X, t ∈ f r := by simp [infoF]

/-- More possible worlds give fewer certain answers. -/
theorem infoF_antitone (f : Table Ω Val → Table Ω' Val) {X Y : Set (Table Ω Val)} (h : X ⊆ Y) :
    infoF f Y ⊆ infoF f X := by
  intro t ht; rw [mem_infoF] at ht ⊢; exact fun r hr => ht r (h hr)

/-- The certain answers of a null-table are its identity f-information over the possible worlds. -/
theorem certainAnswer_iff_mem_infoF_id {T : NullTable Ω Val} {t : Tuple Ω Val} :
    CertainAnswer T t ↔ t ∈ infoF id (rep T) := by simp [CertainAnswer, mem_infoF]

/-- **Definition 6.2** (β-equivalence): two sets of instances yield the same f-information for every
operator in the family `ops` — the same certain answers for every `β`-expression. -/
def BetaEquiv (ops : Set (Σ Ω' : Finset Att, Table Ω Val → Table Ω' Val))
    (X Y : Set (Table Ω Val)) : Prop := ∀ p ∈ ops, infoF p.2 X = infoF p.2 Y

/-- β-equivalence is reflexive. -/
theorem BetaEquiv.refl (ops : Set (Σ Ω' : Finset Att, Table Ω Val → Table Ω' Val))
    (X : Set (Table Ω Val)) : BetaEquiv ops X X := fun _ _ => rfl

/-- β-equivalence is symmetric. -/
theorem BetaEquiv.symm {ops : Set (Σ Ω' : Finset Att, Table Ω Val → Table Ω' Val)}
    {X Y : Set (Table Ω Val)} (h : BetaEquiv ops X Y) : BetaEquiv ops Y X :=
  fun p hp => (h p hp).symm

/-- β-equivalence is transitive. -/
theorem BetaEquiv.trans {ops : Set (Σ Ω' : Finset Att, Table Ω Val → Table Ω' Val)}
    {X Y Z : Set (Table Ω Val)} (h₁ : BetaEquiv ops X Y) (h₂ : BetaEquiv ops Y Z) :
    BetaEquiv ops X Z := fun p hp => (h₁ p hp).trans (h₂ p hp)

/-- **Definition 6.2** (β-representation): a null-table `β`-represents `X` when its Codd-table
worlds are β-equivalent to `X`. -/
def BetaRepresents (ops : Set (Σ Ω' : Finset Att, Table Ω Val → Table Ω' Val))
    (T : NullTable Ω Val) (X : Set (Table Ω Val)) : Prop := BetaEquiv ops (coddRep T) X

/-- Every definite (null-free) row of a Codd table is a certain answer: it appears in every
open-world possible instance. -/
theorem mem_infoF_id_coddRep_of_toNull_mem {T : NullTable Ω Val} {t : Tuple Ω Val}
    (h : toNull t ∈ T) : t ∈ infoF id (coddRep T) := by
  rw [mem_infoF]
  intro r hr
  obtain ⟨t', ht', hmi⟩ := hr (toNull t) h
  rwa [toNull_injective ((moreInfo_toNull_iff t _).mp hmi)] at ht'

/-- The certain answers of a definite table are exactly the table itself (its identity
f-information over the possible worlds). -/
theorem infoF_id_rep_toNullTable [Inhabited Val] (r : Table Ω Val) :
    infoF id (rep (toNullTable r)) = r := by
  rw [rep_toNullTable]; simp [infoF]

end DeepWiki
