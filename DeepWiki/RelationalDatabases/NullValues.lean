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

end DeepWiki
