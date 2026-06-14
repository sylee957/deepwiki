import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Set.Defs

/-! # Level sets
The level set `𝓘_{⋈x} = {t | f t ⋈ x}` of times where `f t` compares to a level
`x` under a relation — the book's unified `𝓘_{⋈x}` notation (`⋈ ∈ {<, ≤, ≥, >}`).
Relation-generic, with the admissible (`≥`) and strict (`<`) specializations
used by the pseudo-inverse. -/

namespace DeepWiki

variable {α β : Type*}

/-- The level set `𝓘_{⋈x} = {t | f t ⋈ x}` of times where `f t` compares to
the level `x` under the relation `r` (the book's unified `𝓘_{⋈x}` notation,
`⋈ ∈ {<, ≤, ≥, >}`). -/
def levelSet (r : β → β → Prop) (f : α → β) (x : β) : Set α :=
  {t : α | r (f t) x}

/-- `t ∈ levelSet r f x` iff `r (f t) x`. -/
theorem mem_levelSet {r : β → β → Prop} {f : α → β} {x : β} {t : α} :
    t ∈ levelSet r f x ↔ r (f t) x := Iff.rfl

/-- The admissible set `𝓘_{≥x} = {t | f t ≥ x}` of times. -/
abbrev levelGeSet [LE β] (f : α → β) (x : β) : Set α :=
  levelSet (· ≥ ·) f x

/-- The strict set `𝓘_{<x} = {t | f t < x}` of times. -/
abbrev levelLtSet [LT β] (f : α → β) (x : β) : Set α :=
  levelSet (· < ·) f x

/-- `t ∈ levelGeSet f x` iff `f t ≥ x`. -/
theorem mem_levelGeSet [LE β] {f : α → β} {x : β} {t : α} :
    t ∈ levelGeSet f x ↔ f t ≥ x := Iff.rfl

/-- `t ∈ levelLtSet f x` iff `f t < x`. -/
theorem mem_levelLtSet [LT β] {f : α → β} {x : β} {t : α} :
    t ∈ levelLtSet f x ↔ f t < x := Iff.rfl

end DeepWiki
