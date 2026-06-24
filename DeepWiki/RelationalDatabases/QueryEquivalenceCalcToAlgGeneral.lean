import DeepWiki.RelationalDatabases.QueryEquivalenceCalcToAlg

/-! # Reduction of the tuple calculus to the algebra (§2.4): the general case via position tagging
The disjoint-context reduction (`QueryEquivalenceCalcToAlg`) assumes the variable schemes do not
clash. The book's general method (§2.4.1, Step 2) removes that assumption by *tagging* each
attribute with its tuple-variable's index: attribute `a` of the i-th context variable becomes
`(i, a)`. The product scheme is then clash-free by construction — different positions get different
tags — so two variables sharing a database scheme (e.g. both ranging over the same relation) no
longer collide, and an agreement atom becomes a genuine equality constraint between two tagged
copies (rather than the vacuous condition of the disjoint case).

This file builds the tagged product scheme; the tagged environment-flattening, lookup bridge,
translation and correctness are layered on it (mirroring the disjoint development). -/

namespace DeepWiki

universe u v w

variable {Att : Type u} [DecidableEq Att] {Val : Type v}

/-- *Position-tagged attributes* (§2.4.1, Step 2): attribute `a` of the i-th context variable is
`(i, a)`. Tagging makes the product scheme clash-free without assuming disjoint input schemes. -/
abbrev TagAtt (Att : Type u) : Type u := ℕ × Att

/-- Tag an attribute with position `0` (the innermost variable). -/
def tag0 : Att ↪ TagAtt Att := ⟨fun a => (0, a), fun _ _ h => by simpa using h⟩

/-- Shift every tag's position up by one (moving one variable deeper into the context). -/
def shiftTag : TagAtt Att ↪ TagAtt Att :=
  ⟨Prod.map Nat.succ id, fun _ _ h => by simpa [Prod.ext_iff, Nat.succ_inj] using h⟩

/-- The *tagged product scheme* of a context: the head variable's attributes tagged with `0`, the
rest shifted one position deeper. -/
def flattenTagged : Ctx Att → Finset (TagAtt Att)
  | [] => ∅
  | Ω :: Γ => Ω.map tag0 ∪ (flattenTagged Γ).map shiftTag

@[simp] theorem flattenTagged_nil : flattenTagged ([] : Ctx Att) = ∅ := rfl

@[simp] theorem flattenTagged_cons (Ω : Finset Att) (Γ : Ctx Att) :
    flattenTagged (Ω :: Γ) = Ω.map tag0 ∪ (flattenTagged Γ).map shiftTag := rfl

/-- The head variable's tags (position `0`) are disjoint from the deeper variables' tags (positions
`≥ 1`): the product scheme is clash-free by construction. -/
theorem flattenTagged_disjoint_head (Ω : Finset Att) (Γ : Ctx Att) :
    Disjoint (Ω.map tag0) ((flattenTagged Γ).map shiftTag) := by
  rw [Finset.disjoint_left]
  rintro p hp hq
  simp only [Finset.mem_map, tag0, shiftTag, Function.Embedding.coeFn_mk] at hp hq
  obtain ⟨a, _, rfl⟩ := hp
  obtain ⟨q', _, hq'⟩ := hq
  simp [Prod.ext_iff] at hq'

end DeepWiki
