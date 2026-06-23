import DeepWiki.RelationalDatabases.FunctionalDependencies

/-! # Multivalued dependencies
A multivalued dependency `X ↠ Y` holds in a row set when, for any two rows agreeing on `X`,
the "tuple swap" on `Y` versus `Ω − Y` stays in the relation (Def 3.8) — equivalently, the
relation decomposes losslessly onto `X ∪ Y` and `X ∪ (Ω − Y)`. Two basic inference rules are
proved sound at the row-set level: every functional dependency is a multivalued dependency
(FM1) and multivalued dependencies are closed under complementation `Y ↦ Ω − Y` (M1).

The remaining axioms of the fd+mvd system (mvd-augmentation, mvd- and mixed pseudotransitivity),
the dependency basis, Algorithm 3.3 and the completeness of the axiom system are layered on
later. -/

namespace DeepWiki

universe u v

variable {Att : Type u} [DecidableEq Att] {Val : Type v} {Ω : Finset Att}

/-- A row set `r` satisfies the *multivalued dependency* `X ↠ Y` (Def 3.8): for any two rows
agreeing on `X`, there is a row agreeing with the first on `X ∪ Y` and with the second on
`X ∪ (Ω − Y)`. -/
def SatisfiesMvd (r : Table Ω Val) (X Y : Finset Att) : Prop :=
  ∀ t ∈ r, ∀ u ∈ r, Agree X t u →
    ∃ v ∈ r, Agree (X ∪ Y) v t ∧ Agree (X ∪ (Ω \ Y)) v u

variable {r : Table Ω Val} {X Y : Finset Att}

/-- Rule FM1 (Corollary 3.1): every functional dependency is a multivalued dependency —
`X → Y` implies `X ↠ Y`. The second row itself is the required witness. -/
theorem satisfiesMvd_of_satisfiesFd (h : SatisfiesFd r X Y) : SatisfiesMvd r X Y := by
  intro t ht u hu hag
  exact ⟨u, hu, agree_union.mpr ⟨hag.symm, (h t ht u hu hag).symm⟩, fun _ _ => rfl⟩

/-- Rule M1 (Corollary 3.1, complementation): `X ↠ Y` implies `X ↠ Ω − Y`. The witness for the
swapped pair `(u, t)` is the witness for `X ↠ Ω − Y` on `(t, u)`. -/
theorem satisfiesMvd_complement (h : SatisfiesMvd r X Y) : SatisfiesMvd r X (Ω \ Y) := by
  intro t ht u hu hag
  obtain ⟨v, hv, hvY, hvc⟩ := h u hu t ht hag.symm
  refine ⟨v, hv, hvc, Agree.mono ?_ hvY⟩
  intro a ha
  simp only [Finset.mem_union, Finset.mem_sdiff] at ha ⊢
  tauto

end DeepWiki
