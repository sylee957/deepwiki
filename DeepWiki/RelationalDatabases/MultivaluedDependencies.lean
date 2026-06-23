import DeepWiki.RelationalDatabases.FunctionalDependencies
import DeepWiki.RelationalDatabases.JoinDependencies

/-! # Multivalued dependencies
A multivalued dependency `X ↠ Y` holds in a row set when, for any two rows agreeing on `X`,
the "tuple swap" on `Y` versus `Ω − Y` stays in the relation (Def 3.8) — equivalently, the
relation decomposes losslessly onto `X ∪ Y` and `X ∪ (Ω − Y)`. The inference rules of the fd+mvd
system are proved sound at the row-set level: FD-implies-MVD (FM1), complementation (M1),
augmentation (M2), mvd-transitivity (M3), mixed pseudotransitivity (FM2), and the Lemma 3.1
derived rules union (M4), intersection (M5) and difference (M6).

The dependency basis, Algorithm 3.3 and the completeness of the axiom system are layered on
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

/-- An `X ↠ Y` witness `v` (agreeing with `t` on `X ∪ Y` and with `u` on `X ∪ (Ω − Y)`) agrees
with `t` on every attribute where `t` and `u` already agree. -/
theorem mvd_witness_agree {X Y : Finset Att} {t u v : Tuple Ω Val}
    (hvt : Agree (X ∪ Y) v t) (hvu : Agree (X ∪ (Ω \ Y)) v u)
    {a : {x // x ∈ Ω}} (ha : t a = u a) : v a = t a := by
  by_cases hY : a.val ∈ Y
  · exact hvt a (Finset.mem_union_right _ hY)
  · exact (hvu a (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨a.property, hY⟩))).trans ha.symm

/-- Rule M2 (Theorem 3.10, mvd-augmentation): `X ↠ Y` gives `W ∪ X ↠ V ∪ Y` when `V ⊆ W`. -/
theorem satisfiesMvd_augment {X Y W V : Finset Att} (hVW : V ⊆ W) (h : SatisfiesMvd r X Y) :
    SatisfiesMvd r (W ∪ X) (V ∪ Y) := by
  intro t ht u hu hag
  have hagX : Agree X t u := Agree.mono Finset.subset_union_right hag
  have hagW : Agree W t u := Agree.mono Finset.subset_union_left hag
  obtain ⟨v, hv, hvt, hvu⟩ := h t ht u hu hagX
  have hvtW : Agree W v t := fun a ha => mvd_witness_agree hvt hvu (hagW a ha)
  refine ⟨v, hv, ?_, ?_⟩
  · -- `Agree ((W ∪ X) ∪ (V ∪ Y)) v t`, reduced to `Agree (W ∪ (X ∪ Y)) v t`
    refine Agree.mono ?_ (agree_union.mpr ⟨hvtW, hvt⟩)
    intro a ha
    simp only [Finset.mem_union] at ha ⊢
    rcases ha with (hW | hX) | (hV | hY)
    · exact Or.inl hW
    · exact Or.inr (Or.inl hX)
    · exact Or.inl (hVW hV)
    · exact Or.inr (Or.inr hY)
  · -- `Agree ((W ∪ X) ∪ (Ω − (V ∪ Y))) v u`, reduced to `Agree (W ∪ (X ∪ (Ω − Y))) v u`
    have hvuW : Agree W v u := fun a ha => (hvtW a ha).trans (hagW a ha)
    refine Agree.mono ?_ (agree_union.mpr ⟨hvuW, hvu⟩)
    intro a ha
    simp only [Finset.mem_union, Finset.mem_sdiff] at ha ⊢
    rcases ha with (hW | hX) | ⟨haΩ, hnVY⟩
    · exact Or.inl hW
    · exact Or.inr (Or.inl hX)
    · exact Or.inr (Or.inr ⟨haΩ, fun hY => hnVY (Or.inr hY)⟩)

/-- Rule M3 (Theorem 3.10, mvd-transitivity): `X ↠ Y` and `Y ↠ Z` give `X ↠ (Z − Y)`. The witness
swaps onto `Y` (via `X ↠ Y`, on the pair `u, t`) and then onto `Z` (via `Y ↠ Z`). -/
theorem satisfiesMvd_trans {X Y Z : Finset Att} (hXY : SatisfiesMvd r X Y)
    (hYZ : SatisfiesMvd r Y Z) : SatisfiesMvd r X (Z \ Y) := by
  intro t ht u hu hag
  obtain ⟨a, ha, hau, hat⟩ := hXY u hu t ht hag.symm
  have haYu : Agree Y a u := Agree.mono Finset.subset_union_right hau
  obtain ⟨w, hw, hwa, hwu⟩ := hYZ a ha u hu haYu
  refine ⟨w, hw, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_union, Finset.mem_sdiff] at hb
    rcases hb with hX | ⟨hZ, hnY⟩
    · by_cases hYZb : b.val ∈ Y ∨ b.val ∈ Z
      · rw [hwa b (Finset.mem_union.mpr hYZb), hau b (Finset.mem_union.mpr (Or.inl hX))]
        exact (hag b hX).symm
      · push Not at hYZb
        rw [hwu b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hYZb.2⟩)))]
        exact (hag b hX).symm
    · rw [hwa b (Finset.mem_union.mpr (Or.inr hZ))]
      exact hat b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hnY⟩)))
  · intro b hb
    simp only [Finset.mem_union, Finset.mem_sdiff, not_and, not_not] at hb
    rcases hb with hX | ⟨hbΩ, hZY⟩
    · by_cases hYZb : b.val ∈ Y ∨ b.val ∈ Z
      · rw [hwa b (Finset.mem_union.mpr hYZb)]
        exact hau b (Finset.mem_union.mpr (Or.inl hX))
      · push Not at hYZb
        exact hwu b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hYZb.2⟩)))
    · by_cases hY : b.val ∈ Y
      · rw [hwa b (Finset.mem_union.mpr (Or.inl hY))]
        exact hau b (Finset.mem_union.mpr (Or.inr hY))
      · exact hwu b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hbΩ, fun hZ => hY (hZY hZ)⟩)))

/-- Rule FM2 (Theorem 3.10, mixed pseudotransitivity): `X ↠ Y` and `Y → Z` give `X → (Z − Y)`.
The `X ↠ Y` witness `w` agrees with `t` on `Y` (hence on `Z`, by the functional dependency) and
with `u` off `Y`, so `t` and `u` agree on `Z − Y`. -/
theorem satisfiesFd_of_mvd_fd {X Y Z : Finset Att} (hXY : SatisfiesMvd r X Y)
    (hYZ : SatisfiesFd r Y Z) : SatisfiesFd r X (Z \ Y) := by
  intro t ht u hu hag
  obtain ⟨w, hw, hwt, hwu⟩ := hXY t ht u hu hag
  have hwZ : Agree Z w t := hYZ w hw t ht (Agree.mono Finset.subset_union_right hwt)
  intro b hb
  rw [Finset.mem_sdiff] at hb
  have h2 : w b = u b :=
    hwu b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hb.2⟩)))
  exact (hwZ b hb.1).symm.trans h2

/-- Rule M4 (Lemma 3.1, mvd-union): `X ↠ Y` and `X ↠ Z` give `X ↠ (Y ∪ Z)`. Swap onto `Y` (via
`X ↠ Y`), then onto `Z` (via `X ↠ Z` on the swapped row and `t`). -/
theorem satisfiesMvd_union {X Y Z : Finset Att} (hXY : SatisfiesMvd r X Y)
    (hXZ : SatisfiesMvd r X Z) : SatisfiesMvd r X (Y ∪ Z) := by
  intro t ht u hu hag
  obtain ⟨a, ha, hat, hau⟩ := hXY t ht u hu hag
  have hXta : Agree X t a := (Agree.mono Finset.subset_union_left hat).symm
  obtain ⟨w, hw, hwt, hwa⟩ := hXZ t ht a ha hXta
  refine ⟨w, hw, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_union] at hb
    rcases hb with hX | hY | hZ
    · exact hwt b (Finset.mem_union.mpr (Or.inl hX))
    · by_cases hZb : b.val ∈ Z
      · exact hwt b (Finset.mem_union.mpr (Or.inr hZb))
      · rw [hwa b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hZb⟩)))]
        exact hat b (Finset.mem_union.mpr (Or.inr hY))
    · exact hwt b (Finset.mem_union.mpr (Or.inr hZ))
  · intro b hb
    simp only [Finset.mem_union, Finset.mem_sdiff, not_or] at hb
    rcases hb with hX | ⟨hbΩ, hnY, hnZ⟩
    · rw [hwt b (Finset.mem_union.mpr (Or.inl hX))]; exact hag b hX
    · rw [hwa b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hbΩ, hnZ⟩)))]
      exact hau b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hbΩ, hnY⟩)))

/-- Rule M5 (Lemma 3.1, mvd-intersection): `X ↠ Y` and `X ↠ Z` give `X ↠ (Y ∩ Z)`. -/
theorem satisfiesMvd_inter {X Y Z : Finset Att} (hXY : SatisfiesMvd r X Y)
    (hXZ : SatisfiesMvd r X Z) : SatisfiesMvd r X (Y ∩ Z) := by
  intro t ht u hu hag
  obtain ⟨a, ha, hat, hau⟩ := hXY t ht u hu hag
  have hXau : Agree X a u := Agree.mono Finset.subset_union_left hau
  obtain ⟨w, hw, hwa, hwu⟩ := hXZ a ha u hu hXau
  refine ⟨w, hw, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_union, Finset.mem_inter] at hb
    rcases hb with hX | ⟨hY, hZ⟩
    · by_cases hZb : b.val ∈ Z
      · rw [hwa b (Finset.mem_union.mpr (Or.inr hZb))]
        exact hat b (Finset.mem_union.mpr (Or.inl hX))
      · rw [hwu b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hZb⟩)))]
        exact (hag b hX).symm
    · rw [hwa b (Finset.mem_union.mpr (Or.inr hZ))]
      exact hat b (Finset.mem_union.mpr (Or.inr hY))
  · intro b hb
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, not_and] at hb
    rcases hb with hX | ⟨hbΩ, hYnZ⟩
    · by_cases hZb : b.val ∈ Z
      · rw [hwa b (Finset.mem_union.mpr (Or.inr hZb))]
        exact hau b (Finset.mem_union.mpr (Or.inl hX))
      · exact hwu b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hZb⟩)))
    · by_cases hZb : b.val ∈ Z
      · rw [hwa b (Finset.mem_union.mpr (Or.inr hZb))]
        exact hau b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hbΩ, fun hY => hYnZ hY hZb⟩)))
      · exact hwu b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hbΩ, hZb⟩)))

/-- Rule M6 (Lemma 3.1, mvd-difference): `X ↠ Y` and `X ↠ Z` give `X ↠ (Y − Z)`. -/
theorem satisfiesMvd_diff {X Y Z : Finset Att} (hXY : SatisfiesMvd r X Y)
    (hXZ : SatisfiesMvd r X Z) : SatisfiesMvd r X (Y \ Z) := by
  intro t ht u hu hag
  obtain ⟨a, ha, hat, hau⟩ := hXY t ht u hu hag
  have hXua : Agree X u a := (Agree.mono Finset.subset_union_left hau).symm
  obtain ⟨w, hw, hwu, hwa⟩ := hXZ u hu a ha hXua
  refine ⟨w, hw, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_union, Finset.mem_sdiff] at hb
    rcases hb with hX | ⟨hY, hnZ⟩
    · by_cases hZb : b.val ∈ Z
      · rw [hwu b (Finset.mem_union.mpr (Or.inr hZb))]; exact (hag b hX).symm
      · rw [hwa b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hZb⟩)))]
        exact hat b (Finset.mem_union.mpr (Or.inl hX))
    · rw [hwa b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hnZ⟩)))]
      exact hat b (Finset.mem_union.mpr (Or.inr hY))
  · intro b hb
    simp only [Finset.mem_union, Finset.mem_sdiff, not_and, not_not] at hb
    rcases hb with hX | ⟨hbΩ, hYZ⟩
    · by_cases hZb : b.val ∈ Z
      · exact hwu b (Finset.mem_union.mpr (Or.inr hZb))
      · rw [hwa b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨b.property, hZb⟩)))]
        exact hau b (Finset.mem_union.mpr (Or.inl hX))
    · by_cases hZb : b.val ∈ Z
      · exact hwu b (Finset.mem_union.mpr (Or.inr hZb))
      · rw [hwa b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hbΩ, hZb⟩)))]
        exact hau b (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hbΩ, fun hY => hZb (hYZ hY)⟩)))

/-- The two-component family `{X ∪ Y, X ∪ (Ω − Y)}` whose join dependency is the mvd `X ↠ Y`. -/
def mvdComp (X Y Ω : Finset Att) : Bool → Finset Att
  | false => X ∪ Y
  | true => X ∪ (Ω \ Y)

/-- **Theorem 3.9** (§3.3, p.86): a multivalued dependency is exactly a two-component join
dependency — `X ↠ Y` holds iff `r` decomposes losslessly onto `X ∪ Y` and `X ∪ (Ω − Y)`. -/
theorem satisfiesMvd_iff_satisfiesJd {X Y : Finset Att} :
    SatisfiesMvd r X Y ↔ SatisfiesJd r (mvdComp X Y Ω) := by
  have hsub : ∀ a : {x // x ∈ Ω}, a.val ∈ X ∪ Y → a.val ∈ X ∪ (Ω \ Y) → a.val ∈ X := by
    intro a h1 h2
    simp only [Finset.mem_union, Finset.mem_sdiff] at h1 h2
    tauto
  constructor
  · intro h t htr hpair
    have hagX : Agree X (t false) (t true) := fun a ha =>
      hpair false true a (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ ha, Finset.mem_union_left _ ha⟩)
    obtain ⟨v, hv, hvf, hvt⟩ := h (t false) (htr false) (t true) (htr true) hagX
    exact ⟨v, hv, fun i => by cases i with | false => exact hvf | true => exact hvt⟩
  · intro h t ht u hu hag
    have hmem : ∀ i, (fun b => bif b then u else t) i ∈ r := by
      intro i; cases i with | false => exact ht | true => exact hu
    have hpair : ∀ i j, Agree (mvdComp X Y Ω i ∩ mvdComp X Y Ω j)
        ((fun b => bif b then u else t) i) ((fun b => bif b then u else t) j) := by
      intro i j
      cases i <;> cases j
      · exact fun _ _ => rfl
      · exact fun a ha =>
          hag a (hsub a (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp ha).2)
      · exact fun a ha =>
          (hag a (hsub a (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp ha).1)).symm
      · exact fun _ _ => rfl
    obtain ⟨v, hv, hvi⟩ := h (fun b => bif b then u else t) hmem hpair
    exact ⟨v, hv, hvi false, hvi true⟩

end DeepWiki
