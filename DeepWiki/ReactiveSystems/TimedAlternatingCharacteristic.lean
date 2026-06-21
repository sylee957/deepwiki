import DeepWiki.ReactiveSystems.TimedHmlMutualRecursion

/-! # A multi-location characteristic formula via mutual recursion
A two-location timed automaton that single-variable `MtR` cannot characterise: the
action `a` alternates the location, with a *different* guard at each — `x ≤ 1` at
`ℓ0`, `x ≤ 2` at `ℓ1` — resetting the clock, with free delays. The two locations are
not timed bisimilar (at `x = 1.5`, `ℓ1` can still fire `a`, `ℓ0` cannot), so the
characteristic formula needs two mutually-recursive variables `X0`, `X1`:
`X0 =ν (y ≤ 1 ⇒ ⟨a⟩(y in X1)) ∧ [a](y ≤ 1 ∧ y in X1) ∧ ∀∀X0` and the dual `X1` with
bound `2` referencing `X0`. We prove soundness: every state timed bisimilar to `ℓ0`
(resp. `ℓ1`) at clock `d` satisfies `X0` (resp. `X1`) with formula clock `y = d`. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-! ### The alternating two-location automaton -/

/-- States of the alternating automaton: location `ℓ0` or `ℓ1`, each with a clock value. -/
inductive Alt
  | L0 (d : ℝ≥0)
  | L1 (d : ℝ≥0)

/-- SOS: `a` fires from `ℓ0` while `x ≤ 1` (to `ℓ1`, resetting), from `ℓ1` while
`x ≤ 2` (to `ℓ0`, resetting); time elapses freely in either location. -/
inductive AltStep : Alt → (Unit ⊕ ℝ≥0) → Alt → Prop
  /-- `ℓ0 —a→ ℓ1` (reset) while `x ≤ 1`. -/
  | a0 {d : ℝ≥0} (h : d ≤ 1) : AltStep (.L0 d) (Sum.inl ()) (.L1 0)
  /-- `ℓ1 —a→ ℓ0` (reset) while `x ≤ 2`. -/
  | a1 {d : ℝ≥0} (h : d ≤ 2) : AltStep (.L1 d) (Sum.inl ()) (.L0 0)
  /-- `ℓ0` delays freely. -/
  | delay0 (d t : ℝ≥0) : AltStep (.L0 d) (Sum.inr t) (.L0 (d + t))
  /-- `ℓ1` delays freely. -/
  | delay1 (d t : ℝ≥0) : AltStep (.L1 d) (Sum.inr t) (.L1 (d + t))

/-- The alternating automaton as a TLTS (states carry the clock value). -/
def altTLTS : TLTS Alt Unit := ⟨AltStep⟩

@[simp] theorem alt_act {q q' : Alt} : altTLTS.act q () q' ↔ AltStep q (Sum.inl ()) q' := Iff.rfl

@[simp] theorem alt_delay {q q' : Alt} {t : ℝ≥0} :
    altTLTS.delay q t q' ↔ AltStep q (Sum.inr t) q' := Iff.rfl

/-! ### The mutually-recursive characteristic equation system -/

/-- The body of variable `X0` (location `ℓ0`, bound `1`): `(y ≤ 1 ⇒ ⟨a⟩(y in X1)) ∧
[a](y ≤ 1 ∧ y in X1) ∧ ∀∀X0`, the implication written `y > 1 ∨ ⟨a⟩(y in X1)`. References
`X1` across the action and `X0` across delays. -/
def altBody0 : MtRSys Bool Unit Unit :=
  .and
    (.and
      (.or (.guard (.atom () .gt 1)) (.dia () (.reset () (.var true))))
      (.box () (.and (.guard (.atom () .le 1)) (.reset () (.var true)))))
    (.forallDelay (.var false))

/-- The body of variable `X1` (location `ℓ1`, bound `2`): the dual of `altBody0` with
bound `2`, referencing `X0` across the action. -/
def altBody1 : MtRSys Bool Unit Unit :=
  .and
    (.and
      (.or (.guard (.atom () .gt 2)) (.dia () (.reset () (.var false))))
      (.box () (.and (.guard (.atom () .le 2)) (.reset () (.var false)))))
    (.forallDelay (.var true))

/-- The equation system: variable `false ↦ X0`, `true ↦ X1`. -/
def altSys : Bool → MtRSys Bool Unit Unit
  | false => altBody0
  | true => altBody1

/-- The characteristic sets: `altChar false` is `⟦X0⟧`, `altChar true` is `⟦X1⟧`. -/
def altChar : Bool → Set (Alt × Valuation Unit) := recMaxSys altTLTS altSys

/-! ### Soundness: timed bisimilarity to a location implies satisfaction -/

/-- The candidate family: `altRel false` (resp. `true`) holds at `(p, u)` when `p` is
timed bisimilar to `ℓ0` (resp. `ℓ1`) at clock `u(y)`. -/
def altRel : Bool → Set (Alt × Valuation Unit)
  | false => {q | TimedBisimilar altTLTS q.1 (Alt.L0 (q.2 ()))}
  | true => {q | TimedBisimilar altTLTS q.1 (Alt.L1 (q.2 ()))}

/-- The bisimilarity-class family is a post-fixed point of the equation system: each
class lies inside its body's denotation under the family. The mutual references
(`X0`'s action conjuncts land in `X1` and vice versa) are exactly the location flips. -/
theorem altRel_postfixed : ∀ b, altRel b ⊆ denotSys altTLTS (altSys b) altRel := by
  intro b
  cases b with
  | false =>
    rintro ⟨p, u⟩ hb
    simp only [altRel, Set.mem_setOf_eq] at hb
    obtain ⟨haf, hab, hdf, _⟩ := (timedBisimilar_iff altTLTS p (Alt.L0 (u ()))).1 hb
    simp only [altSys, altBody0, denotSys, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      satisfies, Cmp.holds, Nat.cast_one, altRel]
    have h0 : Valuation.reset ({()} : Set Unit) u () = 0 := Valuation.reset_mem rfl u
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases h1 : u () ≤ 1
      · obtain ⟨p', hp'a, hp'b⟩ := hab () (Alt.L1 0) (AltStep.a0 h1)
        refine Or.inr ⟨p', hp'a, ?_⟩
        show TimedBisimilar altTLTS p' (Alt.L1 (Valuation.reset {()} u ()))
        rw [h0]; exact hp'b
      · exact Or.inl (not_le.mp h1)
    · intro p' hp'a
      obtain ⟨r', hr'a, hr'b⟩ := haf () p' hp'a
      replace hr'a := alt_act.mp hr'a
      cases hr'a with
      | a0 hle =>
        refine ⟨hle, ?_⟩
        show TimedBisimilar altTLTS p' (Alt.L1 (Valuation.reset {()} u ()))
        rw [h0]; exact hr'b
    · intro t p' hp'd
      obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
      replace hr'd := alt_delay.mp hr'd
      cases hr'd with
      | delay0 => rw [Valuation.add_apply]; exact hr'b
  | true =>
    rintro ⟨p, u⟩ hb
    simp only [altRel, Set.mem_setOf_eq] at hb
    obtain ⟨haf, hab, hdf, _⟩ := (timedBisimilar_iff altTLTS p (Alt.L1 (u ()))).1 hb
    simp only [altSys, altBody1, denotSys, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      satisfies, Cmp.holds, Nat.cast_ofNat, altRel]
    have h0 : Valuation.reset ({()} : Set Unit) u () = 0 := Valuation.reset_mem rfl u
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases h2 : u () ≤ 2
      · obtain ⟨p', hp'a, hp'b⟩ := hab () (Alt.L0 0) (AltStep.a1 h2)
        refine Or.inr ⟨p', hp'a, ?_⟩
        show TimedBisimilar altTLTS p' (Alt.L0 (Valuation.reset {()} u ()))
        rw [h0]; exact hp'b
      · exact Or.inl (not_le.mp h2)
    · intro p' hp'a
      obtain ⟨r', hr'a, hr'b⟩ := haf () p' hp'a
      replace hr'a := alt_act.mp hr'a
      cases hr'a with
      | a1 hle =>
        refine ⟨hle, ?_⟩
        show TimedBisimilar altTLTS p' (Alt.L0 (Valuation.reset {()} u ()))
        rw [h0]; exact hr'b
    · intro t p' hp'd
      obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
      replace hr'd := alt_delay.mp hr'd
      cases hr'd with
      | delay1 => rw [Valuation.add_apply]; exact hr'b

/-- Componentwise containment of the bisimilarity classes in the characteristic sets,
by the equation-system coinduction principle (`recMaxSys_coinduction`). -/
theorem altRel_subset_altChar (b : Bool) : altRel b ⊆ altChar b :=
  recMaxSys_coinduction altTLTS altSys altRel_postfixed b

/-- **Soundness for `X0`.** A state timed bisimilar to `ℓ0` at clock `d` satisfies the
characteristic formula `X0` with formula clock `y = d`. -/
theorem altChar_false_sound {p : Alt} {u : Valuation Unit}
    (h : TimedBisimilar altTLTS p (Alt.L0 (u ()))) : (p, u) ∈ altChar false :=
  altRel_subset_altChar false h

/-- **Soundness for `X1`.** A state timed bisimilar to `ℓ1` at clock `d` satisfies the
characteristic formula `X1` with formula clock `y = d`. -/
theorem altChar_true_sound {p : Alt} {u : Valuation Unit}
    (h : TimedBisimilar altTLTS p (Alt.L1 (u ()))) : (p, u) ∈ altChar true :=
  altRel_subset_altChar true h

/-! ### The two mutual equations, explicitly (fixed-point unfolding) -/

/-- The `X0` equation: `(p, u) ⊨ X0` iff `u(y) > 1` or an `a`-move lands in `X1` after
resetting `y`; every `a`-move has `u(y) ≤ 1` and lands in `X1`; and every delay stays in
`X0`. The mutual reference to `altChar true` is the equation system at work. -/
theorem mem_altChar_false {q : Alt × Valuation Unit} :
    q ∈ altChar false ↔
      ((1 < q.2 () ∨ ∃ p', altTLTS.act q.1 () p' ∧ (p', Valuation.reset {()} q.2) ∈ altChar true) ∧
       (∀ p', altTLTS.act q.1 () p' → q.2 () ≤ 1 ∧ (p', Valuation.reset {()} q.2) ∈ altChar true) ∧
       (∀ t p', altTLTS.delay q.1 t p' → (p', q.2.add t) ∈ altChar false)) := by
  have h : altChar false = denotSys altTLTS altBody0 altChar := by
    rw [altChar]; exact recMaxSys_unfold altTLTS altSys false
  conv_lhs => rw [h]
  simp only [altBody0, denotSys, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    Cmp.holds, Nat.cast_one, and_assoc, gt_iff_lt]

/-- The `X1` equation, dual with bound `2` and the mutual reference to `altChar false`. -/
theorem mem_altChar_true {q : Alt × Valuation Unit} :
    q ∈ altChar true ↔
      ((2 < q.2 () ∨ ∃ p', altTLTS.act q.1 () p' ∧ (p', Valuation.reset {()} q.2) ∈ altChar false) ∧
       (∀ p', altTLTS.act q.1 () p' → q.2 () ≤ 2 ∧ (p', Valuation.reset {()} q.2) ∈ altChar false) ∧
       (∀ t p', altTLTS.delay q.1 t p' → (p', q.2.add t) ∈ altChar true)) := by
  have h : altChar true = denotSys altTLTS altBody1 altChar := by
    rw [altChar]; exact recMaxSys_unfold altTLTS altSys true
  conv_lhs => rw [h]
  simp only [altBody1, denotSys, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    Cmp.holds, Nat.cast_ofNat, and_assoc, gt_iff_lt]

end TLTS

end DeepWiki.ReactiveSystems
