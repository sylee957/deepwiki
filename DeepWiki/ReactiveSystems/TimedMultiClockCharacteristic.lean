import DeepWiki.ReactiveSystems.TimedHmlMutualRecursion

/-! # Characteristic formulae for multi-clock deterministic timed automata (generic)
Extends `TimedDeterministicCharacteristic` from one clock to **many**: a deterministic
single-action timed automaton over an arbitrary location set `Loc` and clock set `C`, where
each location `ℓ` has one `a`-edge guarded by `gclock ℓ ≤ gbound ℓ`, resetting the clock
subset `rst ℓ` (a finite list), to `succ ℓ`; delays advance all clocks. Variables are indexed
by `Loc`; the formula clocks mirror the automaton clocks (`D = C`), so the edge's
subset-reset is mirrored by `resetAll (rst ℓ)` — a fold of single `reset`s. The characteristic
system gives `(p, u) ⊨ X_ℓ ↔ p ~ (ℓ, u)` (the formula valuation `u` *is* the canonical state's
clock valuation, so resets ride along with no per-clock bookkeeping). The remaining gap to full
Theorem 12.4 is multi-edge (nondeterministic) automata with invariants. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Loc C ι Act : Type*}

/-! ### Resetting a list of clocks -/

/-- Reset every clock in the list `r` to zero (the set-reset over the list's elements). -/
noncomputable def resetListVal (v : Valuation C) (r : List C) : Valuation C :=
  Valuation.reset {x | x ∈ r} v

/-- Resetting the empty list is the identity. -/
theorem resetListVal_nil (v : Valuation C) : resetListVal v [] = v := by
  funext z; simp [resetListVal, Valuation.reset]

/-- Pushing a single reset inside extends the list. -/
theorem resetListVal_cons (x : C) (v : Valuation C) (xs : List C) :
    resetListVal (Valuation.reset {x} v) xs = resetListVal v (x :: xs) := by
  funext z
  by_cases hx : z = x <;> by_cases hxs : z ∈ xs <;>
    simp [resetListVal, Valuation.reset, Set.mem_setOf_eq, Set.mem_singleton_iff, List.mem_cons,
      hx, hxs]

/-- Fold a list of clock resets into a formula: `resetAll [x₁,…,xₙ] F = x₁ in … xₙ in F`. -/
def resetAll : List C → MtRSys ι Act C → MtRSys ι Act C
  | [], F => F
  | x :: xs, F => .reset x (resetAll xs F)

/-- Denotation of a folded reset: evaluate `F` after resetting every clock in `r`. -/
theorem denotSys_resetAll (T : TLTS Proc Act) (r : List C) (F : MtRSys ι Act C)
    (ρ : ι → Set (Proc × Valuation C)) :
    denotSys T (resetAll r F) ρ = {q | (q.1, resetListVal q.2 r) ∈ denotSys T F ρ} := by
  induction r with
  | nil => ext ⟨a, v⟩; simp only [resetAll, Set.mem_setOf_eq, resetListVal_nil]
  | cons x xs ih =>
    ext q
    simp only [resetAll, denotSys, Set.mem_setOf_eq, ih]
    rw [resetListVal_cons]

/-! ### The generic multi-clock deterministic automaton -/

/-- A deterministic single-action multi-clock timed automaton (no invariants): each location
`ℓ` has one `a`-edge guarded by `gclock ℓ ≤ gbound ℓ`, resetting the clocks `rst ℓ`, to
`succ ℓ`. -/
structure DetTA (Loc C : Type*) where
  /-- The clock compared in location `ℓ`'s guard. -/
  gclock : Loc → C
  /-- The (integer) bound of location `ℓ`'s guard. -/
  gbound : Loc → ℕ
  /-- The clocks reset by location `ℓ`'s edge. -/
  rst : Loc → List C
  /-- The target of location `ℓ`'s edge. -/
  succ : Loc → Loc

variable {Loc C : Type*}

/-- SOS: from `(ℓ, v)`, `a` fires while `v (gclock ℓ) ≤ gbound ℓ` (to `(succ ℓ, v[rst ℓ])`);
time elapses freely, advancing every clock. -/
inductive MGenStep (A : DetTA Loc C) :
    (Loc × Valuation C) → (Unit ⊕ ℝ≥0) → (Loc × Valuation C) → Prop
  /-- `(ℓ, v) —a→ (succ ℓ, v[rst ℓ])` while `v (gclock ℓ) ≤ gbound ℓ`. -/
  | act {ℓ : Loc} {v : Valuation C} (h : v (A.gclock ℓ) ≤ (A.gbound ℓ : ℝ≥0)) :
      MGenStep A (ℓ, v) (Sum.inl ()) (A.succ ℓ, resetListVal v (A.rst ℓ))
  /-- `(ℓ, v)` delays freely. -/
  | delay (ℓ : Loc) (v : Valuation C) (t : ℝ≥0) :
      MGenStep A (ℓ, v) (Sum.inr t) (ℓ, v.add t)

/-- The automaton's TLTS. -/
def mgenTLTS (A : DetTA Loc C) : TLTS (Loc × Valuation C) Unit := ⟨MGenStep A⟩

@[simp] theorem mgen_act {A : DetTA Loc C} {q q' : Loc × Valuation C} :
    (mgenTLTS A).act q () q' ↔ MGenStep A q (Sum.inl ()) q' := Iff.rfl

@[simp] theorem mgen_delay {A : DetTA Loc C} {q q' : Loc × Valuation C} {t : ℝ≥0} :
    (mgenTLTS A).delay q t q' ↔ MGenStep A q (Sum.inr t) q' := Iff.rfl

/-- Every state can delay by any duration. -/
theorem mgen_can_delay (A : DetTA Loc C) (q : Loc × Valuation C) (t : ℝ≥0) :
    ∃ q', (mgenTLTS A).delay q t q' :=
  ⟨_, MGenStep.delay q.1 q.2 t⟩

/-! ### The characteristic equation system (one variable per location) -/

/-- The body of `X_ℓ`: `(gclock ℓ > gbound ℓ ∨ ⟨a⟩(rst ℓ in X_{succ ℓ})) ∧
[a](gclock ℓ ≤ gbound ℓ ∧ rst ℓ in X_{succ ℓ}) ∧ ∀∀X_ℓ`. -/
def mgenBody (A : DetTA Loc C) (ℓ : Loc) : MtRSys Loc Unit C :=
  .and
    (.and
      (.or (.guard (.atom (A.gclock ℓ) .gt (A.gbound ℓ)))
        (.dia () (resetAll (A.rst ℓ) (.var (A.succ ℓ)))))
      (.box () (.and (.guard (.atom (A.gclock ℓ) .le (A.gbound ℓ)))
        (resetAll (A.rst ℓ) (.var (A.succ ℓ))))))
    (.forallDelay (.var ℓ))

/-- The characteristic sets, one per location. -/
def mgenChar (A : DetTA Loc C) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  recMaxSys (mgenTLTS A) (mgenBody A)

/-- The `X_ℓ` equation, explicitly. -/
theorem mem_mgenChar {A : DetTA Loc C} {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C} :
    q ∈ mgenChar A ℓ ↔
      (((A.gbound ℓ : ℝ≥0) < q.2 (A.gclock ℓ) ∨ ∃ p', (mgenTLTS A).act q.1 () p' ∧
            (p', resetListVal q.2 (A.rst ℓ)) ∈ mgenChar A (A.succ ℓ)) ∧
       (∀ p', (mgenTLTS A).act q.1 () p' →
            q.2 (A.gclock ℓ) ≤ (A.gbound ℓ : ℝ≥0) ∧
            (p', resetListVal q.2 (A.rst ℓ)) ∈ mgenChar A (A.succ ℓ)) ∧
       (∀ t p', (mgenTLTS A).delay q.1 t p' → (p', q.2.add t) ∈ mgenChar A ℓ)) := by
  have h : mgenChar A ℓ = denotSys (mgenTLTS A) (mgenBody A ℓ) (mgenChar A) := by
    rw [mgenChar]; exact recMaxSys_unfold (mgenTLTS A) (mgenBody A) ℓ
  conv_lhs => rw [h]
  simp only [mgenBody, denotSys, denotSys_resetAll, Set.mem_inter_iff, Set.mem_union,
    Set.mem_setOf_eq, satisfies, Cmp.holds, and_assoc, gt_iff_lt]

/-! ### Soundness -/

/-- The candidate family: `(q, u) ∈ mgenRel ℓ` iff `q` is timed bisimilar to `(ℓ, u)`. -/
def mgenRel (A : DetTA Loc C) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  fun ℓ => {q | TimedBisimilar (mgenTLTS A) q.1 (ℓ, q.2)}

/-- The bisimilarity-class family is a post-fixed point of the equation system. -/
theorem mgenRel_postfixed (A : DetTA Loc C) :
    ∀ ℓ, mgenRel A ℓ ⊆ denotSys (mgenTLTS A) (mgenBody A ℓ) (mgenRel A) := by
  rintro ℓ ⟨p, u⟩ hb
  simp only [mgenRel, Set.mem_setOf_eq] at hb
  obtain ⟨haf, hab, hdf, _⟩ := (timedBisimilar_iff (mgenTLTS A) p (ℓ, u)).1 hb
  simp only [mgenBody, denotSys, denotSys_resetAll, Set.mem_inter_iff, Set.mem_union,
    Set.mem_setOf_eq, satisfies, Cmp.holds, mgenRel]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_cases h1 : u (A.gclock ℓ) ≤ (A.gbound ℓ : ℝ≥0)
    · obtain ⟨p', hp'a, hp'b⟩ := hab () (A.succ ℓ, resetListVal u (A.rst ℓ)) (MGenStep.act h1)
      exact Or.inr ⟨p', hp'a, hp'b⟩
    · exact Or.inl (not_le.mp h1)
  · intro p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf () p' hp'a
    replace hr'a := mgen_act.mp hr'a
    cases hr'a with
    | act hle => exact ⟨hle, hr'b⟩
  · intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    replace hr'd := mgen_delay.mp hr'd
    cases hr'd with
    | delay => exact hr'b

/-- **Soundness.** A state timed bisimilar to `(ℓ, v)` satisfies `X_ℓ` at formula clocks `v`. -/
theorem mgenChar_sound {A : DetTA Loc C} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : TimedBisimilar (mgenTLTS A) p (ℓ, u)) : (p, u) ∈ mgenChar A ℓ :=
  recMaxSys_coinduction (mgenTLTS A) (mgenBody A) (mgenRel_postfixed A) ℓ h

/-! ### Completeness -/

/-- The satisfaction relation: relate `a` to the canonical `(ℓ, v)`-state when
`(a, v) ⊨ X_ℓ`. -/
def mgenSatRel (A : DetTA Loc C) : (Loc × Valuation C) → (Loc × Valuation C) → Prop :=
  fun a b => (a, b.2) ∈ mgenChar A b.1

/-- The satisfaction relation is a timed bisimulation, read off `mem_mgenChar`. -/
theorem isBisimulation_mgenSatRel (A : DetTA Loc C) :
    LTS.IsBisimulation (mgenTLTS A) (mgenSatRel A) := by
  rintro a ⟨ℓ, v⟩ hab
  simp only [mgenSatRel] at hab
  obtain ⟨C1, C2, C3⟩ := mem_mgenChar.mp hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl u =>
      obtain ⟨⟩ := u
      obtain ⟨hle, hmem⟩ := C2 a' hstep
      refine ⟨(A.succ ℓ, resetListVal v (A.rst ℓ)), MGenStep.act hle, ?_⟩
      simp only [mgenSatRel]; exact hmem
    | inr t =>
      refine ⟨(ℓ, v.add t), MGenStep.delay ℓ v t, ?_⟩
      simp only [mgenSatRel]; exact C3 t a' hstep
  · rintro lbl b' hstep
    cases lbl with
    | inl u =>
      obtain ⟨⟩ := u
      replace hstep := mgen_act.mp hstep
      cases hstep with
      | act hle =>
        rcases C1 with hgt | ⟨p', hp'a, hmem⟩
        · exact absurd hgt (not_lt.mpr hle)
        · exact ⟨p', hp'a, hmem⟩
    | inr t =>
      replace hstep := mgen_delay.mp hstep
      cases hstep with
      | delay =>
        obtain ⟨a', ha'd⟩ := mgen_can_delay A a t
        exact ⟨a', ha'd, C3 t a' ha'd⟩

/-- **Completeness.** A state satisfying `X_ℓ` at formula clocks `v` is timed bisimilar to
`(ℓ, v)`. -/
theorem mgenChar_complete {A : DetTA Loc C} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : (p, u) ∈ mgenChar A ℓ) : TimedBisimilar (mgenTLTS A) p (ℓ, u) :=
  (isBisimulation_mgenSatRel A).le_bisimilar (show mgenSatRel A p (ℓ, u) from h)

/-- **The characteristic theorem (generic, multi-clock).** For a deterministic multi-clock
timed automaton, `(p, v) ⊨ X_ℓ` iff `p` is timed bisimilar to `(ℓ, v)`. -/
theorem mgenChar_iff {A : DetTA Loc C} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C} :
    (p, u) ∈ mgenChar A ℓ ↔ TimedBisimilar (mgenTLTS A) p (ℓ, u) :=
  ⟨mgenChar_complete, mgenChar_sound⟩

end TLTS

end DeepWiki.ReactiveSystems
