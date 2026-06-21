import DeepWiki.ReactiveSystems.TimedMultiClockCharacteristic

/-! # Characteristic formulae for nondeterministic multi-clock timed automata (generic)
Extends `TimedMultiClockCharacteristic` to **nondeterminism**: each location carries a finite
*list* of `a`-edges (single action), each with a single-atom guard `gclock ⋈ gbound`
(`⋈ ∈ {≤,<,≥,>}`, so its negation is again an atom — `GuardCmp`), a reset list and a target.
The characteristic body folds over the edge list: a *readiness* conjunction
`⋀ₑ (gₑ ⇒ ⟨a⟩(rₑ in X_{tgtₑ}))` and a *safety* box `[a](⋁ₑ (gₑ ∧ rₑ in X_{tgtₑ}))`, plus `∀∀X_ℓ`.
The full characteristic theorem `ndChar_iff` reads `(p, v) ⊨ X_ℓ ↔ p ~ (ℓ, v)`. The remaining
gap to full Theorem 12.4 is multiple actions (per-action boxes over a finite `Act`) and location
invariants. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act D ι : Type*}

/-! ### Big conjunction / disjunction of formulae -/

/-- The conjunction of a list of formulae. -/
def bigAnd : List (MtRSys ι Act D) → MtRSys ι Act D := fun Fs => Fs.foldr .and .tt

/-- The disjunction of a list of formulae. -/
def bigOr : List (MtRSys ι Act D) → MtRSys ι Act D := fun Fs => Fs.foldr .or .ff

@[simp] theorem bigAnd_cons (F : MtRSys ι Act D) (Fs : List (MtRSys ι Act D)) :
    bigAnd (F :: Fs) = .and F (bigAnd Fs) := rfl

@[simp] theorem bigOr_cons (F : MtRSys ι Act D) (Fs : List (MtRSys ι Act D)) :
    bigOr (F :: Fs) = .or F (bigOr Fs) := rfl

/-- Denotation of a mapped big conjunction: satisfied iff every edge's formula is. -/
theorem denotSys_bigAnd_map {α : Type*} (T : TLTS Proc Act) (es : List α)
    (g : α → MtRSys ι Act D) (ρ : ι → Set (Proc × Valuation D)) :
    denotSys T (bigAnd (es.map g)) ρ = {q | ∀ e ∈ es, q ∈ denotSys T (g e) ρ} := by
  induction es with
  | nil => ext q; simp [bigAnd, denotSys]
  | cons e es ih =>
    ext q
    rw [List.map_cons, bigAnd_cons]
    simp only [denotSys, Set.mem_inter_iff, Set.mem_setOf_eq, List.forall_mem_cons, ih]

/-- Denotation of a mapped big disjunction: satisfied iff some edge's formula is. -/
theorem denotSys_bigOr_map {α : Type*} (T : TLTS Proc Act) (es : List α)
    (g : α → MtRSys ι Act D) (ρ : ι → Set (Proc × Valuation D)) :
    denotSys T (bigOr (es.map g)) ρ = {q | ∃ e ∈ es, q ∈ denotSys T (g e) ρ} := by
  induction es with
  | nil => ext q; simp [bigOr, denotSys]
  | cons e es ih =>
    ext q
    rw [List.map_cons, bigOr_cons]
    simp only [denotSys, Set.mem_union, Set.mem_setOf_eq, List.exists_mem_cons_iff, ih]

/-! ### Negatable single-atom guards -/

/-- The four negatable comparisons (no `=`), so a guard's negation is again a single atom. -/
inductive GuardCmp | le | lt | ge | gt

/-- The underlying clock-constraint comparison. -/
def GuardCmp.toCmp : GuardCmp → Cmp
  | .le => .le | .lt => .lt | .ge => .ge | .gt => .gt

/-- The complementary comparison. -/
def GuardCmp.neg : GuardCmp → GuardCmp
  | .le => .gt | .lt => .ge | .ge => .lt | .gt => .le

/-- The negated comparison holds iff the original fails. -/
theorem GuardCmp.holds_neg (c : GuardCmp) (r : ℝ≥0) (n : ℕ) :
    Cmp.holds c.neg.toCmp r n ↔ ¬ Cmp.holds c.toCmp r n := by
  cases c <;> simp [Cmp.holds, GuardCmp.neg, GuardCmp.toCmp, not_le, not_lt]

end TLTS

/-! ### The generic nondeterministic multi-clock automaton -/

/-- A single-action `a`-edge: guard `gclock ⋈ gbound`, reset list, target. -/
structure NDEdge (Loc C : Type*) where
  /-- The guard's clock. -/
  gclock : C
  /-- The guard's comparison. -/
  gcmp : TLTS.GuardCmp
  /-- The guard's (integer) bound. -/
  gbound : ℕ
  /-- The clocks the edge resets. -/
  rst : List C
  /-- The edge's target location. -/
  tgt : Loc

/-- A nondeterministic single-action multi-clock timed automaton (no invariants): a finite list
of `a`-edges per location. -/
structure NDetTA (Loc C : Type*) where
  /-- The outgoing edges of each location. -/
  edges : Loc → List (NDEdge Loc C)

namespace TLTS

variable {Loc C : Type*}

/-- SOS: from `(ℓ, v)`, fire any edge `e ∈ edges ℓ` whose guard holds, to `(tgt e, v[rst e])`;
delays advance every clock. -/
inductive NDStep (A : NDetTA Loc C) :
    (Loc × Valuation C) → (Unit ⊕ ℝ≥0) → (Loc × Valuation C) → Prop
  /-- `(ℓ, v) —a→ (e.tgt, v[e.rst])` for any guard-satisfying edge `e`. -/
  | act {ℓ : Loc} {v : Valuation C} {e : NDEdge Loc C} (he : e ∈ A.edges ℓ)
      (hg : Cmp.holds e.gcmp.toCmp (v e.gclock) e.gbound) :
      NDStep A (ℓ, v) (Sum.inl ()) (e.tgt, resetListVal v e.rst)
  /-- `(ℓ, v)` delays freely. -/
  | delay (ℓ : Loc) (v : Valuation C) (t : ℝ≥0) : NDStep A (ℓ, v) (Sum.inr t) (ℓ, v.add t)

/-- The automaton's TLTS. -/
def ndTLTS (A : NDetTA Loc C) : TLTS (Loc × Valuation C) Unit := ⟨NDStep A⟩

@[simp] theorem nd_act {A : NDetTA Loc C} {q q' : Loc × Valuation C} :
    (ndTLTS A).act q () q' ↔ NDStep A q (Sum.inl ()) q' := Iff.rfl

@[simp] theorem nd_delay {A : NDetTA Loc C} {q q' : Loc × Valuation C} {t : ℝ≥0} :
    (ndTLTS A).delay q t q' ↔ NDStep A q (Sum.inr t) q' := Iff.rfl

/-- Every state can delay by any duration. -/
theorem nd_can_delay (A : NDetTA Loc C) (q : Loc × Valuation C) (t : ℝ≥0) :
    ∃ q', (ndTLTS A).delay q t q' :=
  ⟨_, NDStep.delay q.1 q.2 t⟩

/-! ### The characteristic equation system -/

/-- Readiness: `⋀ₑ (gₑ ⇒ ⟨a⟩(rₑ in X_{tgtₑ}))`, the implication written `¬gₑ ∨ ⟨a⟩…`. -/
def ndReady (A : NDetTA Loc C) (ℓ : Loc) : MtRSys Loc Unit C :=
  bigAnd ((A.edges ℓ).map fun e =>
    .or (.guard (.atom e.gclock e.gcmp.neg.toCmp e.gbound))
      (.dia () (resetAll e.rst (.var e.tgt))))

/-- Safety: `[a](⋁ₑ (gₑ ∧ rₑ in X_{tgtₑ}))`. -/
def ndSafe (A : NDetTA Loc C) (ℓ : Loc) : MtRSys Loc Unit C :=
  .box () (bigOr ((A.edges ℓ).map fun e =>
    .and (.guard (.atom e.gclock e.gcmp.toCmp e.gbound)) (resetAll e.rst (.var e.tgt))))

/-- The body of `X_ℓ`: readiness ∧ safety ∧ `∀∀X_ℓ`. -/
def ndBody (A : NDetTA Loc C) (ℓ : Loc) : MtRSys Loc Unit C :=
  .and (.and (ndReady A ℓ) (ndSafe A ℓ)) (.forallDelay (.var ℓ))

/-- The characteristic sets, one per location. -/
def ndChar (A : NDetTA Loc C) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  recMaxSys (ndTLTS A) (ndBody A)

/-- The `X_ℓ` equation, explicitly. -/
theorem mem_ndChar {A : NDetTA Loc C} {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C} :
    q ∈ ndChar A ℓ ↔
      ((∀ e ∈ A.edges ℓ, ¬ Cmp.holds e.gcmp.toCmp (q.2 e.gclock) e.gbound ∨
          ∃ p', (ndTLTS A).act q.1 () p' ∧ (p', resetListVal q.2 e.rst) ∈ ndChar A e.tgt) ∧
       (∀ p', (ndTLTS A).act q.1 () p' → ∃ e ∈ A.edges ℓ,
          Cmp.holds e.gcmp.toCmp (q.2 e.gclock) e.gbound ∧
            (p', resetListVal q.2 e.rst) ∈ ndChar A e.tgt) ∧
       (∀ t p', (ndTLTS A).delay q.1 t p' → (p', q.2.add t) ∈ ndChar A ℓ)) := by
  have h : ndChar A ℓ = denotSys (ndTLTS A) (ndBody A ℓ) (ndChar A) := by
    rw [ndChar]; exact recMaxSys_unfold (ndTLTS A) (ndBody A) ℓ
  conv_lhs => rw [h]
  simp only [ndBody, ndReady, ndSafe, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies, GuardCmp.holds_neg, and_assoc]

/-! ### Soundness -/

/-- The candidate family: `(q, u) ∈ ndRel ℓ` iff `q` is timed bisimilar to `(ℓ, u)`. -/
def ndRel (A : NDetTA Loc C) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  fun ℓ => {q | TimedBisimilar (ndTLTS A) q.1 (ℓ, q.2)}

/-- The bisimilarity-class family is a post-fixed point of the equation system. -/
theorem ndRel_postfixed (A : NDetTA Loc C) :
    ∀ ℓ, ndRel A ℓ ⊆ denotSys (ndTLTS A) (ndBody A ℓ) (ndRel A) := by
  rintro ℓ ⟨p, u⟩ hb
  simp only [ndRel, Set.mem_setOf_eq] at hb
  obtain ⟨haf, hab, hdf, _⟩ := (timedBisimilar_iff (ndTLTS A) p (ℓ, u)).1 hb
  simp only [ndBody, ndReady, ndSafe, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies, GuardCmp.holds_neg, ndRel]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    by_cases hg : Cmp.holds e.gcmp.toCmp (u e.gclock) e.gbound
    · obtain ⟨p', hp'a, hp'b⟩ := hab () (e.tgt, resetListVal u e.rst) (NDStep.act he hg)
      exact Or.inr ⟨p', hp'a, hp'b⟩
    · exact Or.inl hg
  · intro p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf () p' hp'a
    replace hr'a := nd_act.mp hr'a
    cases hr'a with
    | act he hg => exact ⟨_, he, hg, hr'b⟩
  · intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    replace hr'd := nd_delay.mp hr'd
    cases hr'd with
    | delay => exact hr'b

/-- **Soundness.** A state timed bisimilar to `(ℓ, v)` satisfies `X_ℓ` at formula clocks `v`. -/
theorem ndChar_sound {A : NDetTA Loc C} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : TimedBisimilar (ndTLTS A) p (ℓ, u)) : (p, u) ∈ ndChar A ℓ :=
  recMaxSys_coinduction (ndTLTS A) (ndBody A) (ndRel_postfixed A) ℓ h

/-! ### Completeness -/

/-- The satisfaction relation: relate `a` to canonical `(ℓ, v)` when `(a, v) ⊨ X_ℓ`. -/
def ndSatRel (A : NDetTA Loc C) : (Loc × Valuation C) → (Loc × Valuation C) → Prop :=
  fun a b => (a, b.2) ∈ ndChar A b.1

/-- The satisfaction relation is a timed bisimulation. -/
theorem isBisimulation_ndSatRel (A : NDetTA Loc C) :
    LTS.IsBisimulation (ndTLTS A) (ndSatRel A) := by
  rintro a ⟨ℓ, v⟩ hab
  simp only [ndSatRel] at hab
  obtain ⟨C1, C2, C3⟩ := mem_ndChar.mp hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl u =>
      obtain ⟨⟩ := u
      obtain ⟨e, he, hg, hmem⟩ := C2 a' hstep
      refine ⟨(e.tgt, resetListVal v e.rst), NDStep.act he hg, ?_⟩
      simp only [ndSatRel]; exact hmem
    | inr t =>
      refine ⟨(ℓ, v.add t), NDStep.delay ℓ v t, ?_⟩
      simp only [ndSatRel]; exact C3 t a' hstep
  · rintro lbl b' hstep
    cases lbl with
    | inl u =>
      obtain ⟨⟩ := u
      replace hstep := nd_act.mp hstep
      cases hstep with
      | act he hg =>
        rcases C1 _ he with hng | ⟨p', hp'a, hmem⟩
        · exact absurd hg hng
        · exact ⟨p', hp'a, hmem⟩
    | inr t =>
      replace hstep := nd_delay.mp hstep
      cases hstep with
      | delay =>
        obtain ⟨a', ha'd⟩ := nd_can_delay A a t
        exact ⟨a', ha'd, C3 t a' ha'd⟩

/-- **Completeness.** A state satisfying `X_ℓ` at formula clocks `v` is timed bisimilar to
`(ℓ, v)`. -/
theorem ndChar_complete {A : NDetTA Loc C} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : (p, u) ∈ ndChar A ℓ) : TimedBisimilar (ndTLTS A) p (ℓ, u) :=
  (isBisimulation_ndSatRel A).le_bisimilar (show ndSatRel A p (ℓ, u) from h)

/-- **The characteristic theorem (generic, nondeterministic multi-clock).** `(p, v) ⊨ X_ℓ` iff
`p` is timed bisimilar to `(ℓ, v)`. -/
theorem ndChar_iff {A : NDetTA Loc C} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C} :
    (p, u) ∈ ndChar A ℓ ↔ TimedBisimilar (ndTLTS A) p (ℓ, u) :=
  ⟨ndChar_complete, ndChar_sound⟩

end TLTS

end DeepWiki.ReactiveSystems
