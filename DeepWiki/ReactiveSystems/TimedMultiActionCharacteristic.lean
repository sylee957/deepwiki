import DeepWiki.ReactiveSystems.TimedNondetCharacteristic

/-! # Characteristic formulae for multi-action nondeterministic timed automata (generic)
Extends `TimedNondetCharacteristic` to **multiple actions** over a finite alphabet `Act`. Each
edge carries an action; the safety clause conjoins a box `[a]` over *every* `a : Act` (so an
action with no edge gets `[a]ff` — the empty disjunction), pinning that the candidate offers
*exactly* the canonical's actions. The full characteristic theorem `maChar_iff` reads
`(p, v) ⊨ X_ℓ ↔ p ~ (ℓ, v)`. The remaining gap to full Theorem 12.4 is location invariants and
conjunctive (multi-atom) guards. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-! ### The generic multi-action nondeterministic automaton -/

/-- An `act`-labelled edge: guard `gclock ⋈ gbound`, reset list, target. -/
structure MAEdge (Loc C Act : Type*) where
  /-- The guard's clock. -/
  gclock : C
  /-- The guard's comparison. -/
  gcmp : TLTS.GuardCmp
  /-- The guard's (integer) bound. -/
  gbound : ℕ
  /-- The edge's action. -/
  act : Act
  /-- The clocks the edge resets. -/
  rst : List C
  /-- The edge's target location. -/
  tgt : Loc

/-- A nondeterministic multi-action multi-clock timed automaton (no invariants): a finite list
of labelled edges per location, over a finite action alphabet. -/
structure MATA (Loc C Act : Type*) where
  /-- The outgoing edges of each location. -/
  edges : Loc → List (MAEdge Loc C Act)

namespace TLTS

variable {Loc C Act : Type*}

/-- SOS: from `(ℓ, v)`, fire any edge `e ∈ edges ℓ` whose guard holds, with label `e.act`, to
`(tgt e, v[rst e])`; delays advance every clock. -/
inductive MAStep (A : MATA Loc C Act) :
    (Loc × Valuation C) → (Act ⊕ ℝ≥0) → (Loc × Valuation C) → Prop
  /-- `(ℓ, v) —e.act→ (e.tgt, v[e.rst])` for any guard-satisfying edge `e`. -/
  | act {ℓ : Loc} {v : Valuation C} {e : MAEdge Loc C Act} (he : e ∈ A.edges ℓ)
      (hg : Cmp.holds e.gcmp.toCmp (v e.gclock) e.gbound) :
      MAStep A (ℓ, v) (Sum.inl e.act) (e.tgt, resetListVal v e.rst)
  /-- `(ℓ, v)` delays freely. -/
  | delay (ℓ : Loc) (v : Valuation C) (t : ℝ≥0) : MAStep A (ℓ, v) (Sum.inr t) (ℓ, v.add t)

/-- The automaton's TLTS. -/
def maTLTS (A : MATA Loc C Act) : TLTS (Loc × Valuation C) Act := ⟨MAStep A⟩

@[simp] theorem ma_act {A : MATA Loc C Act} {q q' : Loc × Valuation C} {a : Act} :
    (maTLTS A).act q a q' ↔ MAStep A q (Sum.inl a) q' := Iff.rfl

@[simp] theorem ma_delay {A : MATA Loc C Act} {q q' : Loc × Valuation C} {t : ℝ≥0} :
    (maTLTS A).delay q t q' ↔ MAStep A q (Sum.inr t) q' := Iff.rfl

/-- Every state can delay by any duration. -/
theorem ma_can_delay (A : MATA Loc C Act) (q : Loc × Valuation C) (t : ℝ≥0) :
    ∃ q', (maTLTS A).delay q t q' :=
  ⟨_, MAStep.delay q.1 q.2 t⟩

/-! ### The characteristic equation system -/

variable [Fintype Act] [DecidableEq Act]

/-- Readiness: `⋀ₑ (gₑ ⇒ ⟨e.act⟩(rₑ in X_{tgtₑ}))`. -/
def maReady (A : MATA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigAnd ((A.edges ℓ).map fun e =>
    .or (.guard (.atom e.gclock e.gcmp.neg.toCmp e.gbound))
      (.dia e.act (resetAll e.rst (.var e.tgt))))

/-- Safety: `⋀_{a : Act} [a](⋁_{e : e.act = a} (gₑ ∧ rₑ in X_{tgtₑ}))`. An action with no edge
gets the empty disjunction `[a]ff`. -/
noncomputable def maSafe (A : MATA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigAnd ((Finset.univ.toList).map fun a =>
    .box a (bigOr (((A.edges ℓ).filter fun e => decide (e.act = a)).map fun e =>
      .and (.guard (.atom e.gclock e.gcmp.toCmp e.gbound)) (resetAll e.rst (.var e.tgt)))))

/-- The body of `X_ℓ`: readiness ∧ safety ∧ `∀∀X_ℓ`. -/
noncomputable def maBody (A : MATA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  .and (.and (maReady A ℓ) (maSafe A ℓ)) (.forallDelay (.var ℓ))

/-- The characteristic sets, one per location. -/
noncomputable def maChar (A : MATA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  recMaxSys (maTLTS A) (maBody A)

/-- The `X_ℓ` equation, explicitly. -/
theorem mem_maChar {A : MATA Loc C Act} {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C} :
    q ∈ maChar A ℓ ↔
      ((∀ e ∈ A.edges ℓ, ¬ Cmp.holds e.gcmp.toCmp (q.2 e.gclock) e.gbound ∨
          ∃ p', (maTLTS A).act q.1 e.act p' ∧ (p', resetListVal q.2 e.rst) ∈ maChar A e.tgt) ∧
       (∀ a p', (maTLTS A).act q.1 a p' → ∃ e ∈ A.edges ℓ, e.act = a ∧
          Cmp.holds e.gcmp.toCmp (q.2 e.gclock) e.gbound ∧
            (p', resetListVal q.2 e.rst) ∈ maChar A e.tgt) ∧
       (∀ t p', (maTLTS A).delay q.1 t p' → (p', q.2.add t) ∈ maChar A ℓ)) := by
  have h : maChar A ℓ = denotSys (maTLTS A) (maBody A ℓ) (maChar A) := by
    rw [maChar]; exact recMaxSys_unfold (maTLTS A) (maBody A) ℓ
  conv_lhs => rw [h]
  simp only [maBody, maReady, maSafe, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    GuardCmp.holds_neg, Finset.mem_toList, Finset.mem_univ, List.mem_filter, decide_eq_true_eq,
    forall_const, and_assoc]

/-! ### Soundness -/

/-- The candidate family: `(q, u) ∈ maRel ℓ` iff `q` is timed bisimilar to `(ℓ, u)`. -/
def maRel (A : MATA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  fun ℓ => {q | TimedBisimilar (maTLTS A) q.1 (ℓ, q.2)}

/-- The bisimilarity-class family is a post-fixed point of the equation system. -/
theorem maRel_postfixed (A : MATA Loc C Act) :
    ∀ ℓ, maRel A ℓ ⊆ denotSys (maTLTS A) (maBody A ℓ) (maRel A) := by
  rintro ℓ ⟨p, u⟩ hb
  simp only [maRel, Set.mem_setOf_eq] at hb
  obtain ⟨haf, hab, hdf, _⟩ := (timedBisimilar_iff (maTLTS A) p (ℓ, u)).1 hb
  simp only [maBody, maReady, maSafe, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    GuardCmp.holds_neg, Finset.mem_toList, Finset.mem_univ, List.mem_filter, decide_eq_true_eq,
    forall_const, maRel]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    by_cases hg : Cmp.holds e.gcmp.toCmp (u e.gclock) e.gbound
    · obtain ⟨p', hp'a, hp'b⟩ := hab e.act (e.tgt, resetListVal u e.rst) (MAStep.act he hg)
      exact Or.inr ⟨p', hp'a, hp'b⟩
    · exact Or.inl hg
  · intro a p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf a p' hp'a
    replace hr'a := ma_act.mp hr'a
    cases hr'a with
    | act he hg => exact ⟨_, ⟨he, rfl⟩, hg, hr'b⟩
  · intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    replace hr'd := ma_delay.mp hr'd
    cases hr'd with
    | delay => exact hr'b

/-- **Soundness.** A state timed bisimilar to `(ℓ, v)` satisfies `X_ℓ` at formula clocks `v`. -/
theorem maChar_sound {A : MATA Loc C Act} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : TimedBisimilar (maTLTS A) p (ℓ, u)) : (p, u) ∈ maChar A ℓ :=
  recMaxSys_coinduction (maTLTS A) (maBody A) (maRel_postfixed A) ℓ h

/-! ### Completeness -/

/-- The satisfaction relation: relate `a` to canonical `(ℓ, v)` when `(a, v) ⊨ X_ℓ`. -/
def maSatRel (A : MATA Loc C Act) : (Loc × Valuation C) → (Loc × Valuation C) → Prop :=
  fun a b => (a, b.2) ∈ maChar A b.1

/-- The satisfaction relation is a timed bisimulation. -/
theorem isBisimulation_maSatRel (A : MATA Loc C Act) :
    LTS.IsBisimulation (maTLTS A) (maSatRel A) := by
  rintro a ⟨ℓ, v⟩ hab
  simp only [maSatRel] at hab
  obtain ⟨C1, C2, C3⟩ := mem_maChar.mp hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl b =>
      obtain ⟨e, he, hea, hg, hmem⟩ := C2 b a' hstep
      subst hea
      refine ⟨(e.tgt, resetListVal v e.rst), MAStep.act he hg, ?_⟩
      simp only [maSatRel]; exact hmem
    | inr t =>
      refine ⟨(ℓ, v.add t), MAStep.delay ℓ v t, ?_⟩
      simp only [maSatRel]; exact C3 t a' hstep
  · rintro lbl b' hstep
    cases lbl with
    | inl b =>
      replace hstep := ma_act.mp hstep
      cases hstep with
      | act he hg =>
        rcases C1 _ he with hng | ⟨p', hp'a, hmem⟩
        · exact absurd hg hng
        · exact ⟨p', hp'a, hmem⟩
    | inr t =>
      replace hstep := ma_delay.mp hstep
      cases hstep with
      | delay =>
        obtain ⟨a', ha'd⟩ := ma_can_delay A a t
        exact ⟨a', ha'd, C3 t a' ha'd⟩

/-- **Completeness.** A state satisfying `X_ℓ` at formula clocks `v` is timed bisimilar to
`(ℓ, v)`. -/
theorem maChar_complete {A : MATA Loc C Act} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : (p, u) ∈ maChar A ℓ) : TimedBisimilar (maTLTS A) p (ℓ, u) :=
  (isBisimulation_maSatRel A).le_bisimilar (show maSatRel A p (ℓ, u) from h)

/-- **The characteristic theorem (generic, multi-action nondeterministic multi-clock).**
`(p, v) ⊨ X_ℓ` iff `p` is timed bisimilar to `(ℓ, v)`. -/
theorem maChar_iff {A : MATA Loc C Act} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C} :
    (p, u) ∈ maChar A ℓ ↔ TimedBisimilar (maTLTS A) p (ℓ, u) :=
  ⟨maChar_complete, maChar_sound⟩

end TLTS

end DeepWiki.ReactiveSystems
