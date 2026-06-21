import DeepWiki.ReactiveSystems.TimedMultiActionCharacteristic

/-! # Characteristic formulae with general (conjunctive) guards
Generalises `TimedMultiActionCharacteristic` from single-atom guards (`GuardCmp`) to arbitrary
clock constraints `ClockConstraint C` — `tt`, atoms `x ⋈ n` with *any* comparison (including
`=`), and conjunctions `g₁ ∧ g₂`. The readiness implication `g ⇒ ⟨a⟩…` needs `¬g`, which for a
general constraint is a disjunction-of-atoms (`negConstraint`, by De Morgan, with `=` splitting
into `< ∨ >`). The full characteristic theorem `mgChar_iff` reads `(p, v) ⊨ X_ℓ ↔ p ~ (ℓ, v)`.
The remaining gap to full Theorem 12.4 is location invariants (which need a delay-forcing clause,
not just the safety `∀∀`). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act D ι : Type*}

/-! ### Negation of a clock constraint as a formula -/

/-- The complement of a single atom `x ⋈ n`, as a (guard) formula. `=` splits into `< ∨ >`. -/
def negAtom (x : C) (c : Cmp) (n : ℕ) : MtRSys ι Act C :=
  match c with
  | .le => .guard (.atom x .gt n)
  | .lt => .guard (.atom x .ge n)
  | .ge => .guard (.atom x .lt n)
  | .gt => .guard (.atom x .le n)
  | .eq => .or (.guard (.atom x .lt n)) (.guard (.atom x .gt n))

/-- The negation of a clock constraint, as a formula (De Morgan over `∧`, per-atom complement). -/
def negConstraint : ClockConstraint C → MtRSys ι Act C
  | .true_ => .ff
  | .atom x c n => negAtom x c n
  | .and g₁ g₂ => .or (negConstraint g₁) (negConstraint g₂)

/-- The negation formula is satisfied exactly when the constraint fails. -/
theorem denotSys_negConstraint (T : TLTS Proc Act) (g : ClockConstraint C)
    (ρ : ι → Set (Proc × Valuation C)) :
    denotSys T (negConstraint g) ρ = {q | ¬ satisfies q.2 g} := by
  induction g with
  | true_ => ext q; simp [negConstraint, denotSys, satisfies]
  | atom x c n =>
    ext q
    cases c with
    | le => simp [negConstraint, negAtom, denotSys, satisfies, Cmp.holds, Set.mem_setOf_eq, not_le]
    | lt => simp [negConstraint, negAtom, denotSys, satisfies, Cmp.holds, Set.mem_setOf_eq, not_lt]
    | ge => simp [negConstraint, negAtom, denotSys, satisfies, Cmp.holds, Set.mem_setOf_eq, not_le]
    | gt => simp [negConstraint, negAtom, denotSys, satisfies, Cmp.holds, Set.mem_setOf_eq, not_lt]
    | eq =>
      simp only [negConstraint, negAtom, denotSys, satisfies, Cmp.holds, Set.mem_union,
        Set.mem_setOf_eq]
      exact ⟨fun h heq => h.elim (fun hlt => absurd heq (ne_of_lt hlt))
              (fun hgt => absurd heq (ne_of_gt hgt)), fun h => lt_or_gt_of_ne h⟩
  | and g₁ g₂ ih₁ ih₂ =>
    ext q
    simp only [negConstraint, denotSys, Set.mem_union, Set.mem_setOf_eq, ih₁, ih₂,
      satisfies, not_and_or]

end TLTS

/-! ### The automaton with general guards -/

/-- An `act`-labelled edge with a general clock-constraint guard. -/
structure MGEdge (Loc C Act : Type*) where
  /-- The edge's guard (any clock constraint). -/
  guard : ClockConstraint C
  /-- The edge's action. -/
  act : Act
  /-- The clocks the edge resets. -/
  rst : List C
  /-- The edge's target location. -/
  tgt : Loc

/-- A nondeterministic multi-action timed automaton with general guards (no invariants). -/
structure MGTA (Loc C Act : Type*) where
  /-- The outgoing edges of each location. -/
  edges : Loc → List (MGEdge Loc C Act)

namespace TLTS

variable {Loc C Act : Type*}

/-- SOS: fire any edge `e ∈ edges ℓ` whose guard holds, with label `e.act`. -/
inductive MGStep (A : MGTA Loc C Act) :
    (Loc × Valuation C) → (Act ⊕ ℝ≥0) → (Loc × Valuation C) → Prop
  /-- `(ℓ, v) —e.act→ (e.tgt, v[e.rst])` for any guard-satisfying edge `e`. -/
  | act {ℓ : Loc} {v : Valuation C} {e : MGEdge Loc C Act} (he : e ∈ A.edges ℓ)
      (hg : satisfies v e.guard) :
      MGStep A (ℓ, v) (Sum.inl e.act) (e.tgt, resetListVal v e.rst)
  /-- `(ℓ, v)` delays freely. -/
  | delay (ℓ : Loc) (v : Valuation C) (t : ℝ≥0) : MGStep A (ℓ, v) (Sum.inr t) (ℓ, v.add t)

/-- The automaton's TLTS. -/
def mgTLTS (A : MGTA Loc C Act) : TLTS (Loc × Valuation C) Act := ⟨MGStep A⟩

@[simp] theorem mg_act {A : MGTA Loc C Act} {q q' : Loc × Valuation C} {a : Act} :
    (mgTLTS A).act q a q' ↔ MGStep A q (Sum.inl a) q' := Iff.rfl

@[simp] theorem mg_delay {A : MGTA Loc C Act} {q q' : Loc × Valuation C} {t : ℝ≥0} :
    (mgTLTS A).delay q t q' ↔ MGStep A q (Sum.inr t) q' := Iff.rfl

/-- Every state can delay by any duration. -/
theorem mg_can_delay (A : MGTA Loc C Act) (q : Loc × Valuation C) (t : ℝ≥0) :
    ∃ q', (mgTLTS A).delay q t q' :=
  ⟨_, MGStep.delay q.1 q.2 t⟩

/-! ### The characteristic equation system -/

variable [Fintype Act] [DecidableEq Act]

/-- Readiness: `⋀ₑ (gₑ ⇒ ⟨e.act⟩(rₑ in X_{tgtₑ}))`, with `¬gₑ` via `negConstraint`. -/
def mgReady (A : MGTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigAnd ((A.edges ℓ).map fun e =>
    .or (negConstraint e.guard) (.dia e.act (resetAll e.rst (.var e.tgt))))

/-- Safety: `⋀_{a : Act} [a](⋁_{e : e.act = a} (gₑ ∧ rₑ in X_{tgtₑ}))`. -/
noncomputable def mgSafe (A : MGTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigAnd ((Finset.univ.toList).map fun a =>
    .box a (bigOr (((A.edges ℓ).filter fun e => decide (e.act = a)).map fun e =>
      .and (.guard e.guard) (resetAll e.rst (.var e.tgt)))))

/-- The body of `X_ℓ`: readiness ∧ safety ∧ `∀∀X_ℓ`. -/
noncomputable def mgBody (A : MGTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  .and (.and (mgReady A ℓ) (mgSafe A ℓ)) (.forallDelay (.var ℓ))

/-- The characteristic sets, one per location. -/
noncomputable def mgChar (A : MGTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  recMaxSys (mgTLTS A) (mgBody A)

/-- The `X_ℓ` equation, explicitly. -/
theorem mem_mgChar {A : MGTA Loc C Act} {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C} :
    q ∈ mgChar A ℓ ↔
      ((∀ e ∈ A.edges ℓ, ¬ satisfies q.2 e.guard ∨
          ∃ p', (mgTLTS A).act q.1 e.act p' ∧ (p', resetListVal q.2 e.rst) ∈ mgChar A e.tgt) ∧
       (∀ a p', (mgTLTS A).act q.1 a p' → ∃ e ∈ A.edges ℓ, e.act = a ∧
          satisfies q.2 e.guard ∧ (p', resetListVal q.2 e.rst) ∈ mgChar A e.tgt) ∧
       (∀ t p', (mgTLTS A).delay q.1 t p' → (p', q.2.add t) ∈ mgChar A ℓ)) := by
  have h : mgChar A ℓ = denotSys (mgTLTS A) (mgBody A ℓ) (mgChar A) := by
    rw [mgChar]; exact recMaxSys_unfold (mgTLTS A) (mgBody A) ℓ
  conv_lhs => rw [h]
  simp only [mgBody, mgReady, mgSafe, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, denotSys_negConstraint, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
    Finset.mem_toList, Finset.mem_univ, List.mem_filter, decide_eq_true_eq,
    forall_const, and_assoc]

/-! ### Soundness -/

/-- The candidate family: `(q, u) ∈ mgRel ℓ` iff `q` is timed bisimilar to `(ℓ, u)`. -/
def mgRel (A : MGTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  fun ℓ => {q | TimedBisimilar (mgTLTS A) q.1 (ℓ, q.2)}

/-- The bisimilarity-class family is a post-fixed point of the equation system. -/
theorem mgRel_postfixed (A : MGTA Loc C Act) :
    ∀ ℓ, mgRel A ℓ ⊆ denotSys (mgTLTS A) (mgBody A ℓ) (mgRel A) := by
  rintro ℓ ⟨p, u⟩ hb
  simp only [mgRel, Set.mem_setOf_eq] at hb
  obtain ⟨haf, hab, hdf, _⟩ := (timedBisimilar_iff (mgTLTS A) p (ℓ, u)).1 hb
  simp only [mgBody, mgReady, mgSafe, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, denotSys_negConstraint, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
    Finset.mem_toList, Finset.mem_univ, List.mem_filter, decide_eq_true_eq,
    forall_const, mgRel]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    by_cases hg : satisfies u e.guard
    · obtain ⟨p', hp'a, hp'b⟩ := hab e.act (e.tgt, resetListVal u e.rst) (MGStep.act he hg)
      exact Or.inr ⟨p', hp'a, hp'b⟩
    · exact Or.inl hg
  · intro a p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf a p' hp'a
    replace hr'a := mg_act.mp hr'a
    cases hr'a with
    | act he hg => exact ⟨_, ⟨he, rfl⟩, hg, hr'b⟩
  · intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    replace hr'd := mg_delay.mp hr'd
    cases hr'd with
    | delay => exact hr'b

/-- **Soundness.** A state timed bisimilar to `(ℓ, v)` satisfies `X_ℓ` at formula clocks `v`. -/
theorem mgChar_sound {A : MGTA Loc C Act} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : TimedBisimilar (mgTLTS A) p (ℓ, u)) : (p, u) ∈ mgChar A ℓ :=
  recMaxSys_coinduction (mgTLTS A) (mgBody A) (mgRel_postfixed A) ℓ h

/-! ### Completeness -/

/-- The satisfaction relation: relate `a` to canonical `(ℓ, v)` when `(a, v) ⊨ X_ℓ`. -/
def mgSatRel (A : MGTA Loc C Act) : (Loc × Valuation C) → (Loc × Valuation C) → Prop :=
  fun a b => (a, b.2) ∈ mgChar A b.1

/-- The satisfaction relation is a timed bisimulation. -/
theorem isBisimulation_mgSatRel (A : MGTA Loc C Act) :
    LTS.IsBisimulation (mgTLTS A) (mgSatRel A) := by
  rintro a ⟨ℓ, v⟩ hab
  simp only [mgSatRel] at hab
  obtain ⟨C1, C2, C3⟩ := mem_mgChar.mp hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl b =>
      obtain ⟨e, he, hea, hg, hmem⟩ := C2 b a' hstep
      subst hea
      refine ⟨(e.tgt, resetListVal v e.rst), MGStep.act he hg, ?_⟩
      simp only [mgSatRel]; exact hmem
    | inr t =>
      refine ⟨(ℓ, v.add t), MGStep.delay ℓ v t, ?_⟩
      simp only [mgSatRel]; exact C3 t a' hstep
  · rintro lbl b' hstep
    cases lbl with
    | inl b =>
      replace hstep := mg_act.mp hstep
      cases hstep with
      | act he hg =>
        rcases C1 _ he with hng | ⟨p', hp'a, hmem⟩
        · exact absurd hg hng
        · exact ⟨p', hp'a, hmem⟩
    | inr t =>
      replace hstep := mg_delay.mp hstep
      cases hstep with
      | delay =>
        obtain ⟨a', ha'd⟩ := mg_can_delay A a t
        exact ⟨a', ha'd, C3 t a' ha'd⟩

/-- **Completeness.** A state satisfying `X_ℓ` at formula clocks `v` is timed bisimilar to
`(ℓ, v)`. -/
theorem mgChar_complete {A : MGTA Loc C Act} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : (p, u) ∈ mgChar A ℓ) : TimedBisimilar (mgTLTS A) p (ℓ, u) :=
  (isBisimulation_mgSatRel A).le_bisimilar (show mgSatRel A p (ℓ, u) from h)

/-- **The characteristic theorem (generic, general guards).** `(p, v) ⊨ X_ℓ` iff `p` is timed
bisimilar to `(ℓ, v)`, for a nondeterministic multi-action multi-clock timed automaton with
arbitrary clock-constraint guards. -/
theorem mgChar_iff {A : MGTA Loc C Act} {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C} :
    (p, u) ∈ mgChar A ℓ ↔ TimedBisimilar (mgTLTS A) p (ℓ, u) :=
  ⟨mgChar_complete, mgChar_sound⟩

end TLTS

end DeepWiki.ReactiveSystems
