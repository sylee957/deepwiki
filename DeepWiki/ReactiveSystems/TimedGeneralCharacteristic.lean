import DeepWiki.ReactiveSystems.TimedConjInvCharacteristic

/-! # Characteristic formulae: the fully general construction
Merges every axis into one characteristic construction for **standard timed automata** — nondeterministic,
multi-clock, multi-action, general-guard edges, *conjunctive* location invariants, **target-invariant-gated
actions** and **arbitrary resets** (no on-entry-reset hypothesis). An `a`-edge fires when its guard holds
and the (conjunctive) *target* invariant holds after the reset; delays are gated by the conjunctive
invariant at both endpoints. The readiness clause carries the conjunctive target-invariant antecedent
`(gₑ ∧ inv(tgtₑ)[rₑ]) ⇒ ⟨a⟩(rₑ in X_{tgtₑ})`, the delay-forcing is the boundary-disjunction
`∃∃(⋀ᵢ xᵢ≤cᵢ ∧ ⋁ᵢ xᵢ=cᵢ ∧ X_ℓ)`. The full theorem `fchar_iff` reads
`(p, v) ⊨ X_ℓ ↔ (p ~ (ℓ, v) ∧ inv ℓ holds at v)`, assuming `inv ℓ ≠ []` (`hne`). This subsumes
`TimedFullCharacteristic`, `TimedTargetInvCharacteristic` and `TimedConjInvCharacteristic`. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- A standard timed automaton with conjunctive invariants and target-invariant-gated actions. -/
structure FTA (Loc C Act : Type*) where
  /-- The outgoing edges of each location. -/
  edges : Loc → List (MGEdge Loc C Act)
  /-- The conjunctive invariant: a list of `(clock, upper bound)` pairs per location. -/
  inv : Loc → List (C × ℕ)
  /-- Every location carries at least one bound. -/
  hne : ∀ ℓ, inv ℓ ≠ []

namespace TLTS

variable {Loc C Act : Type*}

/-- SOS: an `a`-edge fires under its guard *and* the conjunctive target invariant after the
(arbitrary) reset; delays are gated by the conjunctive invariant at both endpoints. -/
inductive FStep (A : FTA Loc C Act) :
    (Loc × Valuation C) → (Act ⊕ ℝ≥0) → (Loc × Valuation C) → Prop
  /-- `(ℓ, v) —e.act→ (e.tgt, v[e.rst])` when `g_e` holds and `inv(e.tgt)` holds at `v[e.rst]`. -/
  | act {ℓ : Loc} {v : Valuation C} {e : MGEdge Loc C Act} (he : e ∈ A.edges ℓ)
      (hg : satisfies v e.guard) (ht : invHolds (A.inv e.tgt) (resetListVal v e.rst)) :
      FStep A (ℓ, v) (Sum.inl e.act) (e.tgt, resetListVal v e.rst)
  /-- `(ℓ, v) —t→ (ℓ, v+t)` while the conjunctive invariant holds at `v` and `v+t`. -/
  | delay (ℓ : Loc) (v : Valuation C) (t : ℝ≥0)
      (h1 : invHolds (A.inv ℓ) v) (h2 : invHolds (A.inv ℓ) (v.add t)) :
      FStep A (ℓ, v) (Sum.inr t) (ℓ, v.add t)

/-- The automaton's TLTS. -/
def fTLTS (A : FTA Loc C Act) : TLTS (Loc × Valuation C) Act := ⟨FStep A⟩

variable {A : FTA Loc C Act}

@[simp] theorem fact {q q' : Loc × Valuation C} {a : Act} :
    (fTLTS A).act q a q' ↔ FStep A q (Sum.inl a) q' := Iff.rfl

@[simp] theorem fdelay {q q' : Loc × Valuation C} {t : ℝ≥0} :
    (fTLTS A).delay q t q' ↔ FStep A q (Sum.inr t) q' := Iff.rfl

/-- Delay prefix-closure: a shorter delay keeps the (convex) conjunctive invariant. -/
theorem fdelay_prefix {ℓ : Loc} {v : Valuation C} {s t : ℝ≥0}
    (hs : (fTLTS A).delay (ℓ, v) s (ℓ, v.add s)) (hts : t ≤ s) :
    (fTLTS A).delay (ℓ, v) t (ℓ, v.add t) := by
  rw [fdelay] at hs ⊢
  cases hs with
  | delay _ _ _ h1 h2 =>
    refine FStep.delay ℓ v t h1 fun p hp => ?_
    have := h2 p hp
    simp only [Valuation.add_apply] at this ⊢
    exact le_trans (by gcongr) this

/-! ### Invariant guards as formulae -/

variable {Proc D : Type*}

/-- `⋀_{(x,c) ∈ L} x ≤ c`. -/
def invGuardL (L : List (C × ℕ)) : MtRSys Loc Act C :=
  bigAnd (L.map fun p => .guard (.atom p.1 .le p.2))

/-- `⋁_{(x,c) ∈ L} x = c`. -/
def invBoundaryL (L : List (C × ℕ)) : MtRSys Loc Act C :=
  bigOr (L.map fun p => .guard (.atom p.1 .eq p.2))

/-- `⋁_{(x,c) ∈ L} x > c` — the negated conjunctive invariant. -/
def invNegL (L : List (C × ℕ)) : MtRSys Loc Act C :=
  bigOr (L.map fun p => .guard (.atom p.1 .gt p.2))

@[simp] theorem denotSys_invGuardL (T : TLTS Proc Act) (L : List (C × ℕ))
    (ρ : Loc → Set (Proc × Valuation C)) :
    denotSys T (invGuardL L) ρ = {q | ∀ p ∈ L, q.2 p.1 ≤ (p.2 : ℝ≥0)} := by
  simp only [invGuardL, denotSys_bigAnd_map, denotSys, Set.mem_setOf_eq, satisfies, Cmp.holds]

@[simp] theorem denotSys_invBoundaryL (T : TLTS Proc Act) (L : List (C × ℕ))
    (ρ : Loc → Set (Proc × Valuation C)) :
    denotSys T (invBoundaryL L) ρ = {q | ∃ p ∈ L, q.2 p.1 = (p.2 : ℝ≥0)} := by
  simp only [invBoundaryL, denotSys_bigOr_map, denotSys, Set.mem_setOf_eq, satisfies, Cmp.holds]

@[simp] theorem denotSys_invNegL (T : TLTS Proc Act) (L : List (C × ℕ))
    (ρ : Loc → Set (Proc × Valuation C)) :
    denotSys T (invNegL L) ρ = {q | ∃ p ∈ L, (p.2 : ℝ≥0) < q.2 p.1} := by
  simp only [invNegL, denotSys_bigOr_map, denotSys, Set.mem_setOf_eq, satisfies, Cmp.holds]

/-! ### The characteristic equation system -/

variable [Fintype Act] [DecidableEq Act]

/-- Readiness `⋀ₑ ((gₑ ∧ inv(tgtₑ)[rₑ]) ⇒ ⟨e.act⟩(rₑ in X_{tgtₑ}))`. -/
def freadiness (A : FTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigAnd ((A.edges ℓ).map fun e =>
    .or (.or (negConstraint e.guard) (resetAll e.rst (invNegL (A.inv e.tgt))))
      (.dia e.act (resetAll e.rst (.var e.tgt))))

/-- Safety `⋀_{a} [a](⋁_{e:e.act=a} (gₑ ∧ inv(tgtₑ)[rₑ] ∧ rₑ in X_{tgtₑ}))`. -/
noncomputable def fsafety (A : FTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigAnd ((Finset.univ.toList).map fun a =>
    .box a (bigOr (((A.edges ℓ).filter fun e => decide (e.act = a)).map fun e =>
      .and (.guard e.guard) (resetAll e.rst (.and (invGuardL (A.inv e.tgt)) (.var e.tgt))))))

/-- The body of `X_ℓ`: readiness, safety, `∀∀X_ℓ`, and the boundary-disjunction forcing. -/
noncomputable def fbody (A : FTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  .and (.and (freadiness A ℓ) (fsafety A ℓ))
    (.and (.forallDelay (.var ℓ))
      (.existsDelay (.and (invGuardL (A.inv ℓ)) (.and (invBoundaryL (A.inv ℓ)) (.var ℓ)))))

/-- The characteristic sets. -/
noncomputable def fchar (A : FTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  recMaxSys (fTLTS A) (fbody A)

/-- The `X_ℓ` equation, explicitly. -/
theorem mem_fchar {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C} :
    q ∈ fchar A ℓ ↔
      ((∀ e ∈ A.edges ℓ,
          (¬ satisfies q.2 e.guard ∨
              ∃ r ∈ A.inv e.tgt, (r.2 : ℝ≥0) < resetListVal q.2 e.rst r.1) ∨
          ∃ p', (fTLTS A).act q.1 e.act p' ∧ (p', resetListVal q.2 e.rst) ∈ fchar A e.tgt) ∧
       (∀ a p', (fTLTS A).act q.1 a p' → ∃ e ∈ A.edges ℓ, e.act = a ∧
          satisfies q.2 e.guard ∧
          (∀ r ∈ A.inv e.tgt, resetListVal q.2 e.rst r.1 ≤ (r.2 : ℝ≥0)) ∧
            (p', resetListVal q.2 e.rst) ∈ fchar A e.tgt) ∧
       (∀ t p', (fTLTS A).delay q.1 t p' → (p', q.2.add t) ∈ fchar A ℓ) ∧
       (∃ t p', (fTLTS A).delay q.1 t p' ∧
          (∀ r ∈ A.inv ℓ, (q.2.add t) r.1 ≤ (r.2 : ℝ≥0)) ∧
          (∃ r ∈ A.inv ℓ, (q.2.add t) r.1 = (r.2 : ℝ≥0)) ∧
          (p', q.2.add t) ∈ fchar A ℓ)) := by
  have h : fchar A ℓ = denotSys (fTLTS A) (fbody A ℓ) (fchar A) := by
    rw [fchar]; exact recMaxSys_unfold (fTLTS A) (fbody A) ℓ
  conv_lhs => rw [h]
  simp only [fbody, freadiness, fsafety, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, denotSys_negConstraint, denotSys_invGuardL, denotSys_invBoundaryL,
    denotSys_invNegL, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
    Finset.mem_toList, Finset.mem_univ, List.mem_filter, decide_eq_true_eq, forall_const, and_assoc]

/-! ### Soundness -/

/-- The candidate family: timed bisimilar to `(ℓ, q.2)` and the invariant holds at `q.2`. -/
def frel (A : FTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  fun ℓ => {q | TimedBisimilar (fTLTS A) q.1 (ℓ, q.2) ∧ invHolds (A.inv ℓ) q.2}

/-- The bisimilarity-class family (restricted to valid states) is a post-fixed point. -/
theorem frel_postfixed :
    ∀ ℓ, frel A ℓ ⊆ denotSys (fTLTS A) (fbody A ℓ) (frel A) := by
  rintro ℓ ⟨p, u⟩ ⟨hb, hvalid⟩
  obtain ⟨haf, hab, hdf, hdb⟩ := (timedBisimilar_iff (fTLTS A) p (ℓ, u)).1 hb
  simp only [fbody, freadiness, fsafety, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, denotSys_negConstraint, denotSys_invGuardL, denotSys_invBoundaryL,
    denotSys_invNegL, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
    Finset.mem_toList, Finset.mem_univ, List.mem_filter, decide_eq_true_eq, forall_const, frel]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- readiness
    intro e he
    by_cases hg : satisfies u e.guard
    · by_cases ht : invHolds (A.inv e.tgt) (resetListVal u e.rst)
      · obtain ⟨p', hp'a, hp'b⟩ := hab e.act (e.tgt, resetListVal u e.rst) (FStep.act he hg ht)
        exact Or.inr ⟨p', hp'a, hp'b, ht⟩
      · refine Or.inl (Or.inr ?_)
        by_contra hc
        exact ht fun r hr => not_lt.mp fun hlt => hc ⟨r, hr, hlt⟩
    · exact Or.inl (Or.inl hg)
  · -- safety
    intro a p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf a p' hp'a
    replace hr'a := fact.mp hr'a
    cases hr'a with
    | act he hg ht => exact ⟨_, ⟨he, rfl⟩, hg, ht, hr'b, ht⟩
  · -- ∀∀
    intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    replace hr'd := fdelay.mp hr'd
    cases hr'd with
    | delay _ _ _ _ h2 => exact ⟨hr'b, h2⟩
  · -- ∃∃ boundary-disjunction forcing: delay to the minimal bound
    set f : C × ℕ → ℝ≥0 := fun p => (p.2 : ℝ≥0) - u p.1 with hf
    obtain ⟨m, hmem, hmin⟩ : ∃ m ∈ A.inv ℓ, ∀ a ∈ A.inv ℓ, f m ≤ f a := by
      have hfin : {x | x ∈ A.inv ℓ}.Finite := (A.inv ℓ).finite_toSet
      have hne' : {x | x ∈ A.inv ℓ}.Nonempty := by
        cases h : A.inv ℓ with
        | nil => exact absurd h (A.hne ℓ)
        | cons a t => exact ⟨a, by simp⟩
      exact Set.exists_min_image {x | x ∈ A.inv ℓ} f hfin hne'
    set s : ℝ≥0 := f m with hs
    have hbnd : invHolds (A.inv ℓ) (u.add s) := by
      intro r hr
      simp only [Valuation.add_apply]
      have : s ≤ (r.2 : ℝ≥0) - u r.1 := hmin r hr
      calc u r.1 + s ≤ u r.1 + ((r.2 : ℝ≥0) - u r.1) := by gcongr
        _ = (r.2 : ℝ≥0) := add_tsub_cancel_of_le (hvalid r hr)
    have hbd : (u.add s) m.1 = (m.2 : ℝ≥0) := by
      simp only [Valuation.add_apply, hs, hf]
      exact add_tsub_cancel_of_le (hvalid m hmem)
    obtain ⟨p', hp'd, hp'b⟩ := hdb s (ℓ, u.add s) (FStep.delay ℓ u s hvalid hbnd)
    exact ⟨s, p', hp'd, fun r hr => hbnd r hr, ⟨m, hmem, hbd⟩, hp'b, hbnd⟩

/-- **Soundness.** -/
theorem fchar_sound {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (hb : TimedBisimilar (fTLTS A) p (ℓ, u)) (hv : invHolds (A.inv ℓ) u) :
    (p, u) ∈ fchar A ℓ :=
  recMaxSys_coinduction (fTLTS A) (fbody A) frel_postfixed ℓ ⟨hb, hv⟩

/-! ### Completeness -/

/-- Membership forces validity. -/
theorem fchar_valid {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C}
    (h : q ∈ fchar A ℓ) : invHolds (A.inv ℓ) q.2 := by
  obtain ⟨_, _, _, t, _, _, hguard, _⟩ := mem_fchar.mp h
  intro r hr
  have := hguard r hr
  rw [Valuation.add_apply] at this
  exact le_trans le_self_add this

/-- The satisfaction relation. -/
def fsatRel (A : FTA Loc C Act) : (Loc × Valuation C) → (Loc × Valuation C) → Prop :=
  fun a b => (a, b.2) ∈ fchar A b.1

/-- The satisfaction relation is a timed bisimulation. -/
theorem isBisimulation_fsatRel :
    LTS.IsBisimulation (fTLTS A) (fsatRel A) := by
  rintro ⟨ℓa, wa⟩ ⟨ℓ, v⟩ hab
  simp only [fsatRel] at hab
  obtain ⟨C1, C2, C3, C4⟩ := mem_fchar.mp hab
  have hvd : invHolds (A.inv ℓ) v := fchar_valid hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl b =>
      obtain ⟨e, he, hea, hg, ht, hmem⟩ := C2 b a' hstep
      subst hea
      exact ⟨(e.tgt, resetListVal v e.rst), FStep.act he hg ht, hmem⟩
    | inr t =>
      have hdval : invHolds (A.inv ℓ) (v.add t) := by
        have := fchar_valid (C3 t a' hstep); simpa using this
      exact ⟨(ℓ, v.add t), FStep.delay ℓ v t hvd hdval, C3 t a' hstep⟩
  · rintro lbl b' hstep
    cases lbl with
    | inl b =>
      replace hstep := fact.mp hstep
      cases hstep with
      | act he hg ht =>
        rcases C1 _ he with (hng | ⟨r, hr, hlt⟩) | ⟨p', hp'a, hmem⟩
        · exact absurd hg hng
        · exact absurd (ht r hr) (not_le.mpr hlt)
        · exact ⟨p', hp'a, hmem⟩
    | inr t =>
      replace hstep := fdelay.mp hstep
      cases hstep with
      | delay _ _ _ _ h2 =>
        obtain ⟨s, a'', hsd, _, ⟨r₀, hr₀mem, hr₀eq⟩, _⟩ := C4
        replace hsd := fdelay.mp hsd
        cases hsd with
        | delay _ _ _ h1s h2s =>
          have hts : t ≤ s := by
            have hle : v r₀.1 + t ≤ v r₀.1 + s := by
              have := h2 r₀ hr₀mem
              rw [Valuation.add_apply] at this
              rw [Valuation.add_apply] at hr₀eq
              rw [hr₀eq]; exact this
            exact le_of_add_le_add_left hle
          have hat : (fTLTS A).delay (ℓa, wa) t (ℓa, wa.add t) :=
            fdelay_prefix (fdelay.mpr (FStep.delay ℓa wa s h1s h2s)) hts
          exact ⟨(ℓa, wa.add t), hat, C3 t (ℓa, wa.add t) hat⟩

/-- **Completeness.** -/
theorem fchar_complete {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : (p, u) ∈ fchar A ℓ) : TimedBisimilar (fTLTS A) p (ℓ, u) :=
  isBisimulation_fsatRel.le_bisimilar (show fsatRel A p (ℓ, u) from h)

/-- **The fully general characteristic theorem.** For standard timed automata with conjunctive
invariants and target-invariant-gated actions, `(p, v) ⊨ X_ℓ` iff `p` is timed bisimilar to `(ℓ, v)`
and the conjunctive invariant holds at `v`. -/
theorem fchar_iff {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C} :
    (p, u) ∈ fchar A ℓ ↔ TimedBisimilar (fTLTS A) p (ℓ, u) ∧ invHolds (A.inv ℓ) u :=
  ⟨fun h => ⟨fchar_complete h, fchar_valid h⟩, fun ⟨hb, hv⟩ => fchar_sound hb hv⟩

end TLTS

end DeepWiki.ReactiveSystems
