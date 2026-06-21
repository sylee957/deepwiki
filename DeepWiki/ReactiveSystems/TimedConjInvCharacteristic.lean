import DeepWiki.ReactiveSystems.TimedFullCharacteristic
import Mathlib.Data.Set.Finite.Lemmas

/-! # Characteristic formulae with conjunctive location invariants
Generalises `TimedFullCharacteristic` from a single-bound invariant to a *conjunction* of upper
bounds per location — `inv ℓ : List (C × ℕ)`, delays gated by `∀ (x,c) ∈ inv ℓ, v x ≤ c`. The
delay-forcing clause becomes a boundary-*disjunction* `∃∃(⋀ᵢ xᵢ ≤ cᵢ ∧ ⋁ᵢ xᵢ = cᵢ ∧ X_ℓ)`: reach a
point where the invariant still holds and *some* clock sits on its bound (the maximal delay). The
edge readiness/safety still reuse `mgReady`/`mgSafe` (on-entry reset of every target-invariant clock,
`hreset`). The full theorem `cchar_iff` reads `(p, v) ⊨ X_ℓ ↔ (p ~ (ℓ, v) ∧ inv ℓ holds at v)`,
assuming every location carries at least one bound (`hne`). The single-bound construction is the
`|inv ℓ| = 1` instance. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- A nondeterministic multi-action multi-clock general-guard timed automaton whose location
invariant is a *conjunction* of upper bounds; edges reset every invariant clock of their target. -/
structure ConjTA (Loc C Act : Type*) where
  /-- The outgoing edges of each location. -/
  edges : Loc → List (MGEdge Loc C Act)
  /-- The conjunctive invariant: a list of `(clock, upper bound)` pairs per location. -/
  inv : Loc → List (C × ℕ)
  /-- Every location carries at least one bound (so the boundary-disjunction is nonempty). -/
  hne : ∀ ℓ, inv ℓ ≠ []
  /-- Each edge resets every invariant clock of its target (on-entry reset). -/
  hreset : ∀ ℓ, ∀ e ∈ edges ℓ, ∀ p ∈ inv e.tgt, p.1 ∈ e.rst

/-- The conjunctive invariant of `L` holds at `v`: every listed clock is below its bound. -/
def invHolds {C : Type*} (L : List (C × ℕ)) (v : Valuation C) : Prop :=
  ∀ p ∈ L, v p.1 ≤ (p.2 : ℝ≥0)

/-- Forget the invariant. -/
def ConjTA.toMGTA {Loc C Act : Type*} (A : ConjTA Loc C Act) : MGTA Loc C Act := ⟨A.edges⟩

namespace TLTS

variable {Loc C Act : Type*}

/-- SOS: edges fire under their guard (targets stay valid by `hreset`); delays are gated by the
conjunctive invariant at both endpoints. -/
inductive CStep (A : ConjTA Loc C Act) :
    (Loc × Valuation C) → (Act ⊕ ℝ≥0) → (Loc × Valuation C) → Prop
  /-- `(ℓ, v) —e.act→ (e.tgt, v[e.rst])` when `g_e` holds. -/
  | act {ℓ : Loc} {v : Valuation C} {e : MGEdge Loc C Act} (he : e ∈ A.edges ℓ)
      (hg : satisfies v e.guard) :
      CStep A (ℓ, v) (Sum.inl e.act) (e.tgt, resetListVal v e.rst)
  /-- `(ℓ, v) —t→ (ℓ, v+t)` while the conjunctive invariant holds at `v` and `v+t`. -/
  | delay (ℓ : Loc) (v : Valuation C) (t : ℝ≥0)
      (h1 : invHolds (A.inv ℓ) v) (h2 : invHolds (A.inv ℓ) (v.add t)) :
      CStep A (ℓ, v) (Sum.inr t) (ℓ, v.add t)

/-- The automaton's TLTS. -/
def cTLTS (A : ConjTA Loc C Act) : TLTS (Loc × Valuation C) Act := ⟨CStep A⟩

variable {A : ConjTA Loc C Act}

@[simp] theorem cact {q q' : Loc × Valuation C} {a : Act} :
    (cTLTS A).act q a q' ↔ CStep A q (Sum.inl a) q' := Iff.rfl

@[simp] theorem cdelay {q q' : Loc × Valuation C} {t : ℝ≥0} :
    (cTLTS A).delay q t q' ↔ CStep A q (Sum.inr t) q' := Iff.rfl

/-- Delay prefix-closure: a shorter delay keeps the (convex) conjunctive invariant. -/
theorem cdelay_prefix {ℓ : Loc} {v : Valuation C} {s t : ℝ≥0}
    (hs : (cTLTS A).delay (ℓ, v) s (ℓ, v.add s)) (hts : t ≤ s) :
    (cTLTS A).delay (ℓ, v) t (ℓ, v.add t) := by
  rw [cdelay] at hs ⊢
  cases hs with
  | delay _ _ _ h1 h2 =>
    refine CStep.delay ℓ v t h1 fun p hp => ?_
    have := h2 p hp
    simp only [Valuation.add_apply] at this ⊢
    exact le_trans (by gcongr) this

variable [Fintype Act] [DecidableEq Act]

/-- The invariant as a formula `⋀_{(x,c) ∈ inv ℓ} x ≤ c` (the delay gate). -/
def invGuard (A : ConjTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigAnd ((A.inv ℓ).map fun p => .guard (.atom p.1 .le p.2))

/-- The invariant boundary as a formula `⋁_{(x,c) ∈ inv ℓ} x = c`. -/
def invBoundary (A : ConjTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigOr ((A.inv ℓ).map fun p => .guard (.atom p.1 .eq p.2))

/-- The body of `X_ℓ`: readiness, safety, `∀∀X_ℓ`, and the boundary-disjunction delay-forcing
`∃∃(invGuard ℓ ∧ invBoundary ℓ ∧ X_ℓ)`. -/
noncomputable def cbody (A : ConjTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  .and (.and (mgReady A.toMGTA ℓ) (mgSafe A.toMGTA ℓ))
    (.and (.forallDelay (.var ℓ))
      (.existsDelay (.and (invGuard A ℓ) (.and (invBoundary A ℓ) (.var ℓ)))))

/-- The characteristic sets. -/
noncomputable def cchar (A : ConjTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  recMaxSys (cTLTS A) (cbody A)

/-- The `X_ℓ` equation, explicitly. -/
theorem mem_cchar {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C} :
    q ∈ cchar A ℓ ↔
      ((∀ e ∈ A.edges ℓ, ¬ satisfies q.2 e.guard ∨
          ∃ p', (cTLTS A).act q.1 e.act p' ∧ (p', resetListVal q.2 e.rst) ∈ cchar A e.tgt) ∧
       (∀ a p', (cTLTS A).act q.1 a p' → ∃ e ∈ A.edges ℓ, e.act = a ∧
          satisfies q.2 e.guard ∧ (p', resetListVal q.2 e.rst) ∈ cchar A e.tgt) ∧
       (∀ t p', (cTLTS A).delay q.1 t p' → (p', q.2.add t) ∈ cchar A ℓ) ∧
       (∃ t p', (cTLTS A).delay q.1 t p' ∧
          (∀ r ∈ A.inv ℓ, (q.2.add t) r.1 ≤ (r.2 : ℝ≥0)) ∧
          (∃ r ∈ A.inv ℓ, (q.2.add t) r.1 = (r.2 : ℝ≥0)) ∧
          (p', q.2.add t) ∈ cchar A ℓ)) := by
  have h : cchar A ℓ = denotSys (cTLTS A) (cbody A ℓ) (cchar A) := by
    rw [cchar]; exact recMaxSys_unfold (cTLTS A) (cbody A) ℓ
  conv_lhs => rw [h]
  simp only [cbody, mgReady, mgSafe, invGuard, invBoundary, ConjTA.toMGTA, denotSys,
    denotSys_bigAnd_map, denotSys_bigOr_map, denotSys_resetAll, denotSys_negConstraint,
    Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies, Cmp.holds, Finset.mem_toList,
    Finset.mem_univ, List.mem_filter, decide_eq_true_eq, forall_const, and_assoc]

/-! ### Soundness -/

/-- The candidate family: timed bisimilar to `(ℓ, q.2)` and the invariant holds at `q.2`. -/
def crel (A : ConjTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  fun ℓ => {q | TimedBisimilar (cTLTS A) q.1 (ℓ, q.2) ∧ invHolds (A.inv ℓ) q.2}

/-- The bisimilarity-class family (restricted to valid states) is a post-fixed point. -/
theorem crel_postfixed :
    ∀ ℓ, crel A ℓ ⊆ denotSys (cTLTS A) (cbody A ℓ) (crel A) := by
  rintro ℓ ⟨p, u⟩ ⟨hb, hvalid⟩
  obtain ⟨haf, hab, hdf, hdb⟩ := (timedBisimilar_iff (cTLTS A) p (ℓ, u)).1 hb
  simp only [cbody, mgReady, mgSafe, invGuard, invBoundary, ConjTA.toMGTA, denotSys,
    denotSys_bigAnd_map, denotSys_bigOr_map, denotSys_resetAll, denotSys_negConstraint,
    Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies, Cmp.holds, Finset.mem_toList,
    Finset.mem_univ, List.mem_filter, decide_eq_true_eq, forall_const, crel]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- readiness
    intro e he
    by_cases hg : satisfies u e.guard
    · obtain ⟨p', hp'a, hp'b⟩ := hab e.act (e.tgt, resetListVal u e.rst) (CStep.act he hg)
      exact Or.inr ⟨p', hp'a, hp'b, fun r hr => by
        rw [resetListVal_mem (A.hreset ℓ e he r hr)]; exact zero_le⟩
    · exact Or.inl hg
  · -- safety
    intro a p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf a p' hp'a
    replace hr'a := cact.mp hr'a
    cases hr'a with
    | act he hg => exact ⟨_, ⟨he, rfl⟩, hg, hr'b, fun r hr => by
        rw [resetListVal_mem (A.hreset ℓ _ he r hr)]; exact zero_le⟩
  · -- ∀∀
    intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    replace hr'd := cdelay.mp hr'd
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
    obtain ⟨p', hp'd, hp'b⟩ :=
      hdb s (ℓ, u.add s) (CStep.delay ℓ u s hvalid hbnd)
    exact ⟨s, p', hp'd, fun r hr => hbnd r hr, ⟨m, hmem, hbd⟩, hp'b, hbnd⟩

/-- **Soundness.** -/
theorem cchar_sound {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (hb : TimedBisimilar (cTLTS A) p (ℓ, u)) (hv : invHolds (A.inv ℓ) u) :
    (p, u) ∈ cchar A ℓ :=
  recMaxSys_coinduction (cTLTS A) (cbody A) crel_postfixed ℓ ⟨hb, hv⟩

/-! ### Completeness -/

/-- Membership forces validity (read off the forcing's `invGuard` at the boundary). -/
theorem cchar_valid {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C}
    (h : q ∈ cchar A ℓ) : invHolds (A.inv ℓ) q.2 := by
  obtain ⟨_, _, _, t, _, _, hguard, _⟩ := mem_cchar.mp h
  intro r hr
  have := hguard r hr
  rw [Valuation.add_apply] at this
  exact le_trans le_self_add this

/-- The satisfaction relation. -/
def csatRel (A : ConjTA Loc C Act) : (Loc × Valuation C) → (Loc × Valuation C) → Prop :=
  fun a b => (a, b.2) ∈ cchar A b.1

/-- The satisfaction relation is a timed bisimulation. -/
theorem isBisimulation_csatRel :
    LTS.IsBisimulation (cTLTS A) (csatRel A) := by
  rintro ⟨ℓa, wa⟩ ⟨ℓ, v⟩ hab
  simp only [csatRel] at hab
  obtain ⟨C1, C2, C3, C4⟩ := mem_cchar.mp hab
  have hvd : invHolds (A.inv ℓ) v := cchar_valid hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl b =>
      obtain ⟨e, he, hea, hg, hmem⟩ := C2 b a' hstep
      subst hea
      exact ⟨(e.tgt, resetListVal v e.rst), CStep.act he hg, hmem⟩
    | inr t =>
      have hdval : invHolds (A.inv ℓ) (v.add t) := by
        have := cchar_valid (C3 t a' hstep); simpa using this
      exact ⟨(ℓ, v.add t), CStep.delay ℓ v t hvd hdval, C3 t a' hstep⟩
  · rintro lbl b' hstep
    cases lbl with
    | inl b =>
      replace hstep := cact.mp hstep
      cases hstep with
      | act he hg =>
        rcases C1 _ he with hng | ⟨p', hp'a, hmem⟩
        · exact absurd hg hng
        · exact ⟨p', hp'a, hmem⟩
    | inr t =>
      replace hstep := cdelay.mp hstep
      cases hstep with
      | delay _ _ _ _ h2 =>
        obtain ⟨s, a'', hsd, _, ⟨r₀, hr₀mem, hr₀eq⟩, _⟩ := C4
        replace hsd := cdelay.mp hsd
        cases hsd with
        | delay _ _ _ h1s h2s =>
          have hts : t ≤ s := by
            have hle : v r₀.1 + t ≤ v r₀.1 + s := by
              have := h2 r₀ hr₀mem
              rw [Valuation.add_apply] at this
              rw [Valuation.add_apply] at hr₀eq
              rw [hr₀eq]; exact this
            exact le_of_add_le_add_left hle
          have hat : (cTLTS A).delay (ℓa, wa) t (ℓa, wa.add t) :=
            cdelay_prefix (cdelay.mpr (CStep.delay ℓa wa s h1s h2s)) hts
          exact ⟨(ℓa, wa.add t), hat, C3 t (ℓa, wa.add t) hat⟩

/-- **Completeness.** -/
theorem cchar_complete {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : (p, u) ∈ cchar A ℓ) : TimedBisimilar (cTLTS A) p (ℓ, u) :=
  isBisimulation_csatRel.le_bisimilar (show csatRel A p (ℓ, u) from h)

/-- **The characteristic theorem (conjunctive location invariants).** `(p, v) ⊨ X_ℓ` iff `p` is
timed bisimilar to `(ℓ, v)` and the conjunctive invariant holds at `v`. -/
theorem cchar_iff {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C} :
    (p, u) ∈ cchar A ℓ ↔ TimedBisimilar (cTLTS A) p (ℓ, u) ∧ invHolds (A.inv ℓ) u :=
  ⟨fun h => ⟨cchar_complete h, cchar_valid h⟩, fun ⟨hb, hv⟩ => cchar_sound hb hv⟩

end TLTS

end DeepWiki.ReactiveSystems
