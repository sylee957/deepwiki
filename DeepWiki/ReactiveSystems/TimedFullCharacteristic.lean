import DeepWiki.ReactiveSystems.TimedGeneralGuardCharacteristic
import DeepWiki.ReactiveSystems.TimedInvariantCharacteristic

/-! # The unified characteristic construction (all features at once)
A single characteristic construction threading **all** features together: nondeterministic,
multi-clock, multi-action, general-guard edges *and* a location invariant. The automaton `FullTA`
has, per location, a finite list of labelled general-guard edges (over a finite action alphabet)
and a single-bound invariant `iclock ℓ ≤ ibnd ℓ` that gates delays (invariants restrict
time-passage). The body reuses the edge readiness/safety of `TimedGeneralGuardCharacteristic`
(`mgReady`/`mgSafe`) and adds the delay-forcing clause `∃∃(iclock ℓ = ibnd ℓ ∧ X_ℓ)` of
`TimedInvariantCharacteristic`. The full characteristic theorem `uchar_iff` reads
`(p, v) ⊨ X_ℓ ↔ (p ~ (ℓ, v) ∧ v(iclock ℓ) ≤ ibnd ℓ)`. (Restrictions vs. textbook LLW: the
invariant is a single upper bound per location and gates delays only; conjunctive invariants and
action-gating target-invariants would add a boundary-disjunction and a readiness antecedent.) -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- A nondeterministic multi-action multi-clock timed automaton with general-guard edges and a
single-bound location invariant `iclock ℓ ≤ ibnd ℓ`. -/
structure FullTA (Loc C Act : Type*) where
  /-- The outgoing edges of each location. -/
  edges : Loc → List (MGEdge Loc C Act)
  /-- The invariant clock of each location. -/
  iclock : Loc → C
  /-- The invariant bound of each location. -/
  ibnd : Loc → ℕ
  /-- Every edge resets its target's invariant clock (entering a location resets its clock), so
  every action-successor satisfies the target invariant. -/
  hreset : ∀ ℓ, ∀ e ∈ edges ℓ, iclock e.tgt ∈ e.rst

/-- Forget the invariant, recovering the general-guard automaton (to reuse `mgReady`/`mgSafe`). -/
def FullTA.toMGTA {Loc C Act : Type*} (A : FullTA Loc C Act) : MGTA Loc C Act := ⟨A.edges⟩

namespace TLTS

variable {Loc C Act : Type*}

/-- A clock in the reset list reads zero after the reset. -/
theorem resetListVal_mem {x : C} {r : List C} (hx : x ∈ r) (v : Valuation C) :
    resetListVal v r x = 0 :=
  Valuation.reset_mem (show x ∈ {y | y ∈ r} from hx) v

/-- SOS: fire any guard-satisfying edge (label `e.act`); delays are gated by the invariant
`iclock ℓ ≤ ibnd ℓ` at both endpoints. -/
inductive UStep (A : FullTA Loc C Act) :
    (Loc × Valuation C) → (Act ⊕ ℝ≥0) → (Loc × Valuation C) → Prop
  /-- `(ℓ, v) —e.act→ (e.tgt, v[e.rst])` for any guard-satisfying edge `e`. -/
  | act {ℓ : Loc} {v : Valuation C} {e : MGEdge Loc C Act} (he : e ∈ A.edges ℓ)
      (hg : satisfies v e.guard) :
      UStep A (ℓ, v) (Sum.inl e.act) (e.tgt, resetListVal v e.rst)
  /-- `(ℓ, v) —t→ (ℓ, v+t)` while the invariant `iclock ℓ ≤ ibnd ℓ` holds at `v` and `v+t`. -/
  | delay (ℓ : Loc) (v : Valuation C) (t : ℝ≥0)
      (h1 : v (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0)) (h2 : (v.add t) (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0)) :
      UStep A (ℓ, v) (Sum.inr t) (ℓ, v.add t)

/-- The automaton's TLTS. -/
def uTLTS (A : FullTA Loc C Act) : TLTS (Loc × Valuation C) Act := ⟨UStep A⟩

variable {A : FullTA Loc C Act}

@[simp] theorem uact {q q' : Loc × Valuation C} {a : Act} :
    (uTLTS A).act q a q' ↔ UStep A q (Sum.inl a) q' := Iff.rfl

@[simp] theorem udelay {q q' : Loc × Valuation C} {t : ℝ≥0} :
    (uTLTS A).delay q t q' ↔ UStep A q (Sum.inr t) q' := Iff.rfl

/-- **Delay prefix-closure**: if `(ℓ,v)` can delay `s`, it can delay any `t ≤ s` (the lone
bounded clock `iclock ℓ` only increases). -/
theorem udelay_prefix {ℓ : Loc} {v : Valuation C} {s t : ℝ≥0}
    (hs : (uTLTS A).delay (ℓ, v) s (ℓ, v.add s)) (hts : t ≤ s) :
    (uTLTS A).delay (ℓ, v) t (ℓ, v.add t) := by
  rw [udelay] at hs ⊢
  cases hs with
  | delay _ _ _ h1 h2 =>
    refine UStep.delay ℓ v t h1 ?_
    simp only [Valuation.add_apply] at h2 ⊢
    exact le_trans (by gcongr) h2

/-! ### The characteristic equation system -/

variable [Fintype Act] [DecidableEq Act]

/-- The body of `X_ℓ`: the edge readiness `mgReady` and safety `mgSafe` (general-guard,
multi-action, nondeterministic), the delay-safety `∀∀X_ℓ`, and the **delay-forcing**
`∃∃(iclock ℓ = ibnd ℓ ∧ X_ℓ)`. -/
noncomputable def ubody (A : FullTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  .and (.and (mgReady A.toMGTA ℓ) (mgSafe A.toMGTA ℓ))
    (.and (.forallDelay (.var ℓ))
      (.existsDelay (.and (.guard (.atom (A.iclock ℓ) .eq (A.ibnd ℓ))) (.var ℓ))))

/-- The characteristic sets, one per location. -/
noncomputable def uchar (A : FullTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  recMaxSys (uTLTS A) (ubody A)

/-- The `X_ℓ` equation, explicitly. -/
theorem mem_uchar {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C} :
    q ∈ uchar A ℓ ↔
      ((∀ e ∈ A.edges ℓ, ¬ satisfies q.2 e.guard ∨
          ∃ p', (uTLTS A).act q.1 e.act p' ∧ (p', resetListVal q.2 e.rst) ∈ uchar A e.tgt) ∧
       (∀ a p', (uTLTS A).act q.1 a p' → ∃ e ∈ A.edges ℓ, e.act = a ∧
          satisfies q.2 e.guard ∧ (p', resetListVal q.2 e.rst) ∈ uchar A e.tgt) ∧
       (∀ t p', (uTLTS A).delay q.1 t p' → (p', q.2.add t) ∈ uchar A ℓ) ∧
       (∃ t p', (uTLTS A).delay q.1 t p' ∧ (q.2.add t) (A.iclock ℓ) = (A.ibnd ℓ : ℝ≥0) ∧
          (p', q.2.add t) ∈ uchar A ℓ)) := by
  have h : uchar A ℓ = denotSys (uTLTS A) (ubody A ℓ) (uchar A) := by
    rw [uchar]; exact recMaxSys_unfold (uTLTS A) (ubody A) ℓ
  conv_lhs => rw [h]
  simp only [ubody, mgReady, mgSafe, FullTA.toMGTA, denotSys, denotSys_bigAnd_map,
    denotSys_bigOr_map, denotSys_resetAll, denotSys_negConstraint, Set.mem_inter_iff,
    Set.mem_union, Set.mem_setOf_eq, satisfies, Cmp.holds, Finset.mem_toList, Finset.mem_univ,
    List.mem_filter, decide_eq_true_eq, forall_const, and_assoc]

/-! ### Soundness -/

/-- The candidate family: timed bisimilar to `(ℓ, q.2)` and valid (`iclock ℓ ≤ ibnd ℓ`). -/
def urel (A : FullTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  fun ℓ => {q | TimedBisimilar (uTLTS A) q.1 (ℓ, q.2) ∧ q.2 (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0)}

/-- The bisimilarity-class family (restricted to valid states) is a post-fixed point. -/
theorem urel_postfixed :
    ∀ ℓ, urel A ℓ ⊆ denotSys (uTLTS A) (ubody A ℓ) (urel A) := by
  rintro ℓ ⟨p, u⟩ ⟨hb, hvalid⟩
  obtain ⟨haf, hab, hdf, hdb⟩ := (timedBisimilar_iff (uTLTS A) p (ℓ, u)).1 hb
  simp only [ubody, mgReady, mgSafe, FullTA.toMGTA, denotSys, denotSys_bigAnd_map,
    denotSys_bigOr_map, denotSys_resetAll, denotSys_negConstraint, Set.mem_inter_iff,
    Set.mem_union, Set.mem_setOf_eq, satisfies, Cmp.holds, Finset.mem_toList, Finset.mem_univ,
    List.mem_filter, decide_eq_true_eq, forall_const, urel]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- readiness
    intro e he
    by_cases hg : satisfies u e.guard
    · obtain ⟨p', hp'a, hp'b⟩ := hab e.act (e.tgt, resetListVal u e.rst) (UStep.act he hg)
      exact Or.inr ⟨p', hp'a, hp'b, by rw [resetListVal_mem (A.hreset ℓ e he)]; exact zero_le⟩
    · exact Or.inl hg
  · -- safety
    intro a p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf a p' hp'a
    replace hr'a := uact.mp hr'a
    cases hr'a with
    | @act _ _ e he hg =>
      exact ⟨e, ⟨he, rfl⟩, hg, hr'b, by rw [resetListVal_mem (A.hreset ℓ e he)]; exact zero_le⟩
  · -- ∀∀ (delay safety)
    intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    replace hr'd := udelay.mp hr'd
    cases hr'd with
    | delay _ _ _ _ h2 => exact ⟨hr'b, h2⟩
  · -- ∃∃ (delay forcing): delay ibnd ℓ - u(iclock ℓ) to the boundary
    obtain ⟨p', hp'd, hp'b⟩ :=
      hdb (A.ibnd ℓ - u (A.iclock ℓ)) (ℓ, u.add (A.ibnd ℓ - u (A.iclock ℓ)))
        (UStep.delay ℓ u (A.ibnd ℓ - u (A.iclock ℓ)) hvalid
          (le_of_eq (by simp only [Valuation.add_apply]; rw [add_tsub_cancel_of_le hvalid])))
    refine ⟨A.ibnd ℓ - u (A.iclock ℓ), p', hp'd, ?_, hp'b, ?_⟩
    · simp only [Valuation.add_apply]; rw [add_tsub_cancel_of_le hvalid]
    · exact le_of_eq (by simp only [Valuation.add_apply]; rw [add_tsub_cancel_of_le hvalid])

/-- **Soundness.** A state timed bisimilar to a *valid* `(ℓ, v)` satisfies `X_ℓ` at `v`. -/
theorem uchar_sound {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (hb : TimedBisimilar (uTLTS A) p (ℓ, u)) (hv : u (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0)) :
    (p, u) ∈ uchar A ℓ :=
  recMaxSys_coinduction (uTLTS A) (ubody A) urel_postfixed ℓ ⟨hb, hv⟩

/-! ### Completeness -/

/-- Membership forces validity (the boundary-forcing implies `iclock ℓ ≤ ibnd ℓ`). -/
theorem uchar_valid {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C}
    (h : q ∈ uchar A ℓ) : q.2 (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0) := by
  obtain ⟨_, _, _, t, _, _, heq, _⟩ := mem_uchar.mp h
  rw [Valuation.add_apply] at heq
  exact heq ▸ le_self_add

/-- The satisfaction relation. -/
def usatRel (A : FullTA Loc C Act) : (Loc × Valuation C) → (Loc × Valuation C) → Prop :=
  fun a b => (a, b.2) ∈ uchar A b.1

/-- The satisfaction relation is a timed bisimulation: actions matched via the edge
readiness/safety, delays via the boundary-forcing plus prefix-closure. -/
theorem isBisimulation_usatRel :
    LTS.IsBisimulation (uTLTS A) (usatRel A) := by
  rintro ⟨ℓa, wa⟩ ⟨ℓ, v⟩ hab
  simp only [usatRel] at hab
  obtain ⟨C1, C2, C3, C4⟩ := mem_uchar.mp hab
  have hvd : v (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0) := uchar_valid hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl b =>
      obtain ⟨e, he, hea, hg, hmem⟩ := C2 b a' hstep
      subst hea
      exact ⟨(e.tgt, resetListVal v e.rst), UStep.act he hg, hmem⟩
    | inr t =>
      have hdval : (v.add t) (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0) := by
        have := uchar_valid (C3 t a' hstep); simpa using this
      exact ⟨(ℓ, v.add t), UStep.delay ℓ v t hvd hdval, C3 t a' hstep⟩
  · rintro lbl b' hstep
    cases lbl with
    | inl b =>
      replace hstep := uact.mp hstep
      cases hstep with
      | act he hg =>
        rcases C1 _ he with hng | ⟨p', hp'a, hmem⟩
        · exact absurd hg hng
        · exact ⟨p', hp'a, hmem⟩
    | inr t =>
      replace hstep := udelay.mp hstep
      cases hstep with
      | delay _ _ _ _ h2 =>
        obtain ⟨s, a'', hsd, hseq, _⟩ := C4
        replace hsd := udelay.mp hsd
        cases hsd with
        | delay _ _ _ h1s h2s =>
          rw [Valuation.add_apply] at hseq
          have hts : t ≤ s := by
            have hle : v (A.iclock ℓ) + t ≤ v (A.iclock ℓ) + s := by
              rw [hseq]; simpa [Valuation.add_apply] using h2
            exact le_of_add_le_add_left hle
          have hat : (uTLTS A).delay (ℓa, wa) t (ℓa, wa.add t) :=
            udelay_prefix (udelay.mpr (UStep.delay ℓa wa s h1s h2s)) hts
          exact ⟨(ℓa, wa.add t), hat, C3 t (ℓa, wa.add t) hat⟩

/-- **Completeness.** A state satisfying `X_ℓ` at `v` is timed bisimilar to `(ℓ, v)`. -/
theorem uchar_complete {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : (p, u) ∈ uchar A ℓ) : TimedBisimilar (uTLTS A) p (ℓ, u) :=
  isBisimulation_usatRel.le_bisimilar (show usatRel A p (ℓ, u) from h)

/-- **The unified characteristic theorem.** For a nondeterministic multi-clock multi-action
general-guard timed automaton with a single-bound location invariant, `(p, v) ⊨ X_ℓ` iff `p` is
timed bisimilar to `(ℓ, v)` and `(ℓ, v)` is valid. -/
theorem uchar_iff {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C} :
    (p, u) ∈ uchar A ℓ ↔
      TimedBisimilar (uTLTS A) p (ℓ, u) ∧ u (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0) :=
  ⟨fun h => ⟨uchar_complete h, uchar_valid h⟩, fun ⟨hb, hv⟩ => uchar_sound hb hv⟩

end TLTS

end DeepWiki.ReactiveSystems
