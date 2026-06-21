import DeepWiki.ReactiveSystems.TimedFullCharacteristic

/-! # Characteristic formulae with target-invariant-gated actions (arbitrary resets)
Generalises `TimedFullCharacteristic` by dropping the on-entry-reset hypothesis: edges may reset
*any* clocks, and an `a`-edge fires only when its **target invariant** holds after the reset (the
standard timed-automaton action rule). The readiness clause therefore gains a target-invariant
antecedent — `(gₑ ∧ iclock(tgtₑ)[rₑ] ≤ ibnd(tgtₑ)) ⇒ ⟨a⟩(rₑ in X_{tgtₑ})` — so it can no longer
reuse `mgReady`/`mgSafe`; the delay-forcing machinery is unchanged. The full theorem `gchar_iff`
reads `(p, v) ⊨ X_ℓ ↔ (p ~ (ℓ, v) ∧ v(iclock ℓ) ≤ ibnd ℓ)`. (Remaining vs. textbook LLW:
conjunctive invariants — a boundary-disjunction in the forcing.) -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- A nondeterministic multi-action multi-clock general-guard timed automaton with a single-bound
location invariant; actions are gated by the target invariant (so resets may be arbitrary). -/
structure GTA (Loc C Act : Type*) where
  /-- The outgoing edges of each location. -/
  edges : Loc → List (MGEdge Loc C Act)
  /-- The invariant clock of each location. -/
  iclock : Loc → C
  /-- The invariant bound of each location. -/
  ibnd : Loc → ℕ

namespace TLTS

variable {Loc C Act : Type*}

/-- SOS: an `a`-edge fires when its guard holds *and* the target invariant holds after the reset;
delays are gated by `iclock ℓ ≤ ibnd ℓ`. -/
inductive GStep (A : GTA Loc C Act) :
    (Loc × Valuation C) → (Act ⊕ ℝ≥0) → (Loc × Valuation C) → Prop
  /-- `(ℓ, v) —e.act→ (e.tgt, v[e.rst])` when `g_e` holds and `iclock(e.tgt)[e.rst] ≤ ibnd(e.tgt)`. -/
  | act {ℓ : Loc} {v : Valuation C} {e : MGEdge Loc C Act} (he : e ∈ A.edges ℓ)
      (hg : satisfies v e.guard)
      (ht : resetListVal v e.rst (A.iclock e.tgt) ≤ (A.ibnd e.tgt : ℝ≥0)) :
      GStep A (ℓ, v) (Sum.inl e.act) (e.tgt, resetListVal v e.rst)
  /-- `(ℓ, v) —t→ (ℓ, v+t)` while the invariant holds at `v` and `v+t`. -/
  | delay (ℓ : Loc) (v : Valuation C) (t : ℝ≥0)
      (h1 : v (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0)) (h2 : (v.add t) (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0)) :
      GStep A (ℓ, v) (Sum.inr t) (ℓ, v.add t)

/-- The automaton's TLTS. -/
def gTLTS (A : GTA Loc C Act) : TLTS (Loc × Valuation C) Act := ⟨GStep A⟩

variable {A : GTA Loc C Act}

@[simp] theorem gact {q q' : Loc × Valuation C} {a : Act} :
    (gTLTS A).act q a q' ↔ GStep A q (Sum.inl a) q' := Iff.rfl

@[simp] theorem gdelay {q q' : Loc × Valuation C} {t : ℝ≥0} :
    (gTLTS A).delay q t q' ↔ GStep A q (Sum.inr t) q' := Iff.rfl

/-- Delay prefix-closure (the lone bounded clock only increases). -/
theorem gdelay_prefix {ℓ : Loc} {v : Valuation C} {s t : ℝ≥0}
    (hs : (gTLTS A).delay (ℓ, v) s (ℓ, v.add s)) (hts : t ≤ s) :
    (gTLTS A).delay (ℓ, v) t (ℓ, v.add t) := by
  rw [gdelay] at hs ⊢
  cases hs with
  | delay _ _ _ h1 h2 =>
    refine GStep.delay ℓ v t h1 ?_
    simp only [Valuation.add_apply] at h2 ⊢
    exact le_trans (by gcongr) h2

/-! ### The characteristic equation system -/

variable [Fintype Act] [DecidableEq Act]

/-- Readiness `⋀ₑ ((gₑ ∧ iclock(tgtₑ)[rₑ] ≤ ibnd(tgtₑ)) ⇒ ⟨e.act⟩(rₑ in X_{tgtₑ}))`, the
implication's negated antecedent being `¬gₑ ∨ iclock(tgtₑ)[rₑ] > ibnd(tgtₑ)`. -/
def greadiness (A : GTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigAnd ((A.edges ℓ).map fun e =>
    .or (.or (negConstraint e.guard)
          (resetAll e.rst (.guard (.atom (A.iclock e.tgt) .gt (A.ibnd e.tgt)))))
      (.dia e.act (resetAll e.rst (.var e.tgt))))

/-- Safety `⋀_{a} [a](⋁_{e:e.act=a} (gₑ ∧ iclock(tgtₑ)[rₑ] ≤ ibnd(tgtₑ) ∧ rₑ in X_{tgtₑ}))`. -/
noncomputable def gsafety (A : GTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  bigAnd ((Finset.univ.toList).map fun a =>
    .box a (bigOr (((A.edges ℓ).filter fun e => decide (e.act = a)).map fun e =>
      .and (.guard e.guard)
        (resetAll e.rst (.and (.guard (.atom (A.iclock e.tgt) .le (A.ibnd e.tgt))) (.var e.tgt))))))

/-- The body of `X_ℓ`: readiness, safety, `∀∀X_ℓ`, and the delay-forcing `∃∃(iclock ℓ = ibnd ℓ ∧ X_ℓ)`. -/
noncomputable def gbody (A : GTA Loc C Act) (ℓ : Loc) : MtRSys Loc Act C :=
  .and (.and (greadiness A ℓ) (gsafety A ℓ))
    (.and (.forallDelay (.var ℓ))
      (.existsDelay (.and (.guard (.atom (A.iclock ℓ) .eq (A.ibnd ℓ))) (.var ℓ))))

/-- The characteristic sets. -/
noncomputable def gchar (A : GTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  recMaxSys (gTLTS A) (gbody A)

/-- The `X_ℓ` equation, explicitly. -/
theorem mem_gchar {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C} :
    q ∈ gchar A ℓ ↔
      ((∀ e ∈ A.edges ℓ,
          (¬ satisfies q.2 e.guard ∨
              (A.ibnd e.tgt : ℝ≥0) < resetListVal q.2 e.rst (A.iclock e.tgt)) ∨
          ∃ p', (gTLTS A).act q.1 e.act p' ∧ (p', resetListVal q.2 e.rst) ∈ gchar A e.tgt) ∧
       (∀ a p', (gTLTS A).act q.1 a p' → ∃ e ∈ A.edges ℓ, e.act = a ∧
          satisfies q.2 e.guard ∧ resetListVal q.2 e.rst (A.iclock e.tgt) ≤ (A.ibnd e.tgt : ℝ≥0) ∧
            (p', resetListVal q.2 e.rst) ∈ gchar A e.tgt) ∧
       (∀ t p', (gTLTS A).delay q.1 t p' → (p', q.2.add t) ∈ gchar A ℓ) ∧
       (∃ t p', (gTLTS A).delay q.1 t p' ∧ (q.2.add t) (A.iclock ℓ) = (A.ibnd ℓ : ℝ≥0) ∧
          (p', q.2.add t) ∈ gchar A ℓ)) := by
  have h : gchar A ℓ = denotSys (gTLTS A) (gbody A ℓ) (gchar A) := by
    rw [gchar]; exact recMaxSys_unfold (gTLTS A) (gbody A) ℓ
  conv_lhs => rw [h]
  simp only [gbody, greadiness, gsafety, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, denotSys_negConstraint, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
    satisfies, Cmp.holds, Finset.mem_toList, Finset.mem_univ, List.mem_filter, decide_eq_true_eq,
    forall_const, and_assoc]

/-! ### Soundness -/

/-- The candidate family: timed bisimilar to `(ℓ, q.2)` and valid. -/
def grel (A : GTA Loc C Act) : Loc → Set ((Loc × Valuation C) × Valuation C) :=
  fun ℓ => {q | TimedBisimilar (gTLTS A) q.1 (ℓ, q.2) ∧ q.2 (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0)}

/-- The bisimilarity-class family (restricted to valid states) is a post-fixed point. -/
theorem grel_postfixed :
    ∀ ℓ, grel A ℓ ⊆ denotSys (gTLTS A) (gbody A ℓ) (grel A) := by
  rintro ℓ ⟨p, u⟩ ⟨hb, hvalid⟩
  obtain ⟨haf, hab, hdf, hdb⟩ := (timedBisimilar_iff (gTLTS A) p (ℓ, u)).1 hb
  simp only [gbody, greadiness, gsafety, denotSys, denotSys_bigAnd_map, denotSys_bigOr_map,
    denotSys_resetAll, denotSys_negConstraint, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
    satisfies, Cmp.holds, Finset.mem_toList, Finset.mem_univ, List.mem_filter, decide_eq_true_eq,
    forall_const, grel]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- readiness
    intro e he
    by_cases hg : satisfies u e.guard
    · by_cases ht : resetListVal u e.rst (A.iclock e.tgt) ≤ (A.ibnd e.tgt : ℝ≥0)
      · obtain ⟨p', hp'a, hp'b⟩ := hab e.act (e.tgt, resetListVal u e.rst) (GStep.act he hg ht)
        exact Or.inr ⟨p', hp'a, hp'b, ht⟩
      · exact Or.inl (Or.inr (not_le.mp ht))
    · exact Or.inl (Or.inl hg)
  · -- safety
    intro a p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf a p' hp'a
    replace hr'a := gact.mp hr'a
    cases hr'a with
    | act he hg ht => exact ⟨_, ⟨he, rfl⟩, hg, ht, hr'b, ht⟩
  · -- ∀∀
    intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    replace hr'd := gdelay.mp hr'd
    cases hr'd with
    | delay _ _ _ _ h2 => exact ⟨hr'b, h2⟩
  · -- ∃∃ forcing
    obtain ⟨p', hp'd, hp'b⟩ :=
      hdb (A.ibnd ℓ - u (A.iclock ℓ)) (ℓ, u.add (A.ibnd ℓ - u (A.iclock ℓ)))
        (GStep.delay ℓ u (A.ibnd ℓ - u (A.iclock ℓ)) hvalid
          (le_of_eq (by simp only [Valuation.add_apply]; rw [add_tsub_cancel_of_le hvalid])))
    refine ⟨A.ibnd ℓ - u (A.iclock ℓ), p', hp'd, ?_, hp'b, ?_⟩
    · simp only [Valuation.add_apply]; rw [add_tsub_cancel_of_le hvalid]
    · exact le_of_eq (by simp only [Valuation.add_apply]; rw [add_tsub_cancel_of_le hvalid])

/-- **Soundness.** -/
theorem gchar_sound {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (hb : TimedBisimilar (gTLTS A) p (ℓ, u)) (hv : u (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0)) :
    (p, u) ∈ gchar A ℓ :=
  recMaxSys_coinduction (gTLTS A) (gbody A) grel_postfixed ℓ ⟨hb, hv⟩

/-! ### Completeness -/

/-- Membership forces validity. -/
theorem gchar_valid {ℓ : Loc} {q : (Loc × Valuation C) × Valuation C}
    (h : q ∈ gchar A ℓ) : q.2 (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0) := by
  obtain ⟨_, _, _, t, _, _, heq, _⟩ := mem_gchar.mp h
  rw [Valuation.add_apply] at heq
  exact heq ▸ le_self_add

/-- The satisfaction relation. -/
def gsatRel (A : GTA Loc C Act) : (Loc × Valuation C) → (Loc × Valuation C) → Prop :=
  fun a b => (a, b.2) ∈ gchar A b.1

/-- The satisfaction relation is a timed bisimulation. -/
theorem isBisimulation_gsatRel :
    LTS.IsBisimulation (gTLTS A) (gsatRel A) := by
  rintro ⟨ℓa, wa⟩ ⟨ℓ, v⟩ hab
  simp only [gsatRel] at hab
  obtain ⟨C1, C2, C3, C4⟩ := mem_gchar.mp hab
  have hvd : v (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0) := gchar_valid hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl b =>
      obtain ⟨e, he, hea, hg, ht, hmem⟩ := C2 b a' hstep
      subst hea
      exact ⟨(e.tgt, resetListVal v e.rst), GStep.act he hg ht, hmem⟩
    | inr t =>
      have hdval : (v.add t) (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0) := by
        have := gchar_valid (C3 t a' hstep); simpa using this
      exact ⟨(ℓ, v.add t), GStep.delay ℓ v t hvd hdval, C3 t a' hstep⟩
  · rintro lbl b' hstep
    cases lbl with
    | inl b =>
      replace hstep := gact.mp hstep
      cases hstep with
      | act he hg ht =>
        rcases C1 _ he with (hng | hngt) | ⟨p', hp'a, hmem⟩
        · exact absurd hg hng
        · exact absurd ht (not_le.mpr hngt)
        · exact ⟨p', hp'a, hmem⟩
    | inr t =>
      replace hstep := gdelay.mp hstep
      cases hstep with
      | delay _ _ _ _ h2 =>
        obtain ⟨s, a'', hsd, hseq, _⟩ := C4
        replace hsd := gdelay.mp hsd
        cases hsd with
        | delay _ _ _ h1s h2s =>
          rw [Valuation.add_apply] at hseq
          have hts : t ≤ s := by
            have hle : v (A.iclock ℓ) + t ≤ v (A.iclock ℓ) + s := by
              rw [hseq]; simpa [Valuation.add_apply] using h2
            exact le_of_add_le_add_left hle
          have hat : (gTLTS A).delay (ℓa, wa) t (ℓa, wa.add t) :=
            gdelay_prefix (gdelay.mpr (GStep.delay ℓa wa s h1s h2s)) hts
          exact ⟨(ℓa, wa.add t), hat, C3 t (ℓa, wa.add t) hat⟩

/-- **Completeness.** -/
theorem gchar_complete {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C}
    (h : (p, u) ∈ gchar A ℓ) : TimedBisimilar (gTLTS A) p (ℓ, u) :=
  isBisimulation_gsatRel.le_bisimilar (show gsatRel A p (ℓ, u) from h)

/-- **The characteristic theorem (standard timed automata, single-bound invariant).** `(p, v) ⊨ X_ℓ`
iff `p` is timed bisimilar to `(ℓ, v)` and `(ℓ, v)` is valid — actions gated by the target
invariant, arbitrary resets. -/
theorem gchar_iff {ℓ : Loc} {p : Loc × Valuation C} {u : Valuation C} :
    (p, u) ∈ gchar A ℓ ↔
      TimedBisimilar (gTLTS A) p (ℓ, u) ∧ u (A.iclock ℓ) ≤ (A.ibnd ℓ : ℝ≥0) :=
  ⟨fun h => ⟨gchar_complete h, gchar_valid h⟩, fun ⟨hb, hv⟩ => gchar_sound hb hv⟩

end TLTS

end DeepWiki.ReactiveSystems
