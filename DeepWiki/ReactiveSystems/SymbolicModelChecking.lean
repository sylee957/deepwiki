import DeepWiki.ReactiveSystems.TimedRegionsBisimulation
import DeepWiki.ReactiveSystems.TimedHmlClocks
import DeepWiki.ReactiveSystems.TimedHmlIntervalDelay

/-! # Symbolic model checking — combined-clock plumbing (§12.2)
Theorem 12.1 relates concrete satisfaction `((ℓ,v),u) ⊨ F` (automaton clocks `v`
over `C`, formula clocks `u` over `D`) to symbolic satisfaction `[ℓ, [vu]] ⊢ F`,
where `vu` is the combined valuation over the disjoint union `C ⊎ D`. We model
`C ∪ D` as the sum type `C ⊕ D` and `vu` as `combineVal v u = Sum.elim v u`, and
record the bridge lemmas tying the combined valuation to its two components under
the operations the symbolic clauses use: delay (`+ t` on both), an automaton-clock
reset (`Sum.inl '' r`, hitting only `C`), and a formula-clock reset (`Sum.inr x`,
hitting only `D`). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {C D : Type*}

/-- The combined valuation `vu` over `C ⊕ D` from an automaton-clock valuation `v`
and a formula-clock valuation `u`: `vu (inl c) = v c`, `vu (inr d) = u d`. -/
def combineVal (v : Valuation C) (u : Valuation D) : Valuation (C ⊕ D) := Sum.elim v u

@[simp] theorem combineVal_inl (v : Valuation C) (u : Valuation D) (c : C) :
    combineVal v u (Sum.inl c) = v c := rfl

@[simp] theorem combineVal_inr (v : Valuation C) (u : Valuation D) (d : D) :
    combineVal v u (Sum.inr d) = u d := rfl

/-- A delay advances both components: `(vu) + t = (v+t)(u+t)`. -/
theorem combineVal_add (v : Valuation C) (u : Valuation D) (t : ℝ≥0) :
    (combineVal v u).add t = combineVal (v.add t) (u.add t) := by
  funext x; cases x <;> simp [combineVal, Valuation.add_apply]

/-- Resetting the automaton clocks `Sum.inl '' r` in the combined valuation resets
`r` in the `C`-component and leaves the `D`-component untouched. -/
theorem reset_inl_combineVal (r : Set C) (v : Valuation C) (u : Valuation D) :
    Valuation.reset (Sum.inl '' r) (combineVal v u) = combineVal (Valuation.reset r v) u := by
  funext z
  cases z with
  | inl c => by_cases h : c ∈ r <;> simp [Valuation.reset, combineVal, Set.mem_image, h]
  | inr d => simp [Valuation.reset, combineVal, Set.mem_image]

/-- Resetting a single formula clock `Sum.inr x` in the combined valuation resets
`x` in the `D`-component and leaves the `C`-component untouched. -/
theorem reset_inr_combineVal (x : D) (v : Valuation C) (u : Valuation D) :
    Valuation.reset {Sum.inr x} (combineVal v u) = combineVal v (Valuation.reset {x} u) := by
  funext z
  cases z with
  | inl c => simp [Valuation.reset, combineVal, Set.mem_singleton_iff]
  | inr d =>
      by_cases h : d = x <;>
        simp [Valuation.reset, combineVal, Set.mem_singleton_iff, Sum.inr.injEq, h]

/-- The base case of Theorem 12.1's combined valuation: both components zero. -/
@[simp] theorem combineVal_zero :
    combineVal (fun _ : C => (0 : ℝ≥0)) (fun _ : D => (0 : ℝ≥0)) = fun _ => 0 := by
  funext x; cases x <;> rfl

variable {Loc Act : Type*}

/-- **Definition 12.5: symbolic satisfaction** `[ℓ, γ] ⊢ F`, on a representative
combined valuation `w : Valuation (C ⊕ D)`. Action modalities follow the automaton's
edges (guard and target invariant over the `C`-clocks `w ∘ inl`, edge reset on those
clocks); the delay quantifiers advance the whole valuation requiring the location
invariant before and after (faithfully matching `A.tlts`, which enforces both — Def
12.5 as printed lists only the post-invariant and omits the routine `x in`/guard
clauses, recovered here as the `D`-clock reset and the `D`-clock constraint). -/
noncomputable def SymSat (A : TimedAutomaton Loc Act C) :
    Loc → Valuation (C ⊕ D) → Mt Act D → Prop
  | _, _, .tt => True
  | _, _, .ff => False
  | ℓ, w, .and F G => SymSat A ℓ w F ∧ SymSat A ℓ w G
  | ℓ, w, .or F G => SymSat A ℓ w F ∨ SymSat A ℓ w G
  | ℓ, w, .dia a F => ∃ ℓ' g r, A.edge ℓ g a r ℓ' ∧ satisfies (fun c => w (Sum.inl c)) g ∧
      satisfies (fun c => Valuation.reset (Sum.inl '' r) w (Sum.inl c)) (A.inv ℓ') ∧
      SymSat A ℓ' (Valuation.reset (Sum.inl '' r) w) F
  | ℓ, w, .box a F => ∀ ℓ' g r, A.edge ℓ g a r ℓ' → satisfies (fun c => w (Sum.inl c)) g →
      satisfies (fun c => Valuation.reset (Sum.inl '' r) w (Sum.inl c)) (A.inv ℓ') →
      SymSat A ℓ' (Valuation.reset (Sum.inl '' r) w) F
  | ℓ, w, .existsDelay F => ∃ t : ℝ≥0, satisfies (fun c => w (Sum.inl c)) (A.inv ℓ) ∧
      satisfies (fun c => (w.add t) (Sum.inl c)) (A.inv ℓ) ∧ SymSat A ℓ (w.add t) F
  | ℓ, w, .forallDelay F => ∀ t : ℝ≥0, satisfies (fun c => w (Sum.inl c)) (A.inv ℓ) →
      satisfies (fun c => (w.add t) (Sum.inl c)) (A.inv ℓ) → SymSat A ℓ (w.add t) F
  | ℓ, w, .reset x F => SymSat A ℓ (Valuation.reset {Sum.inr x} w) F
  | _, w, .guard g => satisfies (fun d => w (Sum.inr d)) g

/-- **Theorem 12.1: symbolic model checking agrees with concrete model checking.**
For a timed automaton `A` (clocks `C`) and an `Mt` formula over formula clocks `D`,
an extended state `((ℓ,v), u)` satisfies `F` iff the symbolic state `[ℓ, vu]`
satisfies `F`, where `vu = combineVal v u`. Proved by structural induction on `F`,
each clause discharged by the combined-clock bridge lemmas and the `tlts` transition
unfoldings — no region reasoning is needed (that is the separate region-invariance
of `SymSat`). -/
theorem mtSat_iff_symSat (A : TimedAutomaton Loc Act C) (F : Mt Act D) :
    ∀ (ℓ : Loc) (v : Valuation C) (u : Valuation D),
      A.tlts.MtSat (ℓ, v) u F ↔ SymSat A ℓ (combineVal v u) F := by
  induction F with
  | tt => intro _ _ _; exact Iff.rfl
  | ff => intro _ _ _; exact Iff.rfl
  | and F G ihF ihG => intro ℓ v u; exact and_congr (ihF ℓ v u) (ihG ℓ v u)
  | or F G ihF ihG => intro ℓ v u; exact or_congr (ihF ℓ v u) (ihG ℓ v u)
  | guard g => intro _ _ _; exact Iff.rfl
  | reset x F ihF =>
      intro ℓ v u
      show A.tlts.MtSat (ℓ, v) (Valuation.reset {x} u) F ↔
        SymSat A ℓ (Valuation.reset {Sum.inr x} (combineVal v u)) F
      rw [reset_inr_combineVal]
      exact ihF ℓ v (Valuation.reset {x} u)
  | dia a F ihF =>
      intro ℓ v u
      constructor
      · rintro ⟨⟨ℓ', v'⟩, hact, hsat⟩
        rw [TimedAutomaton.tlts_act_iff] at hact
        obtain ⟨g, r, hedge, hg, rfl, hinv⟩ := hact
        refine ⟨ℓ', g, r, hedge, hg, ?_, ?_⟩ <;> rw [reset_inl_combineVal]
        · exact hinv
        · exact (ihF ℓ' (Valuation.reset r v) u).mp hsat
      · rintro ⟨ℓ', g, r, hedge, hg, hinv, hsym⟩
        rw [reset_inl_combineVal] at hinv hsym
        refine ⟨(ℓ', Valuation.reset r v), ?_, (ihF ℓ' (Valuation.reset r v) u).mpr hsym⟩
        rw [TimedAutomaton.tlts_act_iff]; exact ⟨g, r, hedge, hg, rfl, hinv⟩
  | box a F ihF =>
      intro ℓ v u
      constructor
      · intro hbox ℓ' g r hedge hg hinv
        rw [reset_inl_combineVal] at hinv ⊢
        refine (ihF ℓ' (Valuation.reset r v) u).mp (hbox (ℓ', Valuation.reset r v) ?_)
        rw [TimedAutomaton.tlts_act_iff]; exact ⟨g, r, hedge, hg, rfl, hinv⟩
      · rintro hsym ⟨ℓ', v'⟩ hact
        rw [TimedAutomaton.tlts_act_iff] at hact
        obtain ⟨g, r, hedge, hg, rfl, hinv⟩ := hact
        have := hsym ℓ' g r hedge hg (by rw [reset_inl_combineVal]; exact hinv)
        rw [reset_inl_combineVal] at this
        exact (ihF ℓ' (Valuation.reset r v) u).mpr this
  | existsDelay F ihF =>
      intro ℓ v u
      constructor
      · rintro ⟨d, ⟨ℓ', v'⟩, hdel, hsat⟩
        rw [TimedAutomaton.tlts_delay_iff] at hdel
        obtain ⟨rfl, rfl, hpre, hpost⟩ := hdel
        refine ⟨d, hpre, hpost, ?_⟩
        rw [combineVal_add]; exact (ihF ℓ' (v.add d) (u.add d)).mp hsat
      · rintro ⟨t, hpre, hpost, hsym⟩
        rw [combineVal_add] at hsym
        refine ⟨t, (ℓ, v.add t), ?_, (ihF ℓ (v.add t) (u.add t)).mpr hsym⟩
        rw [TimedAutomaton.tlts_delay_iff]; exact ⟨rfl, rfl, hpre, hpost⟩
  | forallDelay F ihF =>
      intro ℓ v u
      constructor
      · intro hall t hpre hpost
        rw [combineVal_add]
        exact (ihF ℓ (v.add t) (u.add t)).mp (hall t (ℓ, v.add t) (by rw [TimedAutomaton.tlts_delay_iff]; exact ⟨rfl, rfl, hpre, hpost⟩))
      · rintro hsym t ⟨ℓ', v'⟩ hdel
        rw [TimedAutomaton.tlts_delay_iff] at hdel
        obtain ⟨rfl, rfl, hpre, hpost⟩ := hdel
        have := hsym t hpre hpost
        rw [combineVal_add] at this
        exact (ihF ℓ' (v.add t) (u.add t)).mpr this

/-- **Theorem 12.1, state form.** Starting every formula clock at zero, a state
`(ℓ, v)` satisfies `F` (Def 12.4) iff the symbolic state `[ℓ, v0]` does. -/
theorem satisfiesMtState_iff_symSat (A : TimedAutomaton Loc Act C) (ℓ : Loc)
    (v : Valuation C) (F : Mt Act D) :
    A.tlts.MtSatState (ℓ, v) F ↔ SymSat A ℓ (combineVal v (fun _ => 0)) F :=
  mtSat_iff_symSat A F ℓ v (fun _ => 0)

/-! ## Symbolic satisfaction is region-determined

`SymSat` depends on its combined valuation only through that valuation's region —
the finiteness fact underlying the *symbolic* (region-quotient) reading of Def 12.5
and the decidability of timed model checking (Theorem 12.2). -/

variable [Fintype C] [Fintype D]

/-- **`SymSat` is invariant under region equivalence of the combined valuation.**
Region-equivalent valuations (over `C ⊕ D`) satisfy exactly the same `Mt` formulae
symbolically, so `[ℓ, γ] ⊢ F` descends to the region `γ`. The guard/reset clauses use
`regionEqAll_satisfies`/`RegionEqAll.reset` (restricted to `C`/`D` via
`RegionEqAll.precomp`); the delay clauses use the region time-successor
`regionEqAll_timeSuccessor` to match each delay by a region-preserving one. -/
theorem symSat_congr (A : TimedAutomaton Loc Act C) (F : Mt Act D) :
    ∀ {ℓ : Loc} {w w' : Valuation (C ⊕ D)}, RegionEqAll w w' →
      (SymSat A ℓ w F ↔ SymSat A ℓ w' F) := by
  induction F with
  | tt => intro _ _ _ _; exact Iff.rfl
  | ff => intro _ _ _ _; exact Iff.rfl
  | and F G ihF ihG => intro _ _ _ h; exact and_congr (ihF h) (ihG h)
  | or F G ihF ihG => intro _ _ _ h; exact or_congr (ihF h) (ihG h)
  | guard g => intro _ _ _ h; exact regionEqAll_satisfies (h.precomp Sum.inr_injective) g
  | reset x F ihF => intro _ _ _ h; exact ihF (h.reset {Sum.inr x})
  | dia a F ihF =>
      intro ℓ w w' h
      refine exists_congr fun ℓ' => exists_congr fun g => exists_congr fun r =>
        and_congr Iff.rfl (and_congr ?_ (and_congr ?_ (ihF (h.reset (Sum.inl '' r)))))
      · exact regionEqAll_satisfies (h.precomp Sum.inl_injective) g
      · exact regionEqAll_satisfies ((h.reset (Sum.inl '' r)).precomp Sum.inl_injective) (A.inv ℓ')
  | box a F ihF =>
      intro ℓ w w' h
      refine forall_congr' fun ℓ' => forall_congr' fun g => forall_congr' fun r =>
        imp_congr Iff.rfl (imp_congr ?_ (imp_congr ?_ (ihF (h.reset (Sum.inl '' r)))))
      · exact regionEqAll_satisfies (h.precomp Sum.inl_injective) g
      · exact regionEqAll_satisfies ((h.reset (Sum.inl '' r)).precomp Sum.inl_injective) (A.inv ℓ')
  | existsDelay F ihF =>
      intro ℓ w w' h
      constructor
      · rintro ⟨t, hpre, hpost, hsym⟩
        obtain ⟨t', ht'⟩ := regionEqAll_timeSuccessor h t
        exact ⟨t', (regionEqAll_satisfies (h.precomp Sum.inl_injective) (A.inv ℓ)).mp hpre,
          (regionEqAll_satisfies (ht'.precomp Sum.inl_injective) (A.inv ℓ)).mp hpost,
          (ihF ht').mp hsym⟩
      · rintro ⟨t', hpre, hpost, hsym⟩
        obtain ⟨t, ht⟩ := regionEqAll_timeSuccessor h.symm t'
        exact ⟨t, (regionEqAll_satisfies (h.precomp Sum.inl_injective) (A.inv ℓ)).mpr hpre,
          (regionEqAll_satisfies (ht.precomp Sum.inl_injective) (A.inv ℓ)).mp hpost,
          (ihF ht).mp hsym⟩
  | forallDelay F ihF =>
      intro ℓ w w' h
      constructor
      · intro hall t' hpre hpost
        obtain ⟨t, ht⟩ := regionEqAll_timeSuccessor h.symm t'
        exact (ihF ht).mpr (hall t ((regionEqAll_satisfies (h.precomp Sum.inl_injective) (A.inv ℓ)).mpr hpre)
          ((regionEqAll_satisfies (ht.precomp Sum.inl_injective) (A.inv ℓ)).mp hpost))
      · intro hall t hpre hpost
        obtain ⟨t', ht'⟩ := regionEqAll_timeSuccessor h t
        exact (ihF ht').mpr (hall t' ((regionEqAll_satisfies (h.precomp Sum.inl_injective) (A.inv ℓ)).mp hpre)
          ((regionEqAll_satisfies (ht'.precomp Sum.inl_injective) (A.inv ℓ)).mp hpost))

/-! ## The region-quotient form of Def 12.5

`symSat_congr` says `SymSat` factors through region equivalence, so it descends to a
genuine relation on region classes — the verbatim reading of Def 12.5 where `[ℓ, γ]`
has `γ` a region of `C ⊕ D`. (Decidability of model checking — Theorem 12.2 — uses in
addition that the *bounded* region quotient `Region cmax` is finite; that bounded
descent and its `Decidable` instance are left as the remaining mechanical step.) -/

/-- The setoid of combined valuations under unbounded region equivalence. -/
def regionAllSetoid (C : Type*) : Setoid (Valuation C) where
  r := RegionEqAll
  iseqv := ⟨RegionEqAll.refl, RegionEqAll.symm, RegionEqAll.trans⟩

/-- **Definition 12.5, region form.** Symbolic satisfaction `[ℓ, γ] ⊢ F` with `γ` a
genuine *region* — an equivalence class of combined valuations over `C ⊕ D` — as
`SymSat` descended to the region quotient (well-defined by `symSat_congr`). -/
def SymSatRegion (A : TimedAutomaton Loc Act C) (ℓ : Loc)
    (γ : Quotient (regionAllSetoid (C ⊕ D))) (F : Mt Act D) : Prop :=
  Quotient.liftOn γ (fun w => SymSat A ℓ w F) (fun _ _ h => propext (symSat_congr A F h))

/-- `[ℓ, ⟦w⟧] ⊢ F` reduces to `SymSat` on the representative `w`. -/
@[simp] theorem symSatRegion_mk (A : TimedAutomaton Loc Act C) (ℓ : Loc)
    (w : Valuation (C ⊕ D)) (F : Mt Act D) :
    SymSatRegion A ℓ (Quotient.mk (regionAllSetoid (C ⊕ D)) w) F ↔ SymSat A ℓ w F :=
  Iff.rfl

/-- **Theorem 12.1, region form.** `((ℓ,v), u) ⊨ F ↔ [ℓ, ⟦vu⟧] ⊢ F`, with `⟦vu⟧` the
region of the combined valuation. -/
theorem mtSat_iff_symSatRegion (A : TimedAutomaton Loc Act C) (F : Mt Act D)
    (ℓ : Loc) (v : Valuation C) (u : Valuation D) :
    A.tlts.MtSat (ℓ, v) u F ↔
      SymSatRegion A ℓ (Quotient.mk (regionAllSetoid (C ⊕ D)) (combineVal v u)) F :=
  mtSat_iff_symSat A F ℓ v u

end DeepWiki.ReactiveSystems
