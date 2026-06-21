import DeepWiki.ReactiveSystems.TimedHmlMutualRecursion

/-! # Characteristic formulae with edges AND location invariants (delay-forcing)
The first construction combining *edges* and *location invariants*: a deterministic single-clock
timed automaton where each location `ℓ` has an `a`-edge guarded by `x ≤ gbnd ℓ` (reset, to
`succ ℓ`) and a location invariant `x ≤ ibnd ℓ` gating delays. The characteristic body folds the
edge readiness/safety (as in the deterministic construction) together with the **delay-forcing**
clause `∃∃(x = ibnd ℓ ∧ X_ℓ)` — a forceable delay-successor reaching the invariant boundary.
No `guard(x ≤ ibnd ℓ)` conjunct is needed: the forcing itself enforces validity (a state past the
bound cannot reach `x = ibnd ℓ`), so the characteristic theorem reads
`(p, [y=d]) ⊨ X_ℓ ↔ (p ~ (ℓ,d) ∧ d ≤ ibnd ℓ)`. This integrates the verified delay-forcing design
(`TimedInvariantDelayForcing`) with the edge machinery; the full multi-clock/nondeterministic
version (conjunctive-invariant boundary disjunction, target-invariant gating) remains. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Loc : Type*}

/-- SOS: `a` fires from `(ℓ,d)` while `d ≤ gbnd ℓ` (reset, to `(succ ℓ, 0)`); delays are gated by
the invariant `x ≤ ibnd ℓ` at both endpoints. -/
inductive IStep (gbnd ibnd : Loc → ℕ) (succ : Loc → Loc) :
    (Loc × ℝ≥0) → (Unit ⊕ ℝ≥0) → (Loc × ℝ≥0) → Prop
  /-- `(ℓ, d) —a→ (succ ℓ, 0)` while `d ≤ gbnd ℓ`. -/
  | act {ℓ : Loc} {d : ℝ≥0} (hg : d ≤ (gbnd ℓ : ℝ≥0)) :
      IStep gbnd ibnd succ (ℓ, d) (Sum.inl ()) (succ ℓ, 0)
  /-- `(ℓ, d) —t→ (ℓ, d+t)` while the invariant `x ≤ ibnd ℓ` holds at `d` and `d+t`. -/
  | delay (ℓ : Loc) (d t : ℝ≥0) (h1 : d ≤ (ibnd ℓ : ℝ≥0)) (h2 : d + t ≤ (ibnd ℓ : ℝ≥0)) :
      IStep gbnd ibnd succ (ℓ, d) (Sum.inr t) (ℓ, d + t)

/-- The automaton's TLTS. -/
def iTLTS (gbnd ibnd : Loc → ℕ) (succ : Loc → Loc) : TLTS (Loc × ℝ≥0) Unit :=
  ⟨IStep gbnd ibnd succ⟩

variable {gbnd ibnd : Loc → ℕ} {succ : Loc → Loc}

@[simp] theorem iact {q q' : Loc × ℝ≥0} :
    (iTLTS gbnd ibnd succ).act q () q' ↔ IStep gbnd ibnd succ q (Sum.inl ()) q' := Iff.rfl

@[simp] theorem idelay {q q' : Loc × ℝ≥0} {t : ℝ≥0} :
    (iTLTS gbnd ibnd succ).delay q t q' ↔ IStep gbnd ibnd succ q (Sum.inr t) q' := Iff.rfl

/-- **Delay prefix-closure**: if `(ℓ,d)` can delay `s`, it can delay any `t ≤ s` (convexity of the
upper-bound invariant). This is what lets the boundary-forcing cover *all* intermediate delays. -/
theorem idelay_prefix {ℓ : Loc} {d s t : ℝ≥0}
    (hs : (iTLTS gbnd ibnd succ).delay (ℓ, d) s (ℓ, d + s)) (hts : t ≤ s) :
    (iTLTS gbnd ibnd succ).delay (ℓ, d) t (ℓ, d + t) := by
  rw [idelay] at hs ⊢
  cases hs with
  | delay _ _ _ h1 h2 => exact IStep.delay ℓ d t h1 (le_trans (by gcongr) h2)

/-! ### The characteristic equation system -/

/-- The body of `X_ℓ`: readiness `(x ≤ gbnd ℓ ⇒ ⟨a⟩(x:=0 in X_{succ ℓ}))`, safety
`[a](x ≤ gbnd ℓ ∧ x:=0 in X_{succ ℓ})`, the delay-safety `∀∀X_ℓ`, and the **delay-forcing**
`∃∃(x = ibnd ℓ ∧ X_ℓ)`. -/
def ibody (gbnd ibnd : Loc → ℕ) (succ : Loc → Loc) (ℓ : Loc) : MtRSys Loc Unit Unit :=
  .and
    (.and
      (.or (.guard (.atom () .gt (gbnd ℓ))) (.dia () (.reset () (.var (succ ℓ)))))
      (.box () (.and (.guard (.atom () .le (gbnd ℓ))) (.reset () (.var (succ ℓ))))))
    (.and (.forallDelay (.var ℓ))
      (.existsDelay (.and (.guard (.atom () .eq (ibnd ℓ))) (.var ℓ))))

/-- The characteristic sets, one per location. -/
def ichar (gbnd ibnd : Loc → ℕ) (succ : Loc → Loc) : Loc → Set ((Loc × ℝ≥0) × Valuation Unit) :=
  recMaxSys (iTLTS gbnd ibnd succ) (ibody gbnd ibnd succ)

/-- The `X_ℓ` equation, explicitly. -/
theorem mem_ichar {ℓ : Loc} {q : (Loc × ℝ≥0) × Valuation Unit} :
    q ∈ ichar gbnd ibnd succ ℓ ↔
      (((gbnd ℓ : ℝ≥0) < q.2 () ∨ ∃ p', (iTLTS gbnd ibnd succ).act q.1 () p' ∧
            (p', Valuation.reset {()} q.2) ∈ ichar gbnd ibnd succ (succ ℓ)) ∧
       (∀ p', (iTLTS gbnd ibnd succ).act q.1 () p' →
            q.2 () ≤ (gbnd ℓ : ℝ≥0) ∧
            (p', Valuation.reset {()} q.2) ∈ ichar gbnd ibnd succ (succ ℓ)) ∧
       (∀ t p', (iTLTS gbnd ibnd succ).delay q.1 t p' → (p', q.2.add t) ∈ ichar gbnd ibnd succ ℓ) ∧
       (∃ t p', (iTLTS gbnd ibnd succ).delay q.1 t p' ∧ (q.2.add t) () = (ibnd ℓ : ℝ≥0) ∧
            (p', q.2.add t) ∈ ichar gbnd ibnd succ ℓ)) := by
  have h : ichar gbnd ibnd succ ℓ
      = denotSys (iTLTS gbnd ibnd succ) (ibody gbnd ibnd succ ℓ) (ichar gbnd ibnd succ) := by
    rw [ichar]; exact recMaxSys_unfold (iTLTS gbnd ibnd succ) (ibody gbnd ibnd succ) ℓ
  conv_lhs => rw [h]
  simp only [ibody, denotSys, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    Cmp.holds, and_assoc, gt_iff_lt]

/-! ### `Valuation Unit` bookkeeping -/

private theorem valUnit (u : Valuation Unit) : (fun _ => u ()) = u :=
  funext fun x => by cases x; rfl

private theorem reset_unit (d : ℝ≥0) :
    Valuation.reset ({()} : Set Unit) (fun _ => d) = fun _ => 0 := by
  funext x; cases x; simp [Valuation.reset]

private theorem add_unit (d t : ℝ≥0) :
    Valuation.add (fun _ : Unit => d) t = fun _ => d + t := rfl

/-! ### Soundness -/

/-- The candidate family: `(q, u) ∈ irel ℓ` iff `q` is timed bisimilar to `(ℓ, u())` *and* `u()`
respects the invariant (the canonical state is valid). -/
def irel (gbnd ibnd : Loc → ℕ) (succ : Loc → Loc) : Loc → Set ((Loc × ℝ≥0) × Valuation Unit) :=
  fun ℓ => {q | TimedBisimilar (iTLTS gbnd ibnd succ) q.1 (ℓ, q.2 ()) ∧ q.2 () ≤ (ibnd ℓ : ℝ≥0)}

/-- The bisimilarity-class family (restricted to valid states) is a post-fixed point. -/
theorem irel_postfixed :
    ∀ ℓ, irel gbnd ibnd succ ℓ ⊆ denotSys (iTLTS gbnd ibnd succ) (ibody gbnd ibnd succ ℓ)
      (irel gbnd ibnd succ) := by
  rintro ℓ ⟨p, u⟩ ⟨hb, hvalid⟩
  obtain ⟨haf, hab, hdf, hdb⟩ := (timedBisimilar_iff (iTLTS gbnd ibnd succ) p (ℓ, u ())).1 hb
  have hr0 : Valuation.reset ({()} : Set Unit) u () = 0 := Valuation.reset_mem rfl u
  simp only [ibody, denotSys, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    Cmp.holds, irel]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- readiness
    by_cases hg : u () ≤ (gbnd ℓ : ℝ≥0)
    · obtain ⟨p', hp'a, hp'b⟩ := hab () (succ ℓ, 0) (IStep.act hg)
      exact Or.inr ⟨p', hp'a, by rw [hr0]; exact hp'b, by rw [hr0]; exact zero_le⟩
    · exact Or.inl (not_le.mp hg)
  · -- safety
    intro p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf () p' hp'a
    rw [iact] at hr'a
    cases hr'a with
    | act hg => exact ⟨hg, by rw [hr0]; exact hr'b, by rw [hr0]; exact zero_le⟩
  · -- ∀∀ (delay safety)
    intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    rw [idelay] at hr'd
    cases hr'd with
    | delay _ _ _ _ h2 =>
      simp only [Valuation.add_apply]
      exact ⟨hr'b, h2⟩
  · -- ∃∃ (delay forcing): delay ibnd ℓ - u() to the boundary
    obtain ⟨p', hp'd, hp'b⟩ :=
      hdb (ibnd ℓ - u ()) (ℓ, u () + (ibnd ℓ - u ()))
        (IStep.delay ℓ (u ()) (ibnd ℓ - u ()) hvalid (le_of_eq (add_tsub_cancel_of_le hvalid)))
    rw [add_tsub_cancel_of_le hvalid] at hp'b
    refine ⟨ibnd ℓ - u (), p', hp'd, ?_, ?_⟩
    · simp only [Valuation.add_apply]; rw [add_tsub_cancel_of_le hvalid]
    · simp only [Valuation.add_apply, add_tsub_cancel_of_le hvalid]
      exact ⟨hp'b, le_refl _⟩

/-! ### Completeness -/

/-- Membership forces validity: the boundary-forcing clause `∃∃(x = ibnd ℓ)` implies `x ≤ ibnd ℓ`. -/
theorem ichar_valid {ℓ : Loc} {q : (Loc × ℝ≥0) × Valuation Unit}
    (h : q ∈ ichar gbnd ibnd succ ℓ) : q.2 () ≤ (ibnd ℓ : ℝ≥0) := by
  obtain ⟨_, _, _, t, _, _, heq, _⟩ := mem_ichar.mp h
  rw [Valuation.add_apply] at heq
  exact heq ▸ le_self_add

/-- The satisfaction relation: relate `a` to canonical `(ℓ, d)` when `(a, [y=d]) ⊨ X_ℓ`. -/
def isatRel (gbnd ibnd : Loc → ℕ) (succ : Loc → Loc) :
    (Loc × ℝ≥0) → (Loc × ℝ≥0) → Prop :=
  fun a b => (a, fun _ => b.2) ∈ ichar gbnd ibnd succ b.1

/-- The satisfaction relation is a timed bisimulation: the back-delay is matched using the
boundary-forcing (`C4`) plus delay prefix-closure. -/
theorem isBisimulation_isatRel :
    LTS.IsBisimulation (iTLTS gbnd ibnd succ) (isatRel gbnd ibnd succ) := by
  rintro ⟨ℓa, wa⟩ ⟨ℓ, d⟩ hab
  simp only [isatRel] at hab
  obtain ⟨C1, C2, C3, C4⟩ := mem_ichar.mp hab
  have hd : d ≤ (ibnd ℓ : ℝ≥0) := ichar_valid hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl u =>
      obtain ⟨⟩ := u
      obtain ⟨hg, hmem⟩ := C2 a' hstep
      refine ⟨(succ ℓ, 0), IStep.act hg, ?_⟩
      simp only [isatRel]; rw [reset_unit] at hmem; exact hmem
    | inr t =>
      have hdval : d + t ≤ (ibnd ℓ : ℝ≥0) := ichar_valid (C3 t a' hstep)
      exact ⟨(ℓ, d + t), IStep.delay ℓ d t hd hdval, C3 t a' hstep⟩
  · rintro lbl b' hstep
    cases lbl with
    | inl u =>
      obtain ⟨⟩ := u
      replace hstep := iact.mp hstep
      cases hstep with
      | act hg =>
        rcases C1 with hgt | ⟨p', hp'a, hmem⟩
        · exact absurd hgt (not_lt.mpr hg)
        · refine ⟨p', hp'a, ?_⟩
          simp only [isatRel]; rw [reset_unit] at hmem; exact hmem
    | inr t =>
      replace hstep := idelay.mp hstep
      cases hstep with
      | delay _ _ _ _ h2 =>
        obtain ⟨s, a'', hsd, hseq, _⟩ := C4
        rw [Valuation.add_apply] at hseq
        rw [idelay] at hsd
        cases hsd with
        | delay _ _ _ h1s h2s =>
          have hts : t ≤ s := by
            have hle : d + t ≤ d + s := by rw [hseq]; exact h2
            exact le_of_add_le_add_left hle
          have hat : (iTLTS gbnd ibnd succ).delay (ℓa, wa) t (ℓa, wa + t) :=
            idelay_prefix (idelay.mpr (IStep.delay ℓa wa s h1s h2s)) hts
          exact ⟨(ℓa, wa + t), hat, C3 t (ℓa, wa + t) hat⟩

/-- **Completeness.** A state satisfying `X_ℓ` at `[y=d]` is timed bisimilar to `(ℓ, d)`. -/
theorem ichar_complete {ℓ : Loc} {p : Loc × ℝ≥0} {u : Valuation Unit}
    (h : (p, u) ∈ ichar gbnd ibnd succ ℓ) : TimedBisimilar (iTLTS gbnd ibnd succ) p (ℓ, u ()) :=
  isBisimulation_isatRel.le_bisimilar
    (show isatRel gbnd ibnd succ p (ℓ, u ()) by simp only [isatRel]; rwa [valUnit])

/-- **Soundness.** A state timed bisimilar to a *valid* `(ℓ, d)` satisfies `X_ℓ` at `[y=d]`. -/
theorem ichar_sound {ℓ : Loc} {p : Loc × ℝ≥0} {u : Valuation Unit}
    (hb : TimedBisimilar (iTLTS gbnd ibnd succ) p (ℓ, u ())) (hv : u () ≤ (ibnd ℓ : ℝ≥0)) :
    (p, u) ∈ ichar gbnd ibnd succ ℓ :=
  recMaxSys_coinduction (iTLTS gbnd ibnd succ) (ibody gbnd ibnd succ) irel_postfixed ℓ ⟨hb, hv⟩

/-- **The characteristic theorem with invariants.** `(p, [y=d]) ⊨ X_ℓ` iff `p` is timed bisimilar
to `(ℓ, d)` and `(ℓ, d)` is valid (`d ≤ ibnd ℓ`). The delay-forcing clause supplies both the
matching delays and the validity. -/
theorem ichar_iff {ℓ : Loc} {p : Loc × ℝ≥0} {u : Valuation Unit} :
    (p, u) ∈ ichar gbnd ibnd succ ℓ ↔
      TimedBisimilar (iTLTS gbnd ibnd succ) p (ℓ, u ()) ∧ u () ≤ (ibnd ℓ : ℝ≥0) :=
  ⟨fun h => ⟨ichar_complete h, ichar_valid h⟩, fun ⟨hb, hv⟩ => ichar_sound hb hv⟩

end TLTS

end DeepWiki.ReactiveSystems
