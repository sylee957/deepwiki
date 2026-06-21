import DeepWiki.ReactiveSystems.TimedHmlMutualRecursion

/-! # Characteristic formulae for deterministic single-clock timed automata (generic)
The generic construction behind Theorem 12.4 for the class of **deterministic, single-clock**
timed automata over an *arbitrary* location set `Loc`: each location `ℓ` has one guarded
`a`-edge `x ≤ bound ℓ` to `succ ℓ`, resetting the clock, with free delays. Variables are
indexed by `Loc` (one equation per location); the formula clock `y` mirrors the automaton
clock. The characteristic system
`X_ℓ =ν (y ≤ bound ℓ ⇒ ⟨a⟩(y in X_{succ ℓ})) ∧ [a](y ≤ bound ℓ ∧ y in X_{succ ℓ}) ∧ ∀∀X_ℓ`
characterises timed bisimilarity: `(q, [y = d]) ⊨ X_ℓ ↔ q ~ (ℓ, d)`. This subsumes the
running example (`Loc = Unit`, `bound = 1`) and the alternating example (`Loc = Bool`,
`bound = 1/2`), now uniformly and for any location graph. The remaining gap to full Theorem
12.4 is multi-clock / multi-edge / invariant automata, whose bodies fold over a finite edge
presentation. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Loc : Type*}

/-! ### The generic deterministic single-clock automaton -/

/-- SOS: from `(ℓ, d)`, `a` fires while `d ≤ bound ℓ` (to `(succ ℓ, 0)`); time elapses freely. -/
inductive GenStep (bound : Loc → ℕ) (succ : Loc → Loc) :
    (Loc × ℝ≥0) → (Unit ⊕ ℝ≥0) → (Loc × ℝ≥0) → Prop
  /-- `(ℓ, d) —a→ (succ ℓ, 0)` while `d ≤ bound ℓ`. -/
  | act {ℓ : Loc} {d : ℝ≥0} (h : d ≤ (bound ℓ : ℝ≥0)) :
      GenStep bound succ (ℓ, d) (Sum.inl ()) (succ ℓ, 0)
  /-- `(ℓ, d)` delays freely. -/
  | delay (ℓ : Loc) (d t : ℝ≥0) : GenStep bound succ (ℓ, d) (Sum.inr t) (ℓ, d + t)

/-- The generic automaton as a TLTS (states are location/clock pairs). -/
def genTLTS (bound : Loc → ℕ) (succ : Loc → Loc) : TLTS (Loc × ℝ≥0) Unit := ⟨GenStep bound succ⟩

@[simp] theorem gen_act {bound : Loc → ℕ} {succ : Loc → Loc} {q q' : Loc × ℝ≥0} :
    (genTLTS bound succ).act q () q' ↔ GenStep bound succ q (Sum.inl ()) q' := Iff.rfl

@[simp] theorem gen_delay {bound : Loc → ℕ} {succ : Loc → Loc} {q q' : Loc × ℝ≥0} {t : ℝ≥0} :
    (genTLTS bound succ).delay q t q' ↔ GenStep bound succ q (Sum.inr t) q' := Iff.rfl

/-- Every state can delay by any duration. -/
theorem gen_can_delay (bound : Loc → ℕ) (succ : Loc → Loc) (q : Loc × ℝ≥0) (t : ℝ≥0) :
    ∃ q', (genTLTS bound succ).delay q t q' :=
  ⟨_, GenStep.delay q.1 q.2 t⟩

/-! ### The characteristic equation system (one variable per location) -/

/-- The body of `X_ℓ`: `(y > bound ℓ ∨ ⟨a⟩(y in X_{succ ℓ})) ∧ [a](y ≤ bound ℓ ∧ y in X_{succ ℓ})
∧ ∀∀X_ℓ`. -/
def genBody (bound : Loc → ℕ) (succ : Loc → Loc) (ℓ : Loc) : MtRSys Loc Unit Unit :=
  .and
    (.and
      (.or (.guard (.atom () .gt (bound ℓ))) (.dia () (.reset () (.var (succ ℓ)))))
      (.box () (.and (.guard (.atom () .le (bound ℓ))) (.reset () (.var (succ ℓ))))))
    (.forallDelay (.var ℓ))

/-- The characteristic sets, one per location. -/
def genChar (bound : Loc → ℕ) (succ : Loc → Loc) : Loc → Set ((Loc × ℝ≥0) × Valuation Unit) :=
  recMaxSys (genTLTS bound succ) (genBody bound succ)

/-- The `X_ℓ` equation, explicitly (per-variable fixed-point unfolding). -/
theorem mem_genChar {bound : Loc → ℕ} {succ : Loc → Loc} {ℓ : Loc}
    {q : (Loc × ℝ≥0) × Valuation Unit} :
    q ∈ genChar bound succ ℓ ↔
      (((bound ℓ : ℝ≥0) < q.2 () ∨ ∃ p', (genTLTS bound succ).act q.1 () p' ∧
            (p', Valuation.reset {()} q.2) ∈ genChar bound succ (succ ℓ)) ∧
       (∀ p', (genTLTS bound succ).act q.1 () p' →
            q.2 () ≤ (bound ℓ : ℝ≥0) ∧ (p', Valuation.reset {()} q.2) ∈ genChar bound succ (succ ℓ)) ∧
       (∀ t p', (genTLTS bound succ).delay q.1 t p' → (p', q.2.add t) ∈ genChar bound succ ℓ)) := by
  have h : genChar bound succ ℓ = denotSys (genTLTS bound succ) (genBody bound succ ℓ)
      (genChar bound succ) := by
    rw [genChar]; exact recMaxSys_unfold (genTLTS bound succ) (genBody bound succ) ℓ
  conv_lhs => rw [h]
  simp only [genBody, denotSys, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    Cmp.holds, and_assoc, gt_iff_lt]

/-! ### `Valuation Unit` bookkeeping -/

private theorem valUnit (u : Valuation Unit) : (fun _ => u ()) = u :=
  funext fun x => by cases x; rfl

private theorem reset_unit (d : ℝ≥0) :
    Valuation.reset ({()} : Set Unit) (fun _ => d) = fun _ => 0 := by
  funext x; cases x; simp [Valuation.reset]

private theorem add_unit (d t : ℝ≥0) :
    Valuation.add (fun _ : Unit => d) t = fun _ => d + t := rfl

/-! ### Soundness: timed bisimilarity to a location implies satisfaction -/

/-- The candidate family: `(q, u) ∈ genRel ℓ` iff `q` is timed bisimilar to `(ℓ, u(y))`. -/
def genRel (bound : Loc → ℕ) (succ : Loc → Loc) : Loc → Set ((Loc × ℝ≥0) × Valuation Unit) :=
  fun ℓ => {q | TimedBisimilar (genTLTS bound succ) q.1 (ℓ, q.2 ())}

/-- The bisimilarity-class family is a post-fixed point of the equation system. -/
theorem genRel_postfixed (bound : Loc → ℕ) (succ : Loc → Loc) :
    ∀ ℓ, genRel bound succ ℓ ⊆ denotSys (genTLTS bound succ) (genBody bound succ ℓ)
      (genRel bound succ) := by
  rintro ℓ ⟨p, u⟩ hb
  simp only [genRel, Set.mem_setOf_eq] at hb
  obtain ⟨haf, hab, hdf, _⟩ := (timedBisimilar_iff (genTLTS bound succ) p (ℓ, u ())).1 hb
  simp only [genBody, denotSys, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    Cmp.holds, genRel]
  have h0 : Valuation.reset ({()} : Set Unit) u () = 0 := Valuation.reset_mem rfl u
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_cases h1 : u () ≤ (bound ℓ : ℝ≥0)
    · obtain ⟨p', hp'a, hp'b⟩ := hab () (succ ℓ, 0) (GenStep.act h1)
      refine Or.inr ⟨p', hp'a, ?_⟩
      show TimedBisimilar (genTLTS bound succ) p' (succ ℓ, Valuation.reset {()} u ())
      rw [h0]; exact hp'b
    · exact Or.inl (not_le.mp h1)
  · intro p' hp'a
    obtain ⟨r', hr'a, hr'b⟩ := haf () p' hp'a
    replace hr'a := gen_act.mp hr'a
    cases hr'a with
    | act hle =>
      refine ⟨hle, ?_⟩
      show TimedBisimilar (genTLTS bound succ) p' (succ ℓ, Valuation.reset {()} u ())
      rw [h0]; exact hr'b
  · intro t p' hp'd
    obtain ⟨r', hr'd, hr'b⟩ := hdf t p' hp'd
    replace hr'd := gen_delay.mp hr'd
    cases hr'd with
    | delay => rw [Valuation.add_apply]; exact hr'b

/-- **Soundness.** A state timed bisimilar to `(ℓ, d)` satisfies `X_ℓ` with formula clock
`y = d`. -/
theorem genChar_sound {bound : Loc → ℕ} {succ : Loc → Loc} {ℓ : Loc} {p : Loc × ℝ≥0}
    {u : Valuation Unit} (h : TimedBisimilar (genTLTS bound succ) p (ℓ, u ())) :
    (p, u) ∈ genChar bound succ ℓ :=
  recMaxSys_coinduction (genTLTS bound succ) (genBody bound succ) (genRel_postfixed bound succ) ℓ h

/-! ### Completeness: satisfaction implies timed bisimilarity -/

/-- The satisfaction relation: relate `a` to the canonical `(ℓ, d)`-state when
`(a, [y = d]) ⊨ X_ℓ`. -/
def genSatRel (bound : Loc → ℕ) (succ : Loc → Loc) : (Loc × ℝ≥0) → (Loc × ℝ≥0) → Prop :=
  fun a b => (a, fun _ => b.2) ∈ genChar bound succ b.1

/-- The satisfaction relation is a timed bisimulation, read off `mem_genChar`. -/
theorem isBisimulation_genSatRel (bound : Loc → ℕ) (succ : Loc → Loc) :
    LTS.IsBisimulation (genTLTS bound succ) (genSatRel bound succ) := by
  rintro a ⟨ℓ, d⟩ hab
  simp only [genSatRel] at hab
  obtain ⟨C1, C2, C3⟩ := mem_genChar.mp hab
  constructor
  · rintro lbl a' hstep
    cases lbl with
    | inl u =>
      obtain ⟨⟩ := u
      obtain ⟨hd, hmem⟩ := C2 a' hstep
      refine ⟨(succ ℓ, 0), GenStep.act hd, ?_⟩
      simp only [genSatRel]; rwa [reset_unit] at hmem
    | inr t =>
      refine ⟨(ℓ, d + t), GenStep.delay ℓ d t, ?_⟩
      simp only [genSatRel]
      have hc := C3 t a' hstep; rwa [add_unit] at hc
  · rintro lbl b' hstep
    cases lbl with
    | inl u =>
      obtain ⟨⟩ := u
      replace hstep := gen_act.mp hstep
      cases hstep with
      | act hd =>
        rcases C1 with hgt | ⟨p', hp'a, hmem⟩
        · exact absurd hgt (not_lt.mpr hd)
        · refine ⟨p', hp'a, ?_⟩
          simp only [genSatRel]; rwa [reset_unit] at hmem
    | inr t =>
      replace hstep := gen_delay.mp hstep
      cases hstep with
      | delay =>
        obtain ⟨a', ha'd⟩ := gen_can_delay bound succ a t
        refine ⟨a', ha'd, ?_⟩
        simp only [genSatRel]
        have hc := C3 t a' ha'd; rwa [add_unit] at hc

/-- **Completeness.** A state satisfying `X_ℓ` with formula clock `y = d` is timed bisimilar
to `(ℓ, d)`. -/
theorem genChar_complete {bound : Loc → ℕ} {succ : Loc → Loc} {ℓ : Loc} {p : Loc × ℝ≥0}
    {u : Valuation Unit} (h : (p, u) ∈ genChar bound succ ℓ) :
    TimedBisimilar (genTLTS bound succ) p (ℓ, u ()) :=
  (isBisimulation_genSatRel bound succ).le_bisimilar
    (show genSatRel bound succ p (ℓ, u ()) by simp only [genSatRel]; rwa [valUnit])

/-- **The characteristic theorem (generic).** For a deterministic single-clock timed automaton
over any location graph, `(p, [y = d]) ⊨ X_ℓ` iff `p` is timed bisimilar to `(ℓ, d)`. -/
theorem genChar_iff {bound : Loc → ℕ} {succ : Loc → Loc} {ℓ : Loc} {p : Loc × ℝ≥0}
    {u : Valuation Unit} :
    (p, u) ∈ genChar bound succ ℓ ↔ TimedBisimilar (genTLTS bound succ) p (ℓ, u ()) :=
  ⟨genChar_complete, genChar_sound⟩

end TLTS

end DeepWiki.ReactiveSystems
