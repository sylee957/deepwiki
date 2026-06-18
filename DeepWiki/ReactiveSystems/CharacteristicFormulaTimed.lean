import DeepWiki.ReactiveSystems.TimedHmlRecursion

/-! # A characteristic formula for a timed automaton, modulo timed bisimilarity (§12.4.1)
The recursion-extended timed logic `MtR` is expressive enough to characterise a timed
automaton's timed-bisimilarity classes by a single (recursively defined) formula, just as
`HML` with recursion does for finite LTSs. We formalise the book's running example: the
one-location automaton whose single action `a` is enabled while the clock is `≤ 1` and
resets it, with arbitrary delays allowed. Its characteristic formula is
`X =max (y ≤ 1 ⇒ ⟨a⟩(y in X)) ∧ [a](y ≤ 1 ∧ (y in X)) ∧ ∀∀X`, and an extended state
satisfies `X` (with the formula clock `y` reading `d`) exactly when it is timed bisimilar to
the running example's clock-`d` state. This is a concrete instance of the
characteristic-property theorem for timed automata (the general result is due to
Laroussinie, Larsen and Weise (1995), sketched as Theorem 12.4/12.5 in the book). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-! ### The running-example timed automaton -/

/-- SOS of the running-example timed automaton (one location, one clock `x`): the single
action `a` fires while `x ≤ 1`, resetting the clock to `0`; time may elapse freely. The state
is just the clock value `d : ℝ≥0`. -/
inductive RunStep : ℝ≥0 → (Unit ⊕ ℝ≥0) → ℝ≥0 → Prop
  /-- `d —a→ 0` while `d ≤ 1` (the self-loop, resetting the clock). -/
  | act {d : ℝ≥0} (h : d ≤ 1) : RunStep d (Sum.inl ()) 0
  /-- `d` delays freely: `d ⤳t d + t`. -/
  | delay (d t : ℝ≥0) : RunStep d (Sum.inr t) (d + t)

/-- The running-example TLTS (states = clock values). -/
def runTLTS : TLTS ℝ≥0 Unit := ⟨RunStep⟩

@[simp] theorem run_act {d p : ℝ≥0} : runTLTS.act d () p ↔ RunStep d (Sum.inl ()) p := Iff.rfl

@[simp] theorem run_delay {d t p : ℝ≥0} : runTLTS.delay d t p ↔ RunStep d (Sum.inr t) p := Iff.rfl

/-! ### The characteristic formula -/

/-- The body of the recursive characteristic formula `X` for the running example, over the
single formula clock `y` (`= ()`): `(y ≤ 1 ⇒ ⟨a⟩(y in X)) ∧ [a](y ≤ 1 ∧ (y in X)) ∧ ∀∀X`,
with the implication `y ≤ 1 ⇒ F` written as `y > 1 ∨ F`. -/
def charBody : MtR Unit Unit :=
  .and
    (.and
      (.or (.guard (.atom () .gt 1)) (.dia () (.reset () .var)))
      (.box () (.and (.guard (.atom () .le 1)) (.reset () .var))))
    (.forallDelay .var)

/-- The characteristic formula `X` of the running example's location, as a set of extended
states — the greatest fixed point of `charBody`. -/
def charFormula : Set (ℝ≥0 × Valuation Unit) := recMax runTLTS charBody

/-- **Fixed-point unfolding of the characteristic formula.** An extended state `(p, u)`
satisfies `X` iff: (1) `u(y) > 1` or `p` can fire `a` into a state that satisfies `X` after
resetting `y`; (2) every `a`-move has `u(y) ≤ 1` and lands in a state satisfying `X` after
resetting `y`; and (3) every delay successor still satisfies `X`. -/
theorem mem_charFormula {q : ℝ≥0 × Valuation Unit} :
    q ∈ charFormula ↔
      ((1 : ℝ≥0) < q.2 () ∨
          ∃ p', runTLTS.act q.1 () p' ∧ (p', Valuation.reset {()} q.2) ∈ charFormula) ∧
        (∀ p', runTLTS.act q.1 () p' →
          q.2 () ≤ 1 ∧ (p', Valuation.reset {()} q.2) ∈ charFormula) ∧
        (∀ t p', runTLTS.delay q.1 t p' → (p', q.2.add t) ∈ charFormula) := by
  have h : charFormula = denotMtR runTLTS charBody charFormula :=
    (denotMtR_recMax runTLTS charBody).symm
  conv_lhs => rw [h]
  simp only [charBody, denotMtR, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    Cmp.holds, Nat.cast_one, and_assoc]

/-! ### Soundness: timed bisimilarity to the running example implies satisfaction -/

/-- **Soundness (Theorem 12.5, ⇐).** If `(p, u)` is timed bisimilar to the running example's
clock-`u(y)` state, then it satisfies the characteristic formula `X`. Proved by coinduction:
the timed-bisimilarity-to-the-example relation is a post-fixed point of `charBody`. -/
theorem charFormula_sound {q : ℝ≥0 × Valuation Unit}
    (hb : TimedBisimilar runTLTS q.1 (q.2 ())) : q ∈ charFormula := by
  have key : {r : ℝ≥0 × Valuation Unit | TimedBisimilar runTLTS r.1 (r.2 ())} ⊆
      denotMtR runTLTS charBody {r | TimedBisimilar runTLTS r.1 (r.2 ())} := by
    rintro ⟨d, w⟩ hb'
    simp only [Set.mem_setOf_eq] at hb'
    obtain ⟨haf, hab, hdf, _hdb⟩ := (timedBisimilar_iff runTLTS d (w ())).1 hb'
    have hreset : (Valuation.reset {()} w) () = 0 := Valuation.reset_mem rfl w
    simp only [charBody, denotMtR, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
      Cmp.holds, Nat.cast_one]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- conjunct 1: y > 1, or `a` is enabled into the relation
      by_cases h1 : w () ≤ 1
      · right
        obtain ⟨p', hp', hp'b⟩ := hab () 0 (RunStep.act h1)
        exact ⟨p', hp', by rw [hreset]; exact hp'b⟩
      · exact Or.inl (not_le.mp h1)
    · -- conjunct 2: every `a`-move is within bound and stays in the relation
      intro p' hp'
      cases hp' with
      | act hd1 =>
          obtain ⟨q', hq', _⟩ := haf () 0 (RunStep.act hd1)
          cases hq' with
          | act hw1 => exact ⟨hw1, by rw [hreset]⟩
    · -- conjunct 3: every delay stays in the relation
      intro t p' hp'
      cases hp' with
      | delay =>
          obtain ⟨q', hq', hq'b⟩ := hdf t (d + t) (RunStep.delay d t)
          cases hq' with
          | delay => rw [Valuation.add_apply]; exact hq'b
  exact (denotMtRHom runTLTS charBody).le_gfp key hb

/-! ### Completeness: satisfaction implies timed bisimilarity (Exercise 12.19) -/

/-- **Completeness (Theorem 12.5, ⇒; Exercise 12.19).** If `(p, u)` satisfies the
characteristic formula `X`, then `p` is timed bisimilar to the running example's clock-`u(y)`
state. Proved by exhibiting the satisfaction relation `R a b := (a, [y = b]) ⊨ X` as a timed
bisimulation (read off from `mem_charFormula`). -/
theorem charFormula_complete {q : ℝ≥0 × Valuation Unit} (hq : q ∈ charFormula) :
    TimedBisimilar runTLTS q.1 (q.2 ()) := by
  have hr0 : ∀ c : ℝ≥0, Valuation.reset {()} (fun _ : Unit => c) = (fun _ => (0 : ℝ≥0)) := by
    intro c; funext u; cases u; exact Valuation.reset_mem rfl (fun _ : Unit => c)
  have hadd : ∀ c t : ℝ≥0, Valuation.add (fun _ : Unit => c) t = (fun _ => c + t) := by
    intro c t; funext u; rw [Valuation.add_apply]
  have hR : LTS.IsBisimulation runTLTS
      (fun a b : ℝ≥0 => (a, fun _ : Unit => b) ∈ charFormula) := by
    rintro a b hab
    obtain ⟨hC1, hC2, hC3⟩ := mem_charFormula.1 hab
    dsimp only at hC1 hC2 hC3
    refine ⟨fun l a' hstep => ?_, fun l b' hstep => ?_⟩
    · -- forth
      cases l with
      | inl u =>
          obtain rfl : u = () := rfl
          cases hstep with
          | act ha1 =>
              obtain ⟨hb1, hmem⟩ := hC2 0 (RunStep.act ha1)
              refine ⟨0, RunStep.act hb1, ?_⟩
              rwa [hr0] at hmem
      | inr t =>
          cases hstep with
          | delay =>
              refine ⟨b + t, RunStep.delay b t, ?_⟩
              have hm := hC3 t (a + t) (RunStep.delay a t)
              rwa [hadd] at hm
    · -- back
      cases l with
      | inl u =>
          obtain rfl : u = () := rfl
          cases hstep with
          | act hb1 =>
              rcases hC1 with h1 | ⟨p', hp', hmem⟩
              · exact absurd h1 (not_lt.mpr hb1)
              · cases hp' with
                | act ha1 =>
                    refine ⟨0, RunStep.act ha1, ?_⟩
                    rwa [hr0] at hmem
      | inr t =>
          cases hstep with
          | delay =>
              refine ⟨a + t, RunStep.delay a t, ?_⟩
              have hm := hC3 t (a + t) (RunStep.delay a t)
              rwa [hadd] at hm
  have hq2 : q.2 = fun _ : Unit => q.2 () := by funext u; cases u; rfl
  exact hR.le_bisimilar (by rw [← hq2]; exact hq)

/-- **Theorem 12.5 / Corollary 12.2 (for the running example).** A state `(p, u)` satisfies the
characteristic formula `X` iff it is timed bisimilar to the running example's clock-`u(y)`
state. -/
theorem mem_charFormula_iff_timedBisimilar {q : ℝ≥0 × Valuation Unit} :
    q ∈ charFormula ↔ TimedBisimilar runTLTS q.1 (q.2 ()) :=
  ⟨charFormula_complete, charFormula_sound⟩

/-! ### Exercise 12.20: characteristic formulae without recursion (Example 11.4)

When the action graph is *acyclic*, the characteristic formula needs no recursion — a plain
`Mt` formula suffices. The Example 11.4 automaton (one action `a`, guarded `x ≤ c`, resetting
`x`, into a dead location; free delays) is such a case. Two instances `c = 1` and `c = 2` are
the book's two automata, which are not timed bisimilar. -/

/-- States of the Example 11.4 automaton (bound `c`): the live location `A d` (can fire `a`
while clock `d ≤ c`, reaching the dead location and resetting the clock) and the dead location
`B d`. Both delay freely. -/
inductive Once
  | A (d : ℝ≥0)
  | B (d : ℝ≥0)

/-- SOS of the Example 11.4 automaton with action guard `x ≤ c`. -/
inductive OnceStep (c : ℕ) : Once → (Unit ⊕ ℝ≥0) → Once → Prop
  /-- `A d —a→ B 0` while `d ≤ c` (resetting the clock). -/
  | act {d : ℝ≥0} (h : d ≤ (c : ℝ≥0)) : OnceStep c (.A d) (.inl ()) (.B 0)
  /-- `A` delays freely. -/
  | delayA (d t : ℝ≥0) : OnceStep c (.A d) (.inr t) (.A (d + t))
  /-- `B` delays freely. -/
  | delayB (d t : ℝ≥0) : OnceStep c (.B d) (.inr t) (.B (d + t))

/-- The Example 11.4 TLTS with bound `c`. -/
def onceTLTS (c : ℕ) : TLTS Once Unit := ⟨OnceStep c⟩

@[simp] theorem once_act {c : ℕ} {q q' : Once} :
    (onceTLTS c).act q () q' ↔ OnceStep c q (Sum.inl ()) q' := Iff.rfl

@[simp] theorem once_delay {c : ℕ} {q q' : Once} {t : ℝ≥0} :
    (onceTLTS c).delay q t q' ↔ OnceStep c q (Sum.inr t) q' := Iff.rfl

/-- A state can always delay (by any duration). -/
theorem once_can_delay {c : ℕ} (q : Once) (t : ℝ≥0) :
    ∃ q', OnceStep c q (Sum.inr t) q' := by
  cases q with
  | A d => exact ⟨_, OnceStep.delayA d t⟩
  | B d => exact ⟨_, OnceStep.delayB d t⟩

/-- A state is *dead* — it can never fire `a`, now or after any delay: `B _`, or `A d` with
`c < d` (so `d` can only grow past the guard). -/
def OnceDead (c : ℕ) : Once → Prop
  | .A d => (c : ℝ≥0) < d
  | .B _ => True

/-- Dead states have no `a`-move. -/
theorem OnceDead.no_act {c : ℕ} {q q' : Once} (hq : OnceDead c q) :
    ¬ OnceStep c q (Sum.inl ()) q' := by
  intro h
  cases q with
  | A d => cases h with | act hd => exact absurd hd (not_le.mpr hq)
  | B d => cases h

/-- Death is preserved by delay. -/
theorem OnceDead.delay {c : ℕ} {q q' : Once} {t : ℝ≥0} (hq : OnceDead c q)
    (h : OnceStep c q (Sum.inr t) q') : OnceDead c q' := by
  cases h with
  | delayA d t => exact lt_of_lt_of_le hq le_self_add
  | delayB d t => trivial

/-- The characteristic formula of the dead location: `∀∀[a]ff` — no action is ever possible. -/
def charB : Mt Unit Unit := .forallDelay (.box () .ff)

/-- The characteristic formula of the live location `A` (bound `c`), recursion-free:
`∀∀((y ≤ c ⇒ ⟨a⟩(y in charB)) ∧ [a](y ≤ c ∧ (y in charB)))` (the implication `y ≤ c ⇒ F`
written `y > c ∨ F`). No recursion is needed because the action leads to the dead location,
whose formula `charB` is itself recursion-free. -/
def charA (c : ℕ) : Mt Unit Unit :=
  .forallDelay
    (.and
      (.or (.guard (.atom () .gt c)) (.dia () (.reset () charB)))
      (.box () (.and (.guard (.atom () .le c)) (.reset () charB))))

/-- `charB` is satisfied exactly at the dead states (independently of the formula clock). -/
theorem mtSat_charB {c : ℕ} {q : Once} {u : Valuation Unit} :
    (onceTLTS c).MtSat q u charB ↔ OnceDead c q := by
  constructor
  · intro h
    cases q with
    | A d =>
        by_contra hc
        simp only [OnceDead, not_lt] at hc
        have hdel : OnceStep c (Once.A d) (Sum.inr 0) (Once.A d) := by
          have := OnceStep.delayA (c := c) d 0; rwa [add_zero] at this
        exact h 0 (Once.A d) hdel (Once.B 0) (OnceStep.act hc)
    | B d => trivial
  · intro hq t q' hdel q'' hact
    exact (hq.delay hdel).no_act hact

/-- All dead states are timed bisimilar to the dead location `B 0`. -/
theorem onceDead_timedBisimilar {c : ℕ} {q : Once} (hq : OnceDead c q) :
    TimedBisimilar (onceTLTS c) q (Once.B 0) := by
  have hbis : LTS.IsBisimulation (onceTLTS c) (fun x y => OnceDead c x ∧ OnceDead c y) := by
    rintro x y ⟨hx, hy⟩
    refine ⟨fun l x' hstep => ?_, fun l y' hstep => ?_⟩
    · cases l with
      | inl u => obtain ⟨⟩ := u; exact absurd hstep hx.no_act
      | inr t =>
          obtain ⟨y', hy'⟩ := once_can_delay (c := c) y t
          exact ⟨y', hy', hx.delay hstep, hy.delay hy'⟩
    · cases l with
      | inl u => obtain ⟨⟩ := u; exact absurd hstep hy.no_act
      | inr t =>
          obtain ⟨x', hx'⟩ := once_can_delay (c := c) x t
          exact ⟨x', hx', hx.delay hx', hy.delay hstep⟩
  exact hbis.le_bisimilar ⟨hq, trivial⟩

/-- **`charB` is characteristic for the dead location**: a state satisfies `charB` iff it is
timed bisimilar to `B 0`. -/
theorem mtSat_charB_iff {c : ℕ} {q : Once} {u : Valuation Unit} :
    (onceTLTS c).MtSat q u charB ↔ TimedBisimilar (onceTLTS c) q (Once.B 0) := by
  rw [mtSat_charB]
  refine ⟨onceDead_timedBisimilar, fun hbis => ?_⟩
  cases q with
  | A d =>
      by_contra hc
      simp only [OnceDead, not_lt] at hc
      obtain ⟨haf, _, _, _⟩ := (timedBisimilar_iff (onceTLTS c) (Once.A d) (Once.B 0)).mp hbis
      obtain ⟨q', hq', _⟩ := haf () (Once.B 0) (OnceStep.act hc)
      exact (OnceDead.no_act (q := Once.B 0) trivial) hq'
  | B d => trivial

end TLTS

end DeepWiki.ReactiveSystems
