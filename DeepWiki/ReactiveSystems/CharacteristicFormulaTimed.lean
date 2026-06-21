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

/-- **Exercise 12.16** (§12.4, p.240). One application of the operator `O_F` (Definition 12.6) of
the characteristic formula's body (`charBody`, the RHS of equation (12.3)) to the *singleton*
`{((ℓ, [x=0]), [y=0])} = {(0, y↦0)}` is `∅`: the `∀∀X` conjunct demands that *every* delay
successor lie in the set, but no one-element set is closed under delay — delaying by `1` already
escapes it (`r + 1 ≠ 0`). -/
theorem denotMtR_charBody_initial :
    denotMtR runTLTS charBody {((0 : ℝ≥0), (fun _ => (0 : ℝ≥0)))} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨r, u⟩ hmem
  simp only [charBody, denotMtR, Set.mem_inter_iff, Set.mem_setOf_eq] at hmem
  have hcon := hmem.2 1 (r + 1) (RunStep.delay r 1)
  rw [Set.mem_singleton_iff, Prod.ext_iff] at hcon
  exact absurd hcon.1 (by positivity)

/-! ### Soundness: timed bisimilarity to the running example implies satisfaction -/

/-- **Soundness (Theorem 12.5 for the running example, ⇐).** If `(p, u)` is timed bisimilar to the running example's
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

/-- **Completeness (Theorem 12.5 for the running example, ⇒; Exercise 12.19).** If `(p, u)` satisfies the
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

/-- **Theorem 12.5 (for the running example).** A state `(p, u)` satisfies the characteristic
formula `X` iff it is timed bisimilar to the running example's clock-`u(y)` state. (Here the
tested state `p` is itself a `runTLTS` state — the `A = runTLTS` instance of the book's
statement, which compares `X_ℓ` against a state of an arbitrary automaton `A`.) -/
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

/-! #### Exercise 12.2: `Mt` properties of the two Example 11.4 automata

The `Mt`-with-clocks formulae below distinguish the two automata (`c = 1` on the left,
`c = 2` on the right) and exhibit a property both afford. The distinguishing property
`onceActLate` resets a formula clock `y` and asks for a *later* `a`-move once `y > 1`:
the `c = 2` automaton can still fire `a` after more than one time unit, the `c = 1` one
cannot. The shared property `onceActNow` is the immediate `⟨a⟩tt`. -/

/-- "After resetting `y`, time can pass beyond `y > 1` with `a` still enabled":
`y in ∃∃(y > 1 ∧ ⟨a⟩tt)`. The distinguishing property of Example 11.4. -/
def onceActLate : Mt Unit Unit :=
  .reset () (.existsDelay (.and (.guard (.atom () .gt 1)) (.dia () .tt)))

/-- "`a` is possible right now": `⟨a⟩tt`. A property both Example 11.4 automata afford. -/
def onceActNow : Mt Unit Unit := .dia () .tt

/-- The right automaton (`c = 2`) **has** the property `onceActLate`: delay to `y = 2`
(still `≤ 2`, so `a` is enabled). -/
theorem onceActLate_two : MtSatState (onceTLTS 2) (.A 0) onceActLate := by
  refine ⟨2, _, OnceStep.delayA 0 2, ?_, _, OnceStep.act ?_, trivial⟩
  · simp only [MtSat, satisfies, Cmp.holds, Valuation.add_apply, Valuation.reset,
      Set.mem_singleton_iff]
    norm_num
  · norm_num

/-- The left automaton (`c = 1`) **lacks** the property `onceActLate`: any delay reaching
`y > 1` puts the clock past the guard `x ≤ 1`, so `a` is disabled. -/
theorem not_onceActLate_one : ¬ MtSatState (onceTLTS 1) (.A 0) onceActLate := by
  intro h
  obtain ⟨d, p', hdelay, hguard, p'', hact, -⟩ := h
  cases hdelay with
  | delayA d t =>
    cases hact with
    | act hle =>
      simp only [MtSat, satisfies, Cmp.holds, Valuation.add_apply, Valuation.reset,
        Set.mem_singleton_iff] at hguard
      exact absurd hle (not_le.mpr hguard)

/-- Both Example 11.4 automata **afford** `onceActNow` (`⟨a⟩tt`): at `x = 0` the guard
`x ≤ c` holds for either bound. -/
theorem onceActNow_mtSat (c : ℕ) : MtSatState (onceTLTS c) (.A 0) onceActNow := by
  refine ⟨Once.B 0, OnceStep.act ?_, trivial⟩
  exact zero_le

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

/-! #### The live-location characterization `charA`

`charA c` is characteristic for `A`'s timed-bisimilarity classes. The key is that in this
automaton the *only* observable distinction between states is the **act-profile** — the set of
delays after which `a` is still enabled — because every action goes to the single dead class
and delays are free and deterministic. -/

/-- The unique delay successor of a state by `t`. -/
def adv : Once → ℝ≥0 → Once
  | .A e, t => .A (e + t)
  | .B e, t => .B (e + t)

@[simp] theorem adv_zero (q : Once) : adv q 0 = q := by cases q <;> simp [adv]

theorem adv_adv (q : Once) (t s : ℝ≥0) : adv (adv q t) s = adv q (t + s) := by
  cases q <;> simp [adv, add_assoc]

/-- Delays are deterministic: the successor is `adv q t`. -/
theorem onceStep_delay_eq {c : ℕ} {q r : Once} {t : ℝ≥0}
    (h : OnceStep c q (Sum.inr t) r) : r = adv q t := by
  cases h with
  | delayA e t => rfl
  | delayB e t => rfl

theorem onceStep_delay_adv {c : ℕ} (q : Once) (t : ℝ≥0) :
    OnceStep c q (Sum.inr t) (adv q t) := by
  cases q with
  | A e => exact OnceStep.delayA e t
  | B e => exact OnceStep.delayB e t

/-- Every action leads to the dead location `B 0`. -/
theorem onceStep_act_eq {c : ℕ} {q r : Once} (h : OnceStep c q (Sum.inl ()) r) :
    r = Once.B 0 := by cases h with | act _ => rfl

/-- A state can fire `a` now. -/
def canAct (c : ℕ) (q : Once) : Prop := ∃ q', OnceStep c q (Sum.inl ()) q'

theorem canAct_A {c : ℕ} {e : ℝ≥0} : canAct c (Once.A e) ↔ e ≤ (c : ℝ≥0) :=
  ⟨fun ⟨_, h⟩ => by cases h with | act hh => exact hh, fun h => ⟨_, OnceStep.act h⟩⟩

/-- **Timed bisimilarity in the Example 11.4 automaton is exactly act-profile equality**: two
states are timed bisimilar iff, after every delay, they agree on whether `a` is enabled. -/
theorem timedBisimilar_once_iff {c : ℕ} {q q' : Once} :
    TimedBisimilar (onceTLTS c) q q' ↔ ∀ t, (canAct c (adv q t) ↔ canAct c (adv q' t)) := by
  constructor
  · intro hbis t
    obtain ⟨_, _, hdf, _⟩ := (timedBisimilar_iff (onceTLTS c) q q').mp hbis
    obtain ⟨r, hr, hrb⟩ := hdf t (adv q t) (onceStep_delay_adv q t)
    rw [onceStep_delay_eq hr] at hrb
    obtain ⟨haf, hab, _, _⟩ := (timedBisimilar_iff (onceTLTS c) (adv q t) (adv q' t)).mp hrb
    exact ⟨fun ⟨w, hw⟩ => let ⟨w', hw', _⟩ := haf () w hw; ⟨w', hw'⟩,
           fun ⟨w, hw⟩ => let ⟨w', hw', _⟩ := hab () w hw; ⟨w', hw'⟩⟩
  · intro hprof
    have hbis : LTS.IsBisimulation (onceTLTS c)
        (fun a b => ∀ t, canAct c (adv a t) ↔ canAct c (adv b t)) := by
      rintro a b hab
      refine ⟨fun l a' hstep => ?_, fun l b' hstep => ?_⟩
      · cases l with
        | inl u =>
            obtain ⟨⟩ := u
            have hb : canAct c b := by
              have h0 : canAct c (adv b 0) := (hab 0).mp (by rw [adv_zero]; exact ⟨a', hstep⟩)
              rwa [adv_zero] at h0
            obtain ⟨b', hb'⟩ := hb
            refine ⟨b', hb', ?_⟩
            rw [onceStep_act_eq hstep, onceStep_act_eq hb']; exact fun _ => Iff.rfl
        | inr t =>
            rw [onceStep_delay_eq hstep]
            refine ⟨adv b t, onceStep_delay_adv b t, fun s => ?_⟩
            rw [adv_adv, adv_adv]; exact hab (t + s)
      · cases l with
        | inl u =>
            obtain ⟨⟩ := u
            have ha : canAct c a := by
              have h0 : canAct c (adv a 0) := (hab 0).mpr (by rw [adv_zero]; exact ⟨b', hstep⟩)
              rwa [adv_zero] at h0
            obtain ⟨a', ha'⟩ := ha
            refine ⟨a', ha', ?_⟩
            rw [onceStep_act_eq hstep, onceStep_act_eq ha']; exact fun _ => Iff.rfl
        | inr t =>
            rw [onceStep_delay_eq hstep]
            refine ⟨adv a t, onceStep_delay_adv a t, fun s => ?_⟩
            rw [adv_adv, adv_adv]; exact hab (t + s)
    exact hbis.le_bisimilar hprof

/-- `charA c` (at formula clock `y = d`) is satisfied exactly when the state's act-profile is
that of `A d`: after every delay `t`, `a` is enabled iff `d + t ≤ c`. -/
theorem mtSat_charA {c : ℕ} {q : Once} {d : ℝ≥0} :
    (onceTLTS c).MtSat q (fun _ => d) (charA c) ↔
      ∀ t, (canAct c (adv q t) ↔ d + t ≤ (c : ℝ≥0)) := by
  constructor
  · intro h t
    obtain ⟨hC1, hC2⟩ := h t (adv q t) (onceStep_delay_adv q t)
    refine ⟨fun ⟨w, hw⟩ => ?_, fun hle => ?_⟩
    · exact (hC2 w hw).1
    · rcases hC1 with hgt | ⟨w, hw, _⟩
      · exact absurd hle (not_le.mpr (show (c : ℝ≥0) < d + t from hgt))
      · exact ⟨w, hw⟩
  · intro h t q' hdel
    rw [onceStep_delay_eq hdel]
    refine ⟨?_, fun w hw => ⟨?_, by rw [onceStep_act_eq hw]; exact mtSat_charB.mpr trivial⟩⟩
    · by_cases hle : d + t ≤ (c : ℝ≥0)
      · obtain ⟨w, hw⟩ := (h t).mpr hle
        exact Or.inr ⟨w, hw, by rw [onceStep_act_eq hw]; exact mtSat_charB.mpr trivial⟩
      · exact Or.inl (show (c : ℝ≥0) < d + t from not_le.mp hle)
    · exact (h t).mp ⟨w, hw⟩

/-- **`charA` is characteristic for the live location** (the book's Theorem-12.5 analogue for
Example 11.4, no recursion): `(q, [y = d])` satisfies `charA c` iff `q` is timed bisimilar to
`A d`. -/
theorem mtSat_charA_iff {c : ℕ} {q : Once} {d : ℝ≥0} :
    (onceTLTS c).MtSat q (fun _ => d) (charA c) ↔ TimedBisimilar (onceTLTS c) q (Once.A d) := by
  rw [mtSat_charA, timedBisimilar_once_iff]
  refine forall_congr' (fun t => ?_)
  rw [show adv (Once.A d) t = Once.A (d + t) from rfl, canAct_A]

/-- `charA c` is a characteristic `Mt` formula for the live initial state `A 0` of the
Example 11.4 automaton — the special case `d = 0` of `mtSat_charA_iff`. This discharges the
`IsCharacteristicMt` hypothesis of the timed Hennessy–Milner reduction for a concrete
timed system (no region construction needed, since the action graph is acyclic). -/
theorem isCharacteristicMt_charA {c : ℕ} :
    IsCharacteristicMt (onceTLTS c) (Once.A 0) (charA c) := by
  intro q
  simp only [MtSatState]
  rw [mtSat_charA_iff]
  exact ⟨fun h => (timedBisimilar_equivalence (onceTLTS c)).symm h,
         fun h => (timedBisimilar_equivalence (onceTLTS c)).symm h⟩

/-- **Timed Hennessy–Milner, unconditionally, for the live state `A 0`** (an instance of
`timedBisimilar_iff_mtEquiv_of_characteristic` discharged by `isCharacteristicMt_charA`):
a state `q` of the Example 11.4 automaton is timed bisimilar to `A 0` iff it satisfies the
same state-level `Mt` formulae. -/
theorem timedBisimilar_A0_iff_mtEquiv {c : ℕ} (q : Once) :
    TimedBisimilar (onceTLTS c) (Once.A 0) q ↔
      ∀ F : Mt Unit Unit, (onceTLTS c).MtSatState (Once.A 0) F ↔ (onceTLTS c).MtSatState q F :=
  timedBisimilar_iff_mtEquiv_of_characteristic (onceTLTS c) (charA c) isCharacteristicMt_charA q

end TLTS

end DeepWiki.ReactiveSystems
