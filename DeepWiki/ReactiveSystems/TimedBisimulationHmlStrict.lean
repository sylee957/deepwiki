import DeepWiki.ReactiveSystems.TimedTransitionSystems
import DeepWiki.ReactiveSystems.TimedHml

/-! # Timed bisimilarity is strictly finer than timed-HML equivalence
The converse direction *fails* over arbitrary TLTSs: there are states that
satisfy the same timed-HML (`Mt`) formulae yet are not timed bisimilar. The book's
witness is the `√2` TLTS: states `(A,d)`, `(B,d)` (`d : ℝ≥0`) and
`End`, where `(A,d) —a→ End` for `d < c`, `(B,d) —a→ End` for `d ≤ c`, and every
state delays freely; the book takes the boundary `c = √2`. Since `Mt`'s clock
constraints only compare against integers, `Mt` cannot express "after delaying
exactly `√2` an `a` is enabled", so `(A,0)` and `(B,0)` are `Mt`-equivalent. They
are nonetheless *not* timed bisimilar:
`(B,0) —c→ (B,c) —a→ End`, while after the same `c`-delay `(A,0)` only reaches
`(A,c)`, from which no `a` is possible. We formalise this separating fact —
`¬ (A,0) ~ (B,0)` — for an arbitrary boundary `c` (the argument needs nothing of
`√2` but its being a real). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The single observable action of the `√2` example. -/
inductive Sq2Act | a
  deriving DecidableEq

/-- States of the `√2` TLTS: `A d`, `B d` (parameterised by elapsed time `d`) and
the sink `End`. -/
inductive Sq2 | A (d : ℝ≥0) | B (d : ℝ≥0) | End

variable (c : ℝ≥0)

/-- The SOS of the `√2` TLTS with boundary `c`: `A d` does `a`
strictly below `c`, `B d` does `a` up to and including `c`, and every state delays
freely. -/
inductive Sq2Step (c : ℝ≥0) : Sq2 → (Sq2Act ⊕ ℝ≥0) → Sq2 → Prop
  /-- `A d —a→ End` for `d < c`. -/
  | aA {d : ℝ≥0} (h : d < c) : Sq2Step c (.A d) (.inl .a) .End
  /-- `B d —a→ End` for `d ≤ c` (note the boundary `d = c` is included). -/
  | aB {d : ℝ≥0} (h : d ≤ c) : Sq2Step c (.B d) (.inl .a) .End
  /-- `A d` delays freely. -/
  | delA {d d' : ℝ≥0} : Sq2Step c (.A d) (.inr d') (.A (d + d'))
  /-- `B d` delays freely. -/
  | delB {d d' : ℝ≥0} : Sq2Step c (.B d) (.inr d') (.B (d + d'))
  /-- `End` delays to itself. -/
  | delEnd {d' : ℝ≥0} : Sq2Step c .End (.inr d') .End

/-- The `√2` timed LTS with boundary `c`. -/
def sq2TLTS (c : ℝ≥0) : TLTS Sq2 Sq2Act := ⟨Sq2Step c⟩

/-- An `α`-action in `sq2TLTS c` unfolds to `Sq2Step c p (Sum.inl α) q`. -/
@[simp] theorem sq2_act {c : ℝ≥0} {p q : Sq2} {α : Sq2Act} :
    (sq2TLTS c).act p α q ↔ Sq2Step c p (Sum.inl α) q := Iff.rfl

/-- A `d`-delay in `sq2TLTS c` unfolds to `Sq2Step c p (Sum.inr d) q`. -/
@[simp] theorem sq2_delay {c : ℝ≥0} {p q : Sq2} {d : ℝ≥0} :
    (sq2TLTS c).delay p d q ↔ Sq2Step c p (Sum.inr d) q := Iff.rfl

/-- `(A,0)` and `(B,0)` are **not** timed bisimilar — the
witnessing fact that the converse (timed-HML equivalence implies timed bisimilarity)
fails over arbitrary TLTSs. (With the boundary `c = √2` they nonetheless satisfy
the same `Mt` formulae.) -/
theorem not_timedBisimilar_sqrt2 :
    ¬ TLTS.TimedBisimilar (sq2TLTS c) (Sq2.A 0) (Sq2.B 0) := by
  intro h
  -- Match `(B,0) —c→ (B,c)` with a `c`-delay from `(A,0)`; it can only reach `(A,c)`.
  obtain ⟨-, -, -, hdel⟩ := (TLTS.timedBisimilar_iff (sq2TLTS c) (Sq2.A 0) (Sq2.B 0)).1 h
  have hBdelay : (sq2TLTS c).delay (Sq2.B 0) c (Sq2.B c) := by
    have hb := @Sq2Step.delB c 0 c
    rw [zero_add] at hb
    exact hb
  obtain ⟨p', hp', hbis⟩ := hdel c (Sq2.B c) hBdelay
  rw [sq2_delay] at hp'
  cases hp'
  rw [zero_add] at hbis
  -- `(B,c) —a→ End`, but `(A,c)` has no `a`-move (it would need `c < c`).
  obtain ⟨-, hact, -, -⟩ := (TLTS.timedBisimilar_iff (sq2TLTS c) (Sq2.A c) (Sq2.B c)).1 hbis
  obtain ⟨q', hq', -⟩ := hact Sq2Act.a Sq2.End (sq2_act.mpr (Sq2Step.aB le_rfl))
  rw [sq2_act] at hq'
  cases hq' with
  | aA h => exact absurd h (lt_irrefl _)

/-! ### Past the boundary `A` and `B` agree -/

/-- A state that can no longer perform `a`: `A d` with `c ≤ d`, `B e` with `c < e`,
or `End`. Such states can only delay (into other `a`-disabled states). -/
def aDisabled (c : ℝ≥0) : Sq2 → Prop
  | .A d => c ≤ d
  | .B e => c < e
  | .End => True

/-- An `a`-disabled state has no `a`-move. -/
theorem aDisabled.no_act {c : ℝ≥0} {x x' : Sq2} {α : Sq2Act} (hx : aDisabled c x)
    (h : Sq2Step c x (Sum.inl α) x') : False := by
  cases h with
  | aA hlt => exact absurd hlt (not_lt.mpr hx)
  | aB hle => exact absurd hle (not_le.mpr hx)

/-- Every state has, for each delay, a unique-shape delay successor; `a`-disabled
states stay `a`-disabled under delay. -/
theorem aDisabled.delay_succ {c : ℝ≥0} {x : Sq2} (hx : aDisabled c x) (d' : ℝ≥0) :
    ∃ x', Sq2Step c x (Sum.inr d') x' ∧ aDisabled c x' := by
  cases x with
  | A d => exact ⟨.A (d + d'), Sq2Step.delA, le_trans hx (le_self_add)⟩
  | B e => exact ⟨.B (e + d'), Sq2Step.delB, lt_of_lt_of_le hx le_self_add⟩
  | End => exact ⟨.End, Sq2Step.delEnd, trivial⟩

/-- A delay step out of an `a`-disabled state lands in an `a`-disabled state. -/
theorem aDisabled.delay_pres {c : ℝ≥0} {x x' : Sq2} {d' : ℝ≥0} (hx : aDisabled c x)
    (h : Sq2Step c x (Sum.inr d') x') : aDisabled c x' := by
  cases h with
  | delA => exact le_trans hx le_self_add
  | delB => exact lt_of_lt_of_le hx le_self_add
  | delEnd => trivial

/-- Relating any two `a`-disabled states. -/
def pastRel (c : ℝ≥0) (x y : Sq2) : Prop := aDisabled c x ∧ aDisabled c y

/-- The `a`-disabled states form a timed bisimulation:
past the boundary every state behaves identically (only delays, never `a`). -/
theorem isBisimulation_pastRel : LTS.IsBisimulation (sq2TLTS c) (pastRel c) := by
  rintro x y ⟨hx, hy⟩
  refine ⟨fun l x' hstep => ?_, fun l y' hstep => ?_⟩
  · cases l with
    | inl _a => exact absurd hstep (fun h => hx.no_act h)
    | inr d' =>
      obtain ⟨y', hy', hy'd⟩ := hy.delay_succ d'
      exact ⟨y', hy', hx.delay_pres hstep, hy'd⟩
  · cases l with
    | inl _a => exact absurd hstep (fun h => hy.no_act h)
    | inr d' =>
      obtain ⟨x', hx', hx'd⟩ := hx.delay_succ d'
      exact ⟨x', hx', hx'd, hy.delay_pres hstep⟩

/-- Past the boundary the two states
agree: `(A,d)` with `c ≤ d` and `(B,e)` with `c < e` are timed bisimilar (both can
only delay). In particular `(A,c) ~ (B,e)` for `e > c` — so `(A,0)` and `(B,0)`
differ *only* at the boundary crossing (cf. `not_timedBisimilar_sqrt2`). -/
theorem timedBisimilar_past_boundary {d e : ℝ≥0} (hd : c ≤ d) (he : c < e) :
    TLTS.TimedBisimilar (sq2TLTS c) (Sq2.A d) (Sq2.B e) :=
  (isBisimulation_pastRel c).le_bisimilar ⟨hd, he⟩

/-- The separating behaviour at the boundary: after the same `c`-delay, `(B,c)`
can still do `a` (`c ≤ c`) but `(A,c)` cannot (it would need `c < c`). -/
example :
    (sq2TLTS c).delay (Sq2.A 0) c (Sq2.A c) ∧
    (sq2TLTS c).delay (Sq2.B 0) c (Sq2.B c) ∧
    (sq2TLTS c).act (Sq2.B c) Sq2Act.a Sq2.End ∧
    ¬ ∃ q, (sq2TLTS c).act (Sq2.A c) Sq2Act.a q := by
  refine ⟨?_, ?_, sq2_act.mpr (Sq2Step.aB le_rfl), ?_⟩
  · have := @Sq2Step.delA c 0 c; rwa [zero_add] at this
  · have := @Sq2Step.delB c 0 c; rwa [zero_add] at this
  · rintro ⟨q, hq⟩; rw [sq2_act] at hq; cases hq with | aA h => exact absurd h (lt_irrefl _)

/-! ### `(A,0)` and `(B,0)` are basic-timed-HML equivalent (Prop 12.2 strictness)

Basic timed HML's delay quantifiers `∃∃`/`∀∀` only quantify over the *existence* /
*universality* of a delay, never its duration — exactly the duration-forgetting
matching of untimed bisimilarity. So it suffices to show `(A,0)` and `(B,0)` are
untimed bisimilar (no irrationality of `c` needed, only `0 < c`); they are *not*
timed bisimilar, so timed bisimilarity is strictly finer than basic-timed-HML
equivalence. (The book's full-`Mt`-logic version needs `c = √2` irrational.) -/

/-- Every state can delay past the boundary into an `a`-disabled state. -/
theorem exists_aDisabled_delay (y : Sq2) :
    ∃ d' y', Sq2Step c y (Sum.inr d') y' ∧ aDisabled c y' := by
  cases y with
  | A d => exact ⟨c, Sq2.A (d + c), Sq2Step.delA, le_add_self⟩
  | B e =>
      refine ⟨c + 1, Sq2.B (e + (c + 1)), Sq2Step.delB, ?_⟩
      have h : c < e + c + 1 := lt_of_le_of_lt le_add_self (lt_add_of_pos_right _ one_pos)
      rwa [add_assoc] at h
  | End => exact ⟨0, Sq2.End, Sq2Step.delEnd, trivial⟩

/-- Every state can delay (by `0`) staying in the same `a`-enabledness class. -/
theorem exists_sameClass_delay (y : Sq2) :
    ∃ d' y', Sq2Step c y (Sum.inr d') y' ∧ (aDisabled c y' ↔ aDisabled c y) := by
  cases y with
  | A e => exact ⟨0, Sq2.A (e + 0), Sq2Step.delA, by simp only [aDisabled, add_zero]⟩
  | B e => exact ⟨0, Sq2.B (e + 0), Sq2Step.delB, by simp only [aDisabled, add_zero]⟩
  | End => exact ⟨0, Sq2.End, Sq2Step.delEnd, Iff.rfl⟩

/-- The `a`-enabledness classes form an *untimed* bisimulation: `a`-moves go to the
dead sink `End`, and any delay can be matched by a same-class delay (duration is
forgotten). -/
theorem isBisimulation_sq2_aClass :
    LTS.IsBisimulation (sq2TLTS c).untimedLTS (fun x y => aDisabled c x ↔ aDisabled c y) := by
  have key : ∀ {x y : Sq2}, (aDisabled c x ↔ aDisabled c y) → ∀ {l : Option Sq2Act} {x' : Sq2},
      (sq2TLTS c).untimedLTS.step x l x' →
      ∃ y', (sq2TLTS c).untimedLTS.step y l y' ∧ (aDisabled c x' ↔ aDisabled c y') := by
    intro x y hxy l x' hstep
    cases l with
    | some act =>
        change Sq2Step c x (Sum.inl act) x' at hstep
        have hxlive : ¬ aDisabled c x := by
          cases hstep with
          | aA hd => exact not_le.mpr hd
          | aB he => exact not_lt.mpr he
        have hylive : ¬ aDisabled c y := fun hy => hxlive (hxy.mpr hy)
        obtain rfl : x' = Sq2.End := by cases hstep <;> rfl
        refine ⟨Sq2.End, ?_, Iff.rfl⟩
        show Sq2Step c y (Sum.inl act) Sq2.End
        cases y with
        | A e => exact Sq2Step.aA (not_le.mp hylive)
        | B e => exact Sq2Step.aB (not_lt.mp hylive)
        | End => exact absurd trivial hylive
    | none =>
        change ∃ d, Sq2Step c x (Sum.inr d) x' at hstep
        obtain ⟨d, hd⟩ := hstep
        by_cases hx' : aDisabled c x'
        · obtain ⟨d', y', hy', hyd'⟩ := exists_aDisabled_delay c y
          exact ⟨y', ⟨d', hy'⟩, iff_of_true hx' hyd'⟩
        · have hxlive : ¬ aDisabled c x := fun hx => hx' (aDisabled.delay_pres hx hd)
          have hylive : ¬ aDisabled c y := fun hy => hxlive (hxy.mpr hy)
          obtain ⟨d', y', hy', hyiff⟩ := exists_sameClass_delay c y
          exact ⟨y', ⟨d', hy'⟩, iff_of_false hx' (fun h => hylive (hyiff.mp h))⟩
  intro x y hxy
  exact ⟨fun _l _x' h => key hxy h, fun _l _y' h => by
    obtain ⟨x', hx', hiff⟩ := key hxy.symm h
    exact ⟨x', hx', hiff.symm⟩⟩

/-- `(A,0)` and `(B,0)` are untimed bisimilar (for any positive boundary `c`). -/
theorem untimedBisimilar_sq2 (hc : 0 < c) :
    (sq2TLTS c).UntimedBisimilar (Sq2.A 0) (Sq2.B 0) :=
  (isBisimulation_sq2_aClass c).le_bisimilar
    (iff_of_false (not_le.mpr hc) (not_lt.mpr zero_le))

/-- `(A,0)` and `(B,0)` satisfy the same basic timed-HML formulae. -/
theorem timedHmlEquiv_sq2 (hc : 0 < c) :
    (sq2TLTS c).TimedHMLEquiv (Sq2.A 0) (Sq2.B 0) :=
  TLTS.untimedBisimilar_timedHmlEquiv (untimedBisimilar_sq2 c hc)

/-- **Prop 12.2 (basic-logic form): timed bisimilarity is strictly finer than
basic-timed-HML equivalence.** `(A,0)` and `(B,0)` satisfy the same `TimedHML`
formulae yet are not timed bisimilar. -/
theorem timedHmlEquiv_and_not_timedBisimilar_sq2 (hc : 0 < c) :
    (sq2TLTS c).TimedHMLEquiv (Sq2.A 0) (Sq2.B 0) ∧
    ¬ (sq2TLTS c).TimedBisimilar (Sq2.A 0) (Sq2.B 0) :=
  ⟨timedHmlEquiv_sq2 c hc, not_timedBisimilar_sqrt2 c⟩

end DeepWiki.ReactiveSystems
