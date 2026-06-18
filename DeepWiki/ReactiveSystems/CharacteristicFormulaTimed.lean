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

end TLTS

end DeepWiki.ReactiveSystems
