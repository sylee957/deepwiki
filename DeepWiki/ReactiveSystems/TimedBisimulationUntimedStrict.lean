import DeepWiki.ReactiveSystems.TimedBisimulationUntimed

/-! # Timed bisimilarity is strictly finer than untimed (§11.2)
Timed bisimilarity refines untimed bisimilarity (`TimedBisimilar.untimedBisimilar`);
this file shows the refinement is *strict* — the converse fails. The witness is a
two-state TLTS: state `A` may idle for *any* delay, while `B` may idle only for
delays `≤ 1`; both do the single action, reaching a dead state. Forgetting
durations, `A` and `B` match each other's moves, so they are **untimed bisimilar**;
but `A` can delay `2`, which `B` cannot match, so they are **not timed bisimilar**. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The three states of the witness: `A` (idles for any delay), `B` (idles only
for delays `≤ 1`), and the dead state `Stop`. -/
inductive ThreeState
  | A | B | Stop
  deriving DecidableEq

/-- The witness TLTS: `A —d→ A` for every delay `d`; `B —d→ B` only when `d ≤ 1`;
both `A` and `B` do the single action to `Stop`; `Stop` is dead. -/
def witnessTLTS : TLTS ThreeState Unit where
  step p l q :=
    match p, l, q with
    | .A, .inl _, .Stop => True
    | .A, .inr _, .A => True
    | .B, .inl _, .Stop => True
    | .B, .inr d, .B => d ≤ 1
    | _, _, _ => False

namespace witnessTLTS

/-- `A`'s untimed moves: the action goes to `Stop`, a delay keeps it at `A`. -/
theorem untimed_A (a : Option Unit) (q : ThreeState) :
    witnessTLTS.untimedLTS.step ThreeState.A a q ↔
      (a = some () ∧ q = .Stop) ∨ (a = none ∧ q = .A) := by
  cases a with
  | some u =>
      cases u; cases q <;>
        simp [TLTS.untimedLTS, TLTS.act, witnessTLTS]
  | none =>
      cases q <;>
        simp only [TLTS.untimedLTS, TLTS.delay, witnessTLTS, reduceCtorEq, false_and,
          true_and, or_false, false_or]
      · exact ⟨fun _ => trivial, fun _ => ⟨0, trivial⟩⟩
      · exact ⟨fun ⟨_, h⟩ => h, fun h => h.elim⟩
      · exact ⟨fun ⟨_, h⟩ => h, fun h => h.elim⟩

/-- `B`'s untimed moves: the action goes to `Stop`, a delay keeps it at `B` (some
`d ≤ 1` always exists). -/
theorem untimed_B (a : Option Unit) (q : ThreeState) :
    witnessTLTS.untimedLTS.step ThreeState.B a q ↔
      (a = some () ∧ q = .Stop) ∨ (a = none ∧ q = .B) := by
  cases a with
  | some u =>
      cases u; cases q <;>
        simp [TLTS.untimedLTS, TLTS.act, witnessTLTS]
  | none =>
      cases q <;>
        simp only [TLTS.untimedLTS, TLTS.delay, witnessTLTS, reduceCtorEq, false_and,
          true_and, or_false, false_or]
      · exact ⟨fun ⟨_, h⟩ => h, fun h => h.elim⟩
      · exact ⟨fun _ => trivial, fun _ => ⟨0, by simp⟩⟩
      · exact ⟨fun ⟨_, h⟩ => h, fun h => h.elim⟩

/-- `Stop` is dead in the untimed LTS. -/
theorem untimed_Stop (a : Option Unit) (q : ThreeState) :
    ¬ witnessTLTS.untimedLTS.step ThreeState.Stop a q := by
  cases a with
  | some u => cases u; simp [TLTS.untimedLTS, TLTS.act, witnessTLTS]
  | none => simp only [TLTS.untimedLTS, TLTS.delay, witnessTLTS]; rintro ⟨d, h⟩; exact h

end witnessTLTS

/-- The candidate untimed bisimulation: `A`/`B` are related (both orders), every
state to itself. -/
def witnessRel : ThreeState → ThreeState → Prop :=
  fun x y => (x = .A ∧ y = .B) ∨ (x = .B ∧ y = .A) ∨ x = y

/-- `witnessRel` is an untimed bisimulation. -/
theorem isBisimulation_witnessRel :
    LTS.IsBisimulation witnessTLTS.untimedLTS witnessRel := by
  have step_rel : ∀ {x : ThreeState}, (x = .A ∨ x = .B) → ∀ a q,
      witnessTLTS.untimedLTS.step x a q →
        (a = some () ∧ q = .Stop) ∨ (a = none ∧ q = x) := by
    rintro x (rfl | rfl) a q h
    · exact (witnessTLTS.untimed_A a q).mp h
    · exact (witnessTLTS.untimed_B a q).mp h
  have mk_A : ∀ a q, ((a = some () ∧ q = .Stop) ∨ (a = none ∧ q = .A)) →
      witnessTLTS.untimedLTS.step ThreeState.A a q := fun a q h => (witnessTLTS.untimed_A a q).mpr h
  have mk_B : ∀ a q, ((a = some () ∧ q = .Stop) ∨ (a = none ∧ q = .B)) →
      witnessTLTS.untimedLTS.step ThreeState.B a q := fun a q h => (witnessTLTS.untimed_B a q).mpr h
  rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl)
  · -- (A, B)
    refine ⟨fun a x' hx => ?_, fun a y' hy => ?_⟩
    · rcases step_rel (Or.inl rfl) a x' hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.Stop, mk_B _ _ (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr rfl)⟩
      · exact ⟨.B, mk_B _ _ (Or.inr ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩⟩
    · rcases step_rel (Or.inr rfl) a y' hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.Stop, mk_A _ _ (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr rfl)⟩
      · exact ⟨.A, mk_A _ _ (Or.inr ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩⟩
  · -- (B, A)
    refine ⟨fun a x' hx => ?_, fun a y' hy => ?_⟩
    · rcases step_rel (Or.inr rfl) a x' hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.Stop, mk_A _ _ (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr rfl)⟩
      · exact ⟨.A, mk_A _ _ (Or.inr ⟨rfl, rfl⟩), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · rcases step_rel (Or.inl rfl) a y' hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.Stop, mk_B _ _ (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr rfl)⟩
      · exact ⟨.B, mk_B _ _ (Or.inr ⟨rfl, rfl⟩), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · -- diagonal
    exact ⟨fun a x' hx => ⟨x', hx, Or.inr (Or.inr rfl)⟩,
           fun a y' hy => ⟨y', hy, Or.inr (Or.inr rfl)⟩⟩

/-- **§11.2.** `A` and `B` are untimed bisimilar (durations forgotten). -/
theorem A_untimedBisimilar_B : witnessTLTS.UntimedBisimilar .A .B :=
  ⟨witnessRel, isBisimulation_witnessRel, Or.inl ⟨rfl, rfl⟩⟩

/-- **§11.2.** `A` and `B` are **not** timed bisimilar: `A` can delay `2` but `B`
(idling only for delays `≤ 1`) cannot match it. -/
theorem not_A_timedBisimilar_B : ¬ witnessTLTS.TimedBisimilar .A .B := by
  intro h
  obtain ⟨_, _, hd1, _⟩ := (TLTS.timedBisimilar_iff witnessTLTS .A .B).mp h
  obtain ⟨q', hq', _⟩ := hd1 2 .A trivial
  -- `hq' : witnessTLTS.delay B 2 q'` forces `q' = B ∧ (2 : ℝ≥0) ≤ 1`, impossible
  cases q' <;> simp [TLTS.delay, witnessTLTS] at hq'

/-- **§11.2** (strictness). Timed bisimilarity is *strictly* finer than untimed:
untimed-bisimilar states need not be timed bisimilar. -/
theorem untimedBisimilar_not_imp_timedBisimilar :
    ∃ (Q : Type) (T : TLTS Q Unit) (p q : Q), T.UntimedBisimilar p q ∧ ¬ T.TimedBisimilar p q :=
  ⟨ThreeState, witnessTLTS, .A, .B, A_untimedBisimilar_B, not_A_timedBisimilar_B⟩

end DeepWiki.ReactiveSystems
