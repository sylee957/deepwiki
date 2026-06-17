import DeepWiki.ReactiveSystems.TimedAutomata

/-! # Networks of timed automata
A *network* of timed automata is a parallel composition `A₁ ∣ A₂ ∣ … ∣ Aₙ` of
components over a shared clock set, communicating by hand-shake synchronisation on
channels `c!`/`c?` (always forced — channels are restricted) and otherwise moving
independently on ordinary actions `N`. We model the **binary**
composition (the general `n`-ary case iterates it; the book's examples are
binary): a location pair `(ℓ₁, ℓ₂)`, the conjoined invariant `I₁(ℓ₁) ∧ I₂(ℓ₂)`,
and edges that are either an independent `N`-move of one component or a `τ`
synchronisation of complementary channel edges (with conjoined guards and unioned
resets). Realised as an ordinary `TimedAutomaton` over `L₁ × L₂`, so its TLTS
`T(A)` is just `.tlts` — the simultaneous-delay rule falls out
of the conjoined invariant. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- Network actions (the book's `Act = {c! ∣ c} ∪ {c? ∣ c} ∪ N`): channel output
`out c` (`c!`), channel input `inp c` (`c?`), an ordinary action `ord a ∈ N`, and
the silent `τ ∈ N`. -/
inductive NetAct (Chan Ord : Type*)
  | out : Chan → NetAct Chan Ord
  | inp : Chan → NetAct Chan Ord
  | ord : Ord → NetAct Chan Ord
  | tau : NetAct Chan Ord

/-- The actions in `N` (ordinary actions and `τ`) — those a component may perform
independently; channel actions `c!`/`c?` must synchronise. -/
def NetAct.IsN {Chan Ord : Type*} : NetAct Chan Ord → Prop
  | .out _ => False
  | .inp _ => False
  | .ord _ => True
  | .tau => True

variable {Chan Ord C L₁ L₂ : Type*}

/-- The binary network `A₁ ∣ A₂` as a timed automaton
over location pairs `L₁ × L₂`: the invariant of `(ℓ₁, ℓ₂)` is `I₁(ℓ₁) ∧ I₂(ℓ₂)`,
and an edge is either an independent `N`-move of one component (the other staying
put) or a `τ`-synchronisation of complementary channel edges (`c!` in one, `c?` in
the other) with conjoined guard and unioned resets. Its `.tlts` is the network's
TLTS `T(A)`. -/
def networkAutomaton (A₁ : TimedAutomaton L₁ (NetAct Chan Ord) C)
    (A₂ : TimedAutomaton L₂ (NetAct Chan Ord) C) :
    TimedAutomaton (L₁ × L₂) (NetAct Chan Ord) C where
  initial := (A₁.initial, A₂.initial)
  edge p g a r q :=
    -- component 1 moves independently on an `N`-action
    (a.IsN ∧ A₁.edge p.1 g a r q.1 ∧ q.2 = p.2) ∨
    -- component 2 moves independently on an `N`-action
    (a.IsN ∧ A₂.edge p.2 g a r q.2 ∧ q.1 = p.1) ∨
    -- synchronisation of complementary channel edges into a `τ`-move
    (a = NetAct.tau ∧ ∃ c g₁ r₁ g₂ r₂,
      ((A₁.edge p.1 g₁ (NetAct.out c) r₁ q.1 ∧ A₂.edge p.2 g₂ (NetAct.inp c) r₂ q.2) ∨
       (A₁.edge p.1 g₁ (NetAct.inp c) r₁ q.1 ∧ A₂.edge p.2 g₂ (NetAct.out c) r₂ q.2)) ∧
      g = ClockConstraint.and g₁ g₂ ∧ r = r₁ ∪ r₂)
  inv p := ClockConstraint.and (A₁.inv p.1) (A₂.inv p.2)

/-- The TLTS `T(A)` of a network: the timed LTS of the network
automaton; states pair the component locations with the shared valuation. -/
noncomputable def networkTLTS (A₁ : TimedAutomaton L₁ (NetAct Chan Ord) C)
    (A₂ : TimedAutomaton L₂ (NetAct Chan Ord) C) :
    TLTS ((L₁ × L₂) × Valuation C) (NetAct Chan Ord) :=
  (networkAutomaton A₁ A₂).tlts

/-- The network synchronisation rule. When `A₁` can take an `out c` edge
and `A₂` a complementary `inp c` edge, with both guards holding and the resulting
valuation respecting both invariants, the network performs an internal `τ`-move. -/
theorem networkTLTS_sync (A₁ : TimedAutomaton L₁ (NetAct Chan Ord) C)
    (A₂ : TimedAutomaton L₂ (NetAct Chan Ord) C) {ℓ₁ ℓ₁' : L₁} {ℓ₂ ℓ₂' : L₂}
    {c : Chan} {g₁ g₂ : ClockConstraint C} {r₁ r₂ : Set C} {v : Valuation C}
    (h₁ : A₁.edge ℓ₁ g₁ (NetAct.out c) r₁ ℓ₁') (h₂ : A₂.edge ℓ₂ g₂ (NetAct.inp c) r₂ ℓ₂')
    (hg : satisfies v (ClockConstraint.and g₁ g₂))
    (hinv : satisfies (Valuation.reset (r₁ ∪ r₂) v)
      ((networkAutomaton A₁ A₂).inv (ℓ₁', ℓ₂'))) :
    (networkTLTS A₁ A₂).act ((ℓ₁, ℓ₂), v) NetAct.tau ((ℓ₁', ℓ₂'), Valuation.reset (r₁ ∪ r₂) v) := by
  rw [networkTLTS, TimedAutomaton.tlts_act_iff]
  exact ⟨ClockConstraint.and g₁ g₂, r₁ ∪ r₂,
    Or.inr (Or.inr ⟨rfl, c, g₁, r₁, g₂, r₂, Or.inl ⟨h₁, h₂⟩, rfl, rfl⟩), hg, rfl, hinv⟩

/-- The network simultaneous-delay rule (consequence of the conjoined
invariant): the network delays `d` iff both components' invariants hold before and
after — both clocks advance by the same `d`. -/
theorem networkTLTS_delay_iff (A₁ : TimedAutomaton L₁ (NetAct Chan Ord) C)
    (A₂ : TimedAutomaton L₂ (NetAct Chan Ord) C) (ℓ₁ : L₁) (ℓ₂ : L₂) (v : Valuation C)
    (d : ℝ≥0) (q : (L₁ × L₂) × Valuation C) :
    (networkTLTS A₁ A₂).delay ((ℓ₁, ℓ₂), v) d q ↔
      q = ((ℓ₁, ℓ₂), v.add d) ∧
        satisfies v (A₁.inv ℓ₁) ∧ satisfies v (A₂.inv ℓ₂) ∧
        satisfies (v.add d) (A₁.inv ℓ₁) ∧ satisfies (v.add d) (A₂.inv ℓ₂) := by
  rw [networkTLTS]
  obtain ⟨⟨ℓ', v'⟩⟩ := q
  rw [TimedAutomaton.tlts_delay_iff]
  simp only [networkAutomaton, satisfies, Prod.mk.injEq]
  tauto

end DeepWiki.ReactiveSystems
