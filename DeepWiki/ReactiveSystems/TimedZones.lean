import DeepWiki.ReactiveSystems.TimedBisimulationUntimed
import DeepWiki.ReactiveSystems.TimedAutomata

/-! # Zones and the symbolic reachability graph (§11.5)
A *zone* is a set of clock valuations (the book describes it by an extended clock
constraint `g_Z ∈ B⁺(C)` with diagonal constraints `x − y ⋈ n`, but the zone
*is* the set `{v | v ⊨ g_Z}`; the syntactic description is only what makes zones
finitely representable as difference-bound matrices). The two zone operations
(Definition 11.15) — the *future* `Z↑` and the *reset* `Z[r]` — and the symbolic
transition relation `⤳` (Definition 11.16) lift the timed-automaton semantics to
sets of valuations. **Theorem 11.5**: the symbolic semantics is sound and
complete with respect to the concrete transitions, hence with respect to
reachability. We work with zones as plain valuation sets, so the soundness and
completeness hold for arbitrary sets; closure of *constraint-describable* zones
under the operations (the DBM theory) is what §11.5 cites externally. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {Loc Act C : Type*}

/-! ## Definition 11.15: the two zone operations -/

/-- The set of valuations satisfying a clock constraint `g` (the zone `⟦g⟧`). -/
def zoneGuard (g : ClockConstraint C) : Set (Valuation C) := {v | satisfies v g}

/-- **Definition 11.15.** The *future* `Z↑` of a zone: all delays of its
valuations, `{v + d | v ∈ Z, d ≥ 0}`. -/
def zoneUp (Z : Set (Valuation C)) : Set (Valuation C) :=
  {w | ∃ v ∈ Z, ∃ d : ℝ≥0, w = v.add d}

/-- **Definition 11.15.** The *reset* `Z[r]` of a zone: reset the clocks in `r` in
every valuation of `Z`. -/
def zoneReset (r : Set C) (Z : Set (Valuation C)) : Set (Valuation C) :=
  {w | ∃ v ∈ Z, w = Valuation.reset r v}

/-! ## Definition 11.16: the symbolic transition relation -/

/-- **Definition 11.16.** The symbolic transition relation `⤳` over symbolic
states `(ℓ, Z)` (here in curried form `SymStep A ℓ Z ℓ' Z'`): a *delay* step
takes the future of `Z` intersected with the location invariant, and an *action*
step follows an edge `ℓ —g,a,r→ ℓ'` by guarding, resetting and re-imposing the
target invariant. -/
inductive SymStep (A : TimedAutomaton Loc Act C) :
    Loc → Set (Valuation C) → Loc → Set (Valuation C) → Prop
  /-- Delay: `(ℓ, Z) ⤳ (ℓ, Z↑ ∧ I(ℓ))`. -/
  | delay (ℓ : Loc) (Z : Set (Valuation C)) :
      SymStep A ℓ Z ℓ (zoneUp Z ∩ zoneGuard (A.inv ℓ))
  /-- Action: `(ℓ, Z) ⤳ (ℓ', (Z ∧ g)[r] ∧ I(ℓ'))` for an edge `ℓ —g,a,r→ ℓ'`. -/
  | act {ℓ : Loc} (Z : Set (Valuation C)) {g : ClockConstraint C} {a : Act}
      {r : Set C} {ℓ' : Loc} (h : A.edge ℓ g a r ℓ') :
      SymStep A ℓ Z ℓ' (zoneReset r (Z ∩ zoneGuard g) ∩ zoneGuard (A.inv ℓ'))

/-! ## Theorem 11.5: soundness and completeness of the symbolic semantics -/

/-- **Theorem 11.5** (soundness, §11.5). Whenever `(ℓ, Z) ⤳ (ℓ', Z')` and
`v' ∈ Z'`, some valuation `v ∈ Z` takes a concrete transition `(ℓ, v) → (ℓ', v')`
(an action or a delay). For the delay step this needs the source zone to respect
the location invariant (`Z ⊆ ⟦I(ℓ)⟧`), which every reachable symbolic state
does. -/
theorem symStep_sound (A : TimedAutomaton Loc Act C) {ℓ ℓ' : Loc}
    {Z Z' : Set (Valuation C)} (hstep : SymStep A ℓ Z ℓ' Z')
    (hZinv : Z ⊆ zoneGuard (A.inv ℓ)) {v' : Valuation C} (hv' : v' ∈ Z') :
    ∃ v ∈ Z, ∃ lab, A.tlts.untimedLTS.step (ℓ, v) lab (ℓ', v') := by
  cases hstep with
  | delay =>
      simp only [Set.mem_inter_iff, zoneUp, zoneGuard, Set.mem_setOf_eq] at hv'
      obtain ⟨⟨v, hvZ, d, rfl⟩, hinv⟩ := hv'
      exact ⟨v, hvZ, none, d, (TimedAutomaton.tlts_delay_iff A ℓ v d ℓ (v.add d)).mpr
        ⟨rfl, rfl, hZinv hvZ, hinv⟩⟩
  | act hedge =>
      simp only [Set.mem_inter_iff, zoneReset, zoneGuard, Set.mem_setOf_eq] at hv'
      obtain ⟨⟨w, ⟨hwZ, hwg⟩, rfl⟩, hinv⟩ := hv'
      exact ⟨w, hwZ, some _, (TimedAutomaton.tlts_act_iff A ℓ w _ ℓ' (Valuation.reset _ w)).mpr
        ⟨_, _, hedge, hwg, rfl, hinv⟩⟩

/-- **Theorem 11.5** (completeness for action steps, §11.5). A concrete action
transition `(ℓ, v) —a→ (ℓ', v')` from `v ∈ Z` is captured by a symbolic
transition `(ℓ, Z) ⤳ (ℓ', Z')` with `v' ∈ Z'`. -/
theorem symStep_complete_act (A : TimedAutomaton Loc Act C) {ℓ ℓ' : Loc}
    {Z : Set (Valuation C)} {v v' : Valuation C} {a : Act} (hv : v ∈ Z)
    (hstep : A.tlts.act (ℓ, v) a (ℓ', v')) :
    ∃ Z', SymStep A ℓ Z ℓ' Z' ∧ v' ∈ Z' := by
  rw [TimedAutomaton.tlts_act_iff] at hstep
  obtain ⟨g, r, hedge, hvg, rfl, hinv⟩ := hstep
  exact ⟨_, SymStep.act Z hedge, ⟨v, ⟨hv, hvg⟩, rfl⟩, hinv⟩

/-- **Theorem 11.5** (completeness for delay steps, §11.5). A concrete delay
transition `(ℓ, v) —d→ (ℓ, v')` from `v ∈ Z` is captured by the symbolic delay
step `(ℓ, Z) ⤳ (ℓ, Z↑ ∧ I(ℓ))` with `v' ∈ Z'`. -/
theorem symStep_complete_delay (A : TimedAutomaton Loc Act C) {ℓ : Loc}
    {Z : Set (Valuation C)} {v v' : Valuation C} {d : ℝ≥0} (hv : v ∈ Z)
    (hstep : A.tlts.delay (ℓ, v) d (ℓ, v')) :
    ∃ Z', SymStep A ℓ Z ℓ Z' ∧ v' ∈ Z' := by
  rw [TimedAutomaton.tlts_delay_iff] at hstep
  obtain ⟨_, rfl, _, hinv⟩ := hstep
  exact ⟨_, SymStep.delay ℓ Z, ⟨v, hv, d, rfl⟩, hinv⟩

end DeepWiki.ReactiveSystems
