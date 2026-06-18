import DeepWiki.ReactiveSystems.CharacteristicFormulaTimed
import DeepWiki.ReactiveSystems.Simulation
import DeepWiki.ReactiveSystems.TimedSimulation

/-! # A characteristic formula modulo timed simulation (Exercise 12.21)
A *timed simulation* is the forward half of a timed bisimulation: `R` with `s₁ R s₂`
and `s₁ —α→ s₁'` (`α` an action *or* a delay) giving some `s₂ —α→ s₂'` with
`s₁' R s₂'`; `s₁ ⊑ s₂` (`s₁` is simulated by `s₂`) when some timed simulation relates
them — exactly `LTS.Simulated` on the combined action/delay LTS. The simulation
characteristic formula of the running example is its *bisimulation* characteristic
formula with the universal `[a]` conjunct dropped (a simulator need only *match* the
example's moves, not have its own moves matched back): `X =max (y ≤ 1 ⇒ ⟨a⟩(y in X))
∧ ∀∀X`. An extended state `(p, u)` (with `p` a state of the running example) satisfies
`X` exactly when the example's clock-`u(y)` state is simulated by `p` — the
simulation analogue of Theorem 12.5. (Over the delay-total running example the `∀∀X`
conjunct captures the `∀t ∃` delay-matching a simulation needs.) -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-- Body of the *simulation* characteristic formula: the bisimulation `charBody`
without its universal `[a]` conjunct — `(y ≤ 1 ⇒ ⟨a⟩(y in X)) ∧ ∀∀X`. -/
def charSimBody : MtR Unit Unit :=
  .and
    (.or (.guard (.atom () .gt 1)) (.dia () (.reset () .var)))
    (.forallDelay .var)

/-- The simulation characteristic formula `X` of the running example, as the greatest
fixed point of `charSimBody`. -/
def charSimFormula : Set (ℝ≥0 × Valuation Unit) := recMax runTLTS charSimBody

/-- **Fixed-point unfolding.** `(p, u)` satisfies the simulation characteristic
formula iff (1) `u(y) > 1`, or `p` can fire `a` into a state still satisfying it after
resetting `y`; and (2) every delay successor still satisfies it. -/
theorem mem_charSimFormula {q : ℝ≥0 × Valuation Unit} :
    q ∈ charSimFormula ↔
      ((1 : ℝ≥0) < q.2 () ∨
          ∃ p', runTLTS.act q.1 () p' ∧ (p', Valuation.reset {()} q.2) ∈ charSimFormula) ∧
        (∀ t p', runTLTS.delay q.1 t p' → (p', q.2.add t) ∈ charSimFormula) := by
  have h : charSimFormula = denotMtR runTLTS charSimBody charSimFormula :=
    (denotMtR_recMax runTLTS charSimBody).symm
  conv_lhs => rw [h]
  simp only [charSimBody, denotMtR, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
    Cmp.holds, Nat.cast_one]

/-- **Soundness (Theorem 12.5 modulo simulation, ⇐).** If the running example's
clock-`u(y)` state is simulated by `p`, then `(p, u)` satisfies the simulation
characteristic formula. Proved by coinduction: the "simulated-by" relation is a
post-fixed point of `charSimBody`. -/
theorem charSimFormula_sound {q : ℝ≥0 × Valuation Unit}
    (hs : TimedSimulated runTLTS (q.2 ()) q.1) : q ∈ charSimFormula := by
  have key : {r : ℝ≥0 × Valuation Unit | TimedSimulated runTLTS (r.2 ()) r.1} ⊆
      denotMtR runTLTS charSimBody {r | TimedSimulated runTLTS (r.2 ()) r.1} := by
    rintro ⟨d, w⟩ hs'
    simp only [Set.mem_setOf_eq] at hs'
    obtain ⟨R, hR, hRel⟩ := hs'
    have hreset : (Valuation.reset {()} w) () = 0 := Valuation.reset_mem rfl w
    simp only [charSimBody, denotMtR, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, satisfies,
      Cmp.holds, Nat.cast_one]
    refine ⟨?_, ?_⟩
    · -- conjunct 1: y > 1, or `a` is matched into the relation
      by_cases h1 : w () ≤ 1
      · right
        obtain ⟨d', hstep, hR0⟩ := hR hRel (Sum.inl ()) 0 (RunStep.act h1)
        exact ⟨d', hstep, by rw [hreset]; exact ⟨R, hR, hR0⟩⟩
      · exact Or.inl (not_le.mp h1)
    · -- conjunct 2: every delay is matched into the relation
      intro t p' hp'
      cases hp' with
      | delay =>
          obtain ⟨d'', hstep, hRwt⟩ := hR hRel (Sum.inr t) (w () + t) (RunStep.delay (w ()) t)
          cases hstep with
          | delay => rw [Valuation.add_apply]; exact ⟨R, hR, hRwt⟩
  exact (denotMtRHom runTLTS charSimBody).le_gfp key hs

/-- **Completeness (Theorem 12.5 modulo simulation, ⇒).** If `(p, u)` satisfies the
simulation characteristic formula, then the running example's clock-`u(y)` state is
simulated by `p`. Proved by exhibiting `R a b := (b, [y = a]) ⊨ X` as a timed
simulation (its forward clauses are read off from `mem_charSimFormula`). -/
theorem charSimFormula_complete {q : ℝ≥0 × Valuation Unit} (hq : q ∈ charSimFormula) :
    TimedSimulated runTLTS (q.2 ()) q.1 := by
  have hr0 : ∀ c : ℝ≥0, Valuation.reset {()} (fun _ : Unit => c) = (fun _ => (0 : ℝ≥0)) := by
    intro c; funext u; cases u; exact Valuation.reset_mem rfl (fun _ : Unit => c)
  have hadd : ∀ c t : ℝ≥0, Valuation.add (fun _ : Unit => c) t = (fun _ => c + t) := by
    intro c t; funext u; rw [Valuation.add_apply]
  have hR : LTS.IsSimulation runTLTS
      (fun a b : ℝ≥0 => (b, fun _ : Unit => a) ∈ charSimFormula) := by
    rintro a b hab l a' hstep
    obtain ⟨hC1, hC3⟩ := mem_charSimFormula.1 hab
    dsimp only at hC1 hC3
    cases l with
    | inl u =>
        obtain rfl : u = () := rfl
        cases hstep with
        | act ha1 =>
            rcases hC1 with h1 | ⟨p', hp', hmem⟩
            · exact absurd h1 (not_lt.mpr ha1)
            · cases hp' with
              | act hb1 =>
                  refine ⟨0, RunStep.act hb1, ?_⟩
                  rwa [hr0] at hmem
    | inr t =>
        cases hstep with
        | delay =>
            refine ⟨b + t, RunStep.delay b t, ?_⟩
            have hm := hC3 t (b + t) (RunStep.delay b t)
            rwa [hadd] at hm
  have hq2 : q.2 = fun _ : Unit => q.2 () := by funext u; cases u; rfl
  exact ⟨_, hR, by rw [← hq2]; exact hq⟩

/-- **Theorem 12.5 modulo timed simulation (Exercise 12.21).** A state `(p, u)`
satisfies the simulation characteristic formula `X` iff the running example's
clock-`u(y)` state is simulated by `p`. -/
theorem mem_charSimFormula_iff_simulated {q : ℝ≥0 × Valuation Unit} :
    q ∈ charSimFormula ↔ TimedSimulated runTLTS (q.2 ()) q.1 :=
  ⟨charSimFormula_complete, charSimFormula_sound⟩

end TLTS

end DeepWiki.ReactiveSystems
