import DeepWiki.ReactiveSystems.TimedRegionsBisimulation
import DeepWiki.ReactiveSystems.TimedHmlClocks
import DeepWiki.ReactiveSystems.TimedHmlIntervalDelay

/-! # Symbolic model checking — combined-clock plumbing (§12.2)
Theorem 12.1 relates concrete satisfaction `((ℓ,v),u) ⊨ F` (automaton clocks `v`
over `C`, formula clocks `u` over `D`) to symbolic satisfaction `[ℓ, [vu]] ⊢ F`,
where `vu` is the combined valuation over the disjoint union `C ⊎ D`. We model
`C ∪ D` as the sum type `C ⊕ D` and `vu` as `combineVal v u = Sum.elim v u`, and
record the bridge lemmas tying the combined valuation to its two components under
the operations the symbolic clauses use: delay (`+ t` on both), an automaton-clock
reset (`Sum.inl '' r`, hitting only `C`), and a formula-clock reset (`Sum.inr x`,
hitting only `D`). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {C D : Type*}

/-- The combined valuation `vu` over `C ⊕ D` from an automaton-clock valuation `v`
and a formula-clock valuation `u`: `vu (inl c) = v c`, `vu (inr d) = u d`. -/
def combineVal (v : Valuation C) (u : Valuation D) : Valuation (C ⊕ D) := Sum.elim v u

@[simp] theorem combineVal_inl (v : Valuation C) (u : Valuation D) (c : C) :
    combineVal v u (Sum.inl c) = v c := rfl

@[simp] theorem combineVal_inr (v : Valuation C) (u : Valuation D) (d : D) :
    combineVal v u (Sum.inr d) = u d := rfl

/-- A delay advances both components: `(vu) + t = (v+t)(u+t)`. -/
theorem combineVal_add (v : Valuation C) (u : Valuation D) (t : ℝ≥0) :
    (combineVal v u).add t = combineVal (v.add t) (u.add t) := by
  funext x; cases x <;> simp [combineVal, Valuation.add_apply]

/-- Resetting the automaton clocks `Sum.inl '' r` in the combined valuation resets
`r` in the `C`-component and leaves the `D`-component untouched. -/
theorem reset_inl_combineVal (r : Set C) (v : Valuation C) (u : Valuation D) :
    Valuation.reset (Sum.inl '' r) (combineVal v u) = combineVal (Valuation.reset r v) u := by
  funext z
  cases z with
  | inl c => by_cases h : c ∈ r <;> simp [Valuation.reset, combineVal, Set.mem_image, h]
  | inr d => simp [Valuation.reset, combineVal, Set.mem_image]

/-- Resetting a single formula clock `Sum.inr x` in the combined valuation resets
`x` in the `D`-component and leaves the `C`-component untouched. -/
theorem reset_inr_combineVal (x : D) (v : Valuation C) (u : Valuation D) :
    Valuation.reset {Sum.inr x} (combineVal v u) = combineVal v (Valuation.reset {x} u) := by
  funext z
  cases z with
  | inl c => simp [Valuation.reset, combineVal, Set.mem_singleton_iff]
  | inr d =>
      by_cases h : d = x <;>
        simp [Valuation.reset, combineVal, Set.mem_singleton_iff, Sum.inr.injEq, h]

/-- The base case of Theorem 12.1's combined valuation: both components zero. -/
@[simp] theorem combineVal_zero :
    combineVal (fun _ : C => (0 : ℝ≥0)) (fun _ : D => (0 : ℝ≥0)) = fun _ => 0 := by
  funext x; cases x <;> rfl

end DeepWiki.ReactiveSystems
