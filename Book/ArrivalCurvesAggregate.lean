import Book.ArrivalCurves
import Book.DeviationsBounds

/-! # Arrival curves of aggregate flows
Several flows sharing a server are analyzed through their aggregate, the
pointwise sum of the cumulative processes: per-flow maximal arrival
curves sum to a maximal arrival curve of the aggregate, and conversely
an arrival curve of the aggregate constrains each non-decreasing
sub-flow (the cross-traffic increments are non-negative). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Arrival curve of an aggregate flow**: per-flow maximal arrival
bounds sum to a maximal arrival bound of the aggregate,
`∑ Aᵢ ≤ (∑ Aᵢ) ∗ (∑ αᵢ)`. -/
theorem isMaximalArrivalBound_sum {ι T : Type*} [_root_.AddCommMonoid T]
    [ConditionallyCompleteLattice T] [OrderBot T] [AddLeftMono T]
    (s : Finset ι) {A α : ι → ℝ≥0 → T}
    (h : ∀ i ∈ s, IsMaximalArrivalBound (A i) (α i)) :
    IsMaximalArrivalBound (fun t => ∑ i ∈ s, A i t)
      (fun t => ∑ i ∈ s, α i t) := by
  rw [isMaximalArrivalBound_iff_increment]
  intro t d
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i hi =>
    (isMaximalArrivalBound_iff_increment _ _).mp (h i hi) t d

/-- **Arrival curve of a sub-flow**: a maximal arrival curve of an
aggregate of non-decreasing flows is a maximal arrival curve of each
sub-flow — the cross-traffic increments are non-negative. -/
theorem isMaximalArrivalBound_of_sum {ι : Type*} {s : Finset ι}
    {A : ι → ℝ≥0 → ℝ≥0} {α : ℝ≥0 → ℝ≥0∞}
    (hmono : ∀ i ∈ s, Monotone (A i)) {j : ι} (hj : j ∈ s)
    (h : IsMaximalArrivalBound
      (Deviation.liftENN (fun t => ∑ i ∈ s, A i t)) α) :
    IsMaximalArrivalBound (Deviation.liftENN (A j)) α := by
  rw [isMaximalArrivalBound_iff_increment] at h ⊢
  intro t d
  have hkey : ((∑ i ∈ s, A i (t + d) : ℝ≥0) : ℝ≥0∞)
      ≤ ((∑ i ∈ s, A i t : ℝ≥0) : ℝ≥0∞) + α d := h t d
  rw [show (∑ i ∈ s, A i (t + d)) = A j (t + d) + ∑ i ∈ s.erase j, A i (t + d)
      from (Finset.add_sum_erase s (fun i => A i (t + d)) hj).symm,
    show (∑ i ∈ s, A i t) = A j t + ∑ i ∈ s.erase j, A i t
      from (Finset.add_sum_erase s (fun i => A i t) hj).symm] at hkey
  show ((A j (t + d) : ℝ≥0) : ℝ≥0∞) ≤ ((A j t : ℝ≥0) : ℝ≥0∞) + α d
  -- pad the sub-flow increment with the cross-traffic at time `t`
  have hpad : (A j (t + d) : ℝ≥0∞) + (∑ i ∈ s.erase j, A i t : ℝ≥0)
      ≤ ((A j t : ℝ≥0∞) + α d) + (∑ i ∈ s.erase j, A i t : ℝ≥0) := by
    calc (A j (t + d) : ℝ≥0∞) + (∑ i ∈ s.erase j, A i t : ℝ≥0)
        ≤ (A j (t + d) : ℝ≥0∞) + (∑ i ∈ s.erase j, A i (t + d) : ℝ≥0) := by
          refine add_le_add le_rfl (ENNReal.coe_le_coe.mpr ?_)
          exact Finset.sum_le_sum fun i hi =>
            hmono i (Finset.mem_of_mem_erase hi) le_self_add
      _ ≤ ((A j t : ℝ≥0∞) + (∑ i ∈ s.erase j, A i t : ℝ≥0)) + α d := by
          rw [← ENNReal.coe_add, ← ENNReal.coe_add]
          exact_mod_cast hkey
      _ = ((A j t : ℝ≥0∞) + α d) + (∑ i ∈ s.erase j, A i t : ℝ≥0) := by
          ring
  exact (ENNReal.add_le_add_iff_right ENNReal.coe_ne_top).mp hpad

/-! ## Book restatement (aggregation of flows)
For a finite index set, the aggregate cumulative process is
`A = ∑ᵢ Aᵢ` (a `Curve` again — `Curve.sum_apply`); if each `Aᵢ` has
arrival curve `αᵢ` then `∑ᵢ αᵢ` is an arrival curve of the aggregate,
and any arrival curve `α` of the aggregate is an arrival curve of each
sub-flow `Aⱼ`. -/
example {ι : Type*} (s : Finset ι) (A : ι → ℝ≥0 → ℝ≥0)
    (α : ι → ℝ≥0 → ℝ≥0∞)
    (h : ∀ i ∈ s, IsMaximalArrivalCurve (Deviation.liftENN (A i)) (α i)) :
    IsMaximalArrivalCurve (Deviation.liftENN (fun t => ∑ i ∈ s, A i t))
      (fun t => ∑ i ∈ s, α i t) := by
  refine ⟨fun a b hab => Finset.sum_le_sum fun i hi => (h i hi).1 hab, ?_⟩
  rw [Deviation.liftENN_sum]
  exact isMaximalArrivalBound_sum s fun i hi => (h i hi).2

example {ι : Type*} {s : Finset ι} (A : ι → ℝ≥0 → ℝ≥0) {α : ℝ≥0 → ℝ≥0∞}
    (hmono : ∀ i ∈ s, Monotone (A i)) {j : ι} (hj : j ∈ s)
    (h : IsMaximalArrivalCurve
      (Deviation.liftENN (fun t => ∑ i ∈ s, A i t)) α) :
    IsMaximalArrivalCurve (Deviation.liftENN (A j)) α :=
  ⟨h.1, isMaximalArrivalBound_of_sum hmono hj h.2⟩

end DeepWiki
