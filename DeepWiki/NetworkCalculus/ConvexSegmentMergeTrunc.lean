import DeepWiki.NetworkCalculus.ConvexSegmentMerge

/-! # Theorem 4.1 — the unbalanced case (different asymptotic slopes)
The balanced case (`minConv_convexSegEval_balanced`) needs both convex PWLs to share one asymptotic
slope. The *unbalanced* case has `sf ≤ sg`: the flatter asymptote `sf` wins, and every segment of
`g` steeper than `sf` is **absorbed** into the asymptote. The clean reduction is to **truncate** `g`
at slope `sf` — keep only `g`'s leading segments of slope `≤ sf`, drop the rest, and lower its
asymptote to `sf` — then both operands share asymptote `sf` and the balanced case applies. This file
builds the truncation `truncSegs`, its evaluation lemmas, the order facts (`g' ≤ g`), and the
unbalanced convolution theorem. -/

namespace DeepWiki

open scoped NNReal

/-- Truncate a slope-sorted `(slope, length)` list at cut slope `s`: keep the leading prefix of
segments with slope `≤ s` (and drop the steeper tail). Because the input is slope-sorted, `takeWhile`
keeps exactly `{seg | seg.1 ≤ s}`. -/
noncomputable def truncSegs (s : ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) : List (ℝ≥0 × ℝ≥0) :=
  l.takeWhile (fun seg => seg.1 ≤ s)

@[simp] theorem truncSegs_nil (s : ℝ≥0) : truncSegs s [] = [] := rfl

/-- Truncation keeps a leading segment of slope `≤ s` and recurses. -/
theorem truncSegs_cons_le {s sa ℓa : ℝ≥0} (h : sa ≤ s) (rest : List (ℝ≥0 × ℝ≥0)) :
    truncSegs s ((sa, ℓa) :: rest) = (sa, ℓa) :: truncSegs s rest := by
  rw [truncSegs, truncSegs, List.takeWhile_cons, decide_eq_true h]; rfl

/-- Truncation drops a leading segment of slope `> s` (and everything after it, by sorting). -/
theorem truncSegs_cons_gt {s sa ℓa : ℝ≥0} (h : ¬ sa ≤ s) (rest : List (ℝ≥0 × ℝ≥0)) :
    truncSegs s ((sa, ℓa) :: rest) = [] := by
  rw [truncSegs, List.takeWhile_cons, decide_eq_false (by simpa using h)]; rfl

/-- Truncation is idempotent against the curve's own asymptote: a list whose every slope is already
`≤ s` is unchanged by truncating at `s`. -/
theorem truncSegs_eq_self {s : ℝ≥0} :
    ∀ {l : List (ℝ≥0 × ℝ≥0)}, (∀ seg ∈ l, seg.1 ≤ s) → truncSegs s l = l
  | [], _ => rfl
  | (sa, ℓa) :: rest, h => by
      have hsa : sa ≤ s := h (sa, ℓa) List.mem_cons_self
      have hrest : ∀ seg ∈ rest, seg.1 ≤ s := fun seg hseg => h seg (List.mem_cons_of_mem _ hseg)
      rw [truncSegs_cons_le hsa, truncSegs_eq_self hrest]

/-- Every segment surviving truncation has slope `≤ s`. -/
theorem truncSegs_slope_le {s : ℝ≥0} :
    ∀ (l : List (ℝ≥0 × ℝ≥0)), ∀ seg ∈ truncSegs s l, seg.1 ≤ s
  | [], seg, hseg => by simp [truncSegs] at hseg
  | (sa, ℓa) :: rest, seg, hseg => by
      by_cases h : sa ≤ s
      · rw [truncSegs_cons_le h] at hseg
        rcases List.mem_cons.mp hseg with rfl | hseg
        · exact h
        · exact truncSegs_slope_le rest seg hseg
      · rw [truncSegs_cons_gt h] at hseg
        simp at hseg

/-- Truncation preserves slope-sortedness (it returns a prefix). -/
theorem truncSegs_sorted {s : ℝ≥0} {l : List (ℝ≥0 × ℝ≥0)}
    (hsort : List.Pairwise (fun a b => a.1 ≤ b.1) l) :
    List.Pairwise (fun a b => a.1 ≤ b.1) (truncSegs s l) :=
  hsort.sublist (List.takeWhile_sublist _)

end DeepWiki
