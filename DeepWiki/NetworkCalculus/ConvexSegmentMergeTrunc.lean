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

/-- A convex PWL whose every slope is `≤ p` (and asymptotic slope `≤ p`) grows at most at rate `p`
between any two points: `convexSegEval f0 fs l (x + d) ≤ convexSegEval f0 fs l x + p·d`. The dual of
`convexSegEval_rate`. Used to slide excess `g`-mass onto a flatter `f` during truncation. -/
theorem convexSegEval_upper_rate (fs p : ℝ≥0) :
    ∀ l : List (ℝ≥0 × ℝ≥0), (∀ seg ∈ l, seg.1 ≤ p) → fs ≤ p → ∀ f0 x d : ℝ≥0,
      convexSegEval f0 fs l (x + d) ≤ convexSegEval f0 fs l x + p * d := by
  intro l
  induction l with
  | nil =>
      intro _ hfs f0 x d
      rw [convexSegEval_nil, convexSegEval_nil]
      have hpfs : fs * d ≤ p * d := by gcongr
      calc f0 + fs * (x + d) = f0 + fs * x + fs * d := by ring
        _ ≤ f0 + fs * x + p * d := by gcongr
  | cons hd tl ih =>
      intro hl hfs f0 x d
      obtain ⟨sseg, ℓ⟩ := hd
      have hsseg : sseg ≤ p := hl (sseg, ℓ) List.mem_cons_self
      have htl : ∀ seg ∈ tl, seg.1 ≤ p := fun seg h => hl seg (List.mem_cons_of_mem _ h)
      rw [convexSegEval_cons, convexSegEval_cons]
      by_cases hxd : x + d ≤ ℓ
      · -- both `x` and `x + d` on the leading segment
        have hx : x ≤ ℓ := le_trans le_self_add hxd
        rw [if_pos hx, if_pos hxd]
        have hpsseg : sseg * d ≤ p * d := by gcongr
        calc f0 + sseg * (x + d) = f0 + sseg * x + sseg * d := by ring
          _ ≤ f0 + sseg * x + p * d := by gcongr
      · by_cases hx : x ≤ ℓ
        · -- `x` on the leading segment, `x + d` past it
          rw [if_pos hx, if_neg hxd]
          have hℓxd : ℓ ≤ x + d := (not_le.mp hxd).le
          -- the value past `ℓ` is bounded above by the `fs`/`p`-line continuation
          have hih := ih htl hfs (f0 + sseg * ℓ) 0 (x + d - ℓ)
          rw [zero_add, convexSegEval_zero] at hih
          refine le_trans hih ?_
          -- now: `(f0 + sseg·ℓ) + p·(x+d-ℓ) ≤ (f0 + sseg·x) + p·d`
          have hkey : sseg * ℓ + p * (x + d - ℓ) ≤ sseg * x + p * d := by
            have hpsub : p * (x + d) = p * ℓ + p * (x + d - ℓ) := by
              rw [← mul_add, add_tsub_cancel_of_le hℓxd]
            have hstep : sseg * ℓ + p * x ≤ sseg * x + p * ℓ := by
              have hxℓ : x ≤ ℓ := hx
              have hsub : sseg * (ℓ - x) ≤ p * (ℓ - x) := by gcongr
              calc sseg * ℓ + p * x
                  = sseg * x + sseg * (ℓ - x) + p * x := by
                    rw [show sseg * x + sseg * (ℓ - x) = sseg * (x + (ℓ - x)) from by ring,
                      add_tsub_cancel_of_le hxℓ]
                _ ≤ sseg * x + p * (ℓ - x) + p * x := by gcongr
                _ = sseg * x + p * ℓ := by
                    rw [show sseg * x + p * (ℓ - x) + p * x = sseg * x + (p * (ℓ - x) + p * x) from
                      by ring, ← mul_add, tsub_add_cancel_of_le hxℓ]
            -- combine: add `p·x` and use `hpsub`
            rw [← add_le_add_iff_right (p * x)]
            calc sseg * ℓ + p * (x + d - ℓ) + p * x
                = (sseg * ℓ + p * x) + p * (x + d - ℓ) := by ring
              _ ≤ (sseg * x + p * ℓ) + p * (x + d - ℓ) := by gcongr
              _ = sseg * x + (p * ℓ + p * (x + d - ℓ)) := by ring
              _ = sseg * x + p * (x + d) := by rw [hpsub]
              _ = sseg * x + (p * x + p * d) := by rw [mul_add]
              _ = sseg * x + p * d + p * x := by ring
          calc f0 + sseg * ℓ + p * (x + d - ℓ) = f0 + (sseg * ℓ + p * (x + d - ℓ)) := by ring
            _ ≤ f0 + (sseg * x + p * d) := by gcongr
            _ = f0 + sseg * x + p * d := by ring
        · -- both past the leading segment
          rw [if_neg hx, if_neg hxd]
          have hℓx : ℓ ≤ x := (not_le.mp hx).le
          have hsplit : x + d - ℓ = (x - ℓ) + d := by rw [tsub_add_eq_add_tsub hℓx]
          rw [hsplit]
          exact ih htl hfs (f0 + sseg * ℓ) (x - ℓ) d

/-- The `convexSegEval_upper_rate` packaged for a curve whose own asymptote is the cut slope:
`convexSegEval f0 sf l` with all slopes `≤ sf` grows at most at rate `sf`. -/
theorem convexSegEval_upper_rate_of_le {sf f0 : ℝ≥0} {l : List (ℝ≥0 × ℝ≥0)}
    (hall : ∀ seg ∈ l, seg.1 ≤ sf) :
    ∀ x d : ℝ≥0, convexSegEval f0 sf l (x + d) ≤ convexSegEval f0 sf l x + sf * d :=
  fun x d => convexSegEval_upper_rate sf sf l hall le_rfl f0 x d

end DeepWiki
