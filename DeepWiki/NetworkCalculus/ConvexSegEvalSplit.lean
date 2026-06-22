import DeepWiki.NetworkCalculus.ConvexConcaveReadback

/-! # Splitting a convex PWL at the truncation breakpoint (toward Theorem 4.2 §4.2.2)
The convex-by-concave crossing of Theorem 4.2 needs a *minimum-growth-rate* fact: beyond the
token-bucket breakpoint `u* = segLenSum (truncSegs r fsegs)`, the convex PWL
`f = convexSegEval f0 fs fsegs` grows at rate at least `r`, because every remaining segment was
excluded from `truncSegs r` (slope `> r`) and the asymptote satisfies `r ≤ fs`.

The clean route is a **split-at-the-breakpoint decomposition**: for `t ≥ u*`,
`f t = convexSegEval (f u*) fs (dropSegs r fsegs) (t − u*)` — the prefix `truncSegs r fsegs`
fixes `[0, u*]`, and the dropped tail (`dropSegs`, all slopes `> r`), shifted to start at `u*`,
governs the rest. Applying `convexSegEval_rate` with `p = r` to that tail yields the growth bound.

This file builds `dropSegs` and its API, the general append-peel of `convexSegEval`, the split
decomposition, the minimum-growth-rate lemma, and the single-crossing structure (the `f ≤ line`
region is a down-set) that makes the Theorem 4.2 meet a single switch. -/

namespace DeepWiki

open scoped NNReal

/-- Drop the leading slope-`≤ s` prefix of a slope-sorted `(slope, length)` list, keeping the steep
tail; the complement of `truncSegs s` (`takeWhile ++ dropWhile = id`). -/
noncomputable def dropSegs (s : ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) : List (ℝ≥0 × ℝ≥0) :=
  l.dropWhile (fun seg => seg.1 ≤ s)

@[simp] theorem dropSegs_nil (s : ℝ≥0) : dropSegs s [] = [] := rfl

/-- `dropSegs` skips a leading segment of slope `≤ s` and recurses. -/
theorem dropSegs_cons_le {s sa ℓa : ℝ≥0} (h : sa ≤ s) (rest : List (ℝ≥0 × ℝ≥0)) :
    dropSegs s ((sa, ℓa) :: rest) = dropSegs s rest := by
  rw [dropSegs, dropSegs, List.dropWhile_cons_of_pos (by simpa using h)]

/-- `dropSegs` stops (keeps everything) at a leading segment of slope `> s`. -/
theorem dropSegs_cons_gt {s sa ℓa : ℝ≥0} (h : ¬ sa ≤ s) (rest : List (ℝ≥0 × ℝ≥0)) :
    dropSegs s ((sa, ℓa) :: rest) = (sa, ℓa) :: rest := by
  rw [dropSegs, List.dropWhile_cons_of_neg (by simpa using h)]

/-- `truncSegs s l ++ dropSegs s l = l`: the kept prefix and dropped tail reassemble the list. -/
theorem truncSegs_append_dropSegs (s : ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) :
    truncSegs s l ++ dropSegs s l = l :=
  List.takeWhile_append_dropWhile

/-- Every segment surviving `dropSegs s` of a slope-sorted list has slope `> s` (`¬ seg.1 ≤ s`,
hence `s ≤ seg.1`): the first slope-`> s` segment ends the kept prefix, and sortedness makes all
later slopes at least as large. -/
theorem dropSegs_slope_gt {s : ℝ≥0} :
    ∀ (l : List (ℝ≥0 × ℝ≥0)), List.Pairwise (fun a b => a.1 ≤ b.1) l →
      ∀ seg ∈ dropSegs s l, ¬ seg.1 ≤ s
  | [], _, seg, hseg => by simp [dropSegs] at hseg
  | (sa, ℓa) :: rest, hsort, seg, hseg => by
      by_cases hsa : sa ≤ s
      · rw [dropSegs_cons_le hsa] at hseg
        exact dropSegs_slope_gt rest (List.pairwise_cons.mp hsort).2 seg hseg
      · rw [dropSegs_cons_gt hsa] at hseg
        rcases List.mem_cons.mp hseg with rfl | hseg
        · exact hsa
        · -- a later segment: its slope dominates `sa > s`, so it too is `> s`
          intro hcon
          exact hsa (le_trans ((List.pairwise_cons.mp hsort).1 seg hseg) hcon)

/-- Every segment surviving `dropSegs s` of a slope-sorted list has slope `≥ s` (the `≤`-form of
`dropSegs_slope_gt`, ready for `convexSegEval_rate`'s `∀ seg ∈ l, p ≤ seg.1` hypothesis). -/
theorem dropSegs_slope_ge {s : ℝ≥0} (l : List (ℝ≥0 × ℝ≥0))
    (hsort : List.Pairwise (fun a b => a.1 ≤ b.1) l) :
    ∀ seg ∈ dropSegs s l, s ≤ seg.1 :=
  fun seg hseg => (not_le.mp (dropSegs_slope_gt l hsort seg hseg)).le

/-- **General append-peel.** Evaluating a concatenation `pre ++ suf` past the cumulative length of
`pre` peels the whole prefix: `convexSegEval f0 fs (pre ++ suf) (segLenSum pre + d)
= convexSegEval (convexSegEval f0 fs pre (segLenSum pre)) fs suf d`. (The corner value
`convexSegEval f0 fs pre (segLenSum pre)` is the base for the suffix; generalizes
`convexSegEval_cons_peel` from a one-segment prefix to an arbitrary one.) -/
theorem convexSegEval_append_peel (fs : ℝ≥0) :
    ∀ (pre suf : List (ℝ≥0 × ℝ≥0)) (f0 d : ℝ≥0),
      convexSegEval f0 fs (pre ++ suf) (segLenSum pre + d)
        = convexSegEval (convexSegEval f0 fs pre (segLenSum pre)) fs suf d := by
  intro pre
  induction pre with
  | nil =>
      intro suf f0 d
      rw [segLenSum_nil, List.nil_append, zero_add, convexSegEval_zero]
  | cons hd tl ih =>
      intro suf f0 d
      obtain ⟨s, ℓ⟩ := hd
      rw [segLenSum_cons, List.cons_append, convexSegEval_cons_peel,
        show ℓ + segLenSum tl + d = ℓ + (segLenSum tl + d) from by ring, convexSegEval_cons_peel,
        ih suf (f0 + s * ℓ) d]

/-- **Split at the breakpoint.** With `u* = segLenSum (truncSegs r fsegs)`, for `t ≥ u*` the convex
PWL splits as `f t = convexSegEval (f u*) fs (dropSegs r fsegs) (t − u*)`: the kept prefix fixes the
value `f u*` at the corner, and the dropped (steep) tail, restarted from there, governs the rest. -/
theorem convexSegEval_split_truncSegs (fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0)) (f0 : ℝ≥0)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t) :
    convexSegEval f0 fs fsegs t
      = convexSegEval (convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs))) fs
          (dropSegs r fsegs) (t - segLenSum (truncSegs r fsegs)) := by
  -- corner value: on `[0, u*]` truncated and untruncated agree
  have hcorner : convexSegEval f0 fs (truncSegs r fsegs) (segLenSum (truncSegs r fsegs))
      = convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) :=
    convexSegEval_truncSegs_eq_below r fs fsegs f0 _ le_rfl
  -- name `pre`/`suf` so the peel rewrite touches only the segment-list argument
  obtain ⟨pre, suf, hpre, hsuf, hsplit⟩ :
      ∃ pre suf, pre = truncSegs r fsegs ∧ suf = dropSegs r fsegs ∧ pre ++ suf = fsegs :=
    ⟨truncSegs r fsegs, dropSegs r fsegs, rfl, rfl, truncSegs_append_dropSegs r fsegs⟩
  have key : convexSegEval f0 fs fsegs (segLenSum pre + (t - segLenSum pre))
      = convexSegEval (convexSegEval f0 fs pre (segLenSum pre)) fs suf (t - segLenSum pre) := by
    rw [← hsplit, convexSegEval_append_peel]
  subst hpre hsuf
  rw [add_tsub_cancel_of_le ht] at key
  rw [key, hcorner]

/-- **Minimum growth rate beyond the breakpoint** (the Theorem 4.2 engine). For a slope-sorted
convex PWL `f = convexSegEval f0 fs fsegs` with `r ≤ fs`, beyond `u* = segLenSum (truncSegs r fsegs)`
the curve grows at rate at least `r`: `f u* + r·(t − u*) ≤ f t` for all `t ≥ u*`. Every remaining
segment was excluded from `truncSegs r` (slope `> r`) and the asymptote satisfies `r ≤ fs`, so the
dropped tail — restarted at `u*` via `convexSegEval_split_truncSegs` — grows at rate `≥ r`
(`convexSegEval_rate`). -/
theorem convexSegEval_rate_past_breakpoint (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t) :
    convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs))
        + r * (t - segLenSum (truncSegs r fsegs))
      ≤ convexSegEval f0 fs fsegs t := by
  set us := segLenSum (truncSegs r fsegs) with hus
  rw [convexSegEval_split_truncSegs fs r fsegs f0 ht, ← hus]
  -- the dropped tail has all slopes `≥ r`; apply the rate lemma from `x = 0`
  have hdrop : ∀ seg ∈ dropSegs r fsegs, r ≤ seg.1 := dropSegs_slope_ge fsegs hfsort
  have hrate := convexSegEval_rate fs r (dropSegs r fsegs) hdrop hrf
    (convexSegEval f0 fs fsegs us) 0 (t - us)
  rwa [convexSegEval_zero, zero_add] at hrate

/-- **Minimum growth rate from any point beyond the breakpoint.** For `u* ≤ t₁ ≤ t₂`, the convex
PWL grows at rate at least `r` between `t₁` and `t₂`: `f t₁ + r·(t₂ − t₁) ≤ f t₂`. (Strengthens
`convexSegEval_rate_past_breakpoint`, the `t₁ = u*` case, to an arbitrary lower endpoint past the
breakpoint — both points are read off the steep `dropSegs` tail, all of whose slopes are `≥ r`.) -/
theorem convexSegEval_rate_from_breakpoint (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs) (hrf : r ≤ fs)
    {t₁ t₂ : ℝ≥0} (h1 : segLenSum (truncSegs r fsegs) ≤ t₁) (h12 : t₁ ≤ t₂) :
    convexSegEval f0 fs fsegs t₁ + r * (t₂ - t₁) ≤ convexSegEval f0 fs fsegs t₂ := by
  set us := segLenSum (truncSegs r fsegs) with hus
  -- read both points off the steep tail restarted at `u*`
  rw [convexSegEval_split_truncSegs fs r fsegs f0 h1, ← hus,
    convexSegEval_split_truncSegs fs r fsegs f0 (le_trans h1 h12), ← hus]
  have hdrop : ∀ seg ∈ dropSegs r fsegs, r ≤ seg.1 := dropSegs_slope_ge fsegs hfsort
  have hrate := convexSegEval_rate fs r (dropSegs r fsegs) hdrop hrf
    (convexSegEval f0 fs fsegs us) (t₁ - us) (t₂ - t₁)
  -- `(t₁ − u*) + (t₂ − t₁) = t₂ − u*` since `u* ≤ t₁ ≤ t₂`
  have hsum : (t₁ - us) + (t₂ - t₁) = t₂ - us := by
    rw [add_comm, tsub_add_tsub_cancel h12 h1]
  rwa [hsum] at hrate

/-! ## Single-crossing structure of the Theorem 4.2 meet

`minConv_tbEReal_convexSegEval_eq` writes `f ∗ γ_{r,b} t = f(t) ⊓ (f(u*) + b + r·(t − u*))`. The
growth lemma turns the comparison "`f(t)` vs the line" into a *single switch*: the line is the
slower-growing branch beyond `u*`, so once `f` overtakes it (the meet returns the line) it stays
overtaken — the "`line ≤ f`" times form an up-set, equivalently "`f ≤ line`" times a down-set. -/

/-- The line continuation `c(t) = f(u*) + b + r·(t − u*)` and `f` are pinned at the breakpoint:
`f u* ≤ c u*` (the line starts `b` above `f`). Below `u*`, by monotonicity `f t ≤ f u* ≤ c u*`, but
`c` is the *line through `u*`*; the down-set claim below concerns `t ≥ u*` where `c` is honest. -/
theorem convexSegEval_le_lineCont_at_breakpoint (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0)) :
    convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs))
      ≤ convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
          + r * (segLenSum (truncSegs r fsegs) - segLenSum (truncSegs r fsegs)) := by
  rw [tsub_self, mul_zero, add_zero]; exact le_self_add

/-- **The crossing is a single switch (down-set form).** Define the line continuation
`c(t) = f(u*) + b + r·(t − u*)`. Beyond `u*`, the set of times where `f` stays under the line,
`{t | u* ≤ t ∧ f t ≤ c t}`, is downward closed: if `f t₂ ≤ c t₂` and `u* ≤ t₁ ≤ t₂` then
`f t₁ ≤ c t₁`. (Because beyond `u*` both grow but `f`'s rate `≥ r = c`'s rate, the gap `c − f` is
nonincreasing, so once `f` catches up to `c` it stays caught up — there is at most one crossing.) -/
theorem convexSegEval_le_lineCont_downset (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs) (hrf : r ≤ fs)
    {t₁ t₂ : ℝ≥0} (h1 : segLenSum (truncSegs r fsegs) ≤ t₁) (h12 : t₁ ≤ t₂)
    (h2 : convexSegEval f0 fs fsegs t₂
        ≤ convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t₂ - segLenSum (truncSegs r fsegs))) :
    convexSegEval f0 fs fsegs t₁
      ≤ convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
          + r * (t₁ - segLenSum (truncSegs r fsegs)) := by
  set us := segLenSum (truncSegs r fsegs) with hus
  set fu := convexSegEval f0 fs fsegs us with hfu
  -- from `t₁` to `t₂`, `f` grows by at least `r·(t₂ − t₁)` (growth past the breakpoint)
  have hgrow : convexSegEval f0 fs fsegs t₁ + r * (t₂ - t₁) ≤ convexSegEval f0 fs fsegs t₂ :=
    convexSegEval_rate_from_breakpoint f0 fs r fsegs hfsort hrf h1 h12
  -- the line splits additively: `c t₂ = c t₁ + r·(t₂ − t₁)`
  have hsum : t₂ - us = (t₁ - us) + (t₂ - t₁) := by
    rw [add_comm]; exact (tsub_add_tsub_cancel h12 h1).symm
  have hline : fu + b + r * (t₂ - us) = (fu + b + r * (t₁ - us)) + r * (t₂ - t₁) := by
    rw [hsum, mul_add]; ring
  -- chain: `f t₁ + r·(t₂−t₁) ≤ f t₂ ≤ c t₂ = c t₁ + r·(t₂−t₁)`, then cancel
  rw [← add_le_add_iff_right (r * (t₂ - t₁))]
  calc convexSegEval f0 fs fsegs t₁ + r * (t₂ - t₁)
      ≤ convexSegEval f0 fs fsegs t₂ := hgrow
    _ ≤ fu + b + r * (t₂ - us) := h2
    _ = (fu + b + r * (t₁ - us)) + r * (t₂ - t₁) := hline

/-! ## The two regimes of the Theorem 4.2 meet, resolved -/

/-- **Theorem 4.2, `f`-wins regime.** Where the curve stays under the line continuation
(`f t ≤ f(u*) + b + r·(t − u*)`), the token-bucket convolution is `f` itself:
`f ∗ γ_{r,b} t = f(t)`. (Resolves the meet `minConv_tbEReal_convexSegEval_eq` via `inf_of_le_left`.) -/
theorem minConv_tbEReal_convexSegEval_eq_f (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs) {t : ℝ≥0}
    (h : convexSegEval f0 fs fsegs t
        ≤ convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs))) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_tbEReal_convexSegEval_eq f0 fs r b fsegs hfsort hfs hrf, inf_of_le_left]
  exact_mod_cast h

/-- **Theorem 4.2, `line`-wins regime.** Where the line continuation has fallen under the curve
(`f(u*) + b + r·(t − u*) ≤ f t`, i.e. the token bucket is the binding constraint), the convolution
runs at the bucket's rate: `f ∗ γ_{r,b} t = f(u*) + b + r·(t − u*)`. (Resolves the meet via
`inf_of_le_right`.) -/
theorem minConv_tbEReal_convexSegEval_eq_line (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs) {t : ℝ≥0}
    (h : convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs))
        ≤ convexSegEval f0 fs fsegs t) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_tbEReal_convexSegEval_eq f0 fs r b fsegs hfsort hfs hrf, inf_of_le_right]
  exact_mod_cast h

/-- Faithfulness: the primary goal verbatim — minimum growth rate `r` beyond the breakpoint
`u* = segLenSum (truncSegs r fsegs)`, for `r ≤ fs` and slope-sorted `fsegs`. -/
example (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t) :
    convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs))
        + r * (t - segLenSum (truncSegs r fsegs))
      ≤ convexSegEval f0 fs fsegs t :=
  convexSegEval_rate_past_breakpoint f0 fs r fsegs hfsort hrf ht

/-- Faithfulness: the split decomposition recovers the corner value at `t = u*` (the tail term
`dropSegs` evaluated at `0` is the base `f u*`). -/
example (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0)) :
    convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs))
      = convexSegEval (convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs))) fs
          (dropSegs r fsegs) 0 := by
  rw [convexSegEval_zero]

/-- Faithfulness: `dropSegs r fsegs` for an empty list is empty, so the split is trivial. -/
example (f0 fs r : ℝ≥0) (t : ℝ≥0) :
    convexSegEval f0 fs [] t
      = convexSegEval (convexSegEval f0 fs [] (segLenSum (truncSegs r ([] : List (ℝ≥0 × ℝ≥0))))) fs
          (dropSegs r []) (t - segLenSum (truncSegs r ([] : List (ℝ≥0 × ℝ≥0)))) := by
  apply convexSegEval_split_truncSegs fs r [] f0
  simp

end DeepWiki
