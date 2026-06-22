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

/-- **Truncation decomposition.** The truncated curve `Gt = convexSegEval g0 sf (truncSegs sf gsegs)`
agrees with the original `G = convexSegEval g0 sg gsegs` up to the cut point and then continues at
slope `sf`: for every `v` there is a `w ≤ v` (the matching point, `min v cutLen`) with
`Gt v = G w + sf·(v − w)`. This is the exact structural fact that lets us slide the convolution's
excess `g`-mass past the cut onto a flatter `f`. -/
theorem convexSegEval_truncSegs_decomp (sf sg : ℝ≥0) :
    ∀ (gsegs : List (ℝ≥0 × ℝ≥0)) (g0 v : ℝ≥0), ∃ w : ℝ≥0, w ≤ v ∧
      convexSegEval g0 sf (truncSegs sf gsegs) v
        = convexSegEval g0 sg gsegs w + sf * (v - w) := by
  intro gsegs
  induction gsegs with
  | nil =>
      intro g0 v
      refine ⟨0, zero_le, ?_⟩
      rw [truncSegs_nil, convexSegEval_nil, convexSegEval_nil, tsub_zero, mul_zero, add_zero]
  | cons hd tl ih =>
      intro g0 v
      obtain ⟨sb, ℓb⟩ := hd
      by_cases hsb : sb ≤ sf
      · -- segment kept; split on whether `v` is on it
        rw [truncSegs_cons_le hsb]
        by_cases hv : v ≤ ℓb
        · -- on the leading segment: `Gt v = G v`, witness `w = v`
          refine ⟨v, le_rfl, ?_⟩
          rw [convexSegEval_cons, if_pos hv, convexSegEval_cons, if_pos hv, tsub_self, mul_zero,
            add_zero]
        · -- past the leading segment: peel and use IH on the tail
          have hℓbv : ℓb ≤ v := (not_le.mp hv).le
          rw [convexSegEval_cons, if_neg hv]
          obtain ⟨w', hw'le, hw'eq⟩ := ih (g0 + sb * ℓb) (v - ℓb)
          refine ⟨ℓb + w', ?_, ?_⟩
          · -- `ℓb + w' ≤ v`
            calc ℓb + w' ≤ ℓb + (v - ℓb) := by gcongr
              _ = v := add_tsub_cancel_of_le hℓbv
          · -- `Gt v = G (ℓb + w') + sf·(v - (ℓb + w'))`
            rw [hw'eq, ← convexSegEval_cons_peel g0 sg sb ℓb w' tl]
            congr 2
            rw [tsub_add_eq_tsub_tsub]
      · -- segment dropped (and all after, by sorting): `Gt v = g0 + sf·v`, witness `w = 0`
        rw [truncSegs_cons_gt hsb]
        refine ⟨0, zero_le, ?_⟩
        rw [convexSegEval_nil, convexSegEval_zero, tsub_zero]

/-- **Truncation lowers the curve.** The truncated curve `convexSegEval g0 sf (truncSegs sf gsegs)`
is pointwise `≤` the original `convexSegEval g0 sg gsegs` (for `sf ≤ sg`, slope-sorted `gsegs` with
slopes `≤ sg`): below the cut they agree; beyond it the truncated curve runs at the flatter slope
`sf` while the original keeps its steeper segments. -/
theorem convexSegEval_truncSegs_le (sf sg : ℝ≥0) (hsfg : sf ≤ sg) :
    ∀ (gsegs : List (ℝ≥0 × ℝ≥0)), List.Pairwise (fun a b => a.1 ≤ b.1) gsegs →
      (∀ seg ∈ gsegs, seg.1 ≤ sg) → ∀ g0 v : ℝ≥0,
      convexSegEval g0 sf (truncSegs sf gsegs) v ≤ convexSegEval g0 sg gsegs v := by
  intro gsegs
  induction gsegs with
  | nil =>
      intro _ _ g0 v
      rw [truncSegs_nil, convexSegEval_nil, convexSegEval_nil]
      gcongr
  | cons hd tl ih =>
      intro hsort hle g0 v
      obtain ⟨sb, ℓb⟩ := hd
      have htl_sort : List.Pairwise (fun a b => a.1 ≤ b.1) tl := (List.pairwise_cons.mp hsort).2
      have htl_le : ∀ seg ∈ tl, seg.1 ≤ sg := fun seg h => hle seg (List.mem_cons_of_mem _ h)
      by_cases hsb : sb ≤ sf
      · -- segment kept
        rw [truncSegs_cons_le hsb]
        by_cases hv : v ≤ ℓb
        · rw [convexSegEval_cons, if_pos hv, convexSegEval_cons, if_pos hv]
        · rw [convexSegEval_cons, if_neg hv, convexSegEval_cons, if_neg hv]
          exact ih htl_sort htl_le (g0 + sb * ℓb) (v - ℓb)
      · -- segment dropped: `Gt v = g0 + sf·v`; sortedness ⟹ all remaining slopes `≥ sb > sf`
        rw [truncSegs_cons_gt hsb, convexSegEval_nil]
        have hsfb : sf ≤ sb := (not_le.mp hsb).le
        have hall : ∀ seg ∈ (sb, ℓb) :: tl, sf ≤ seg.1 :=
          sorted_head_le_all hsort rfl hsfb
        have := convexSegEval_lower sg sf ((sb, ℓb) :: tl) hall hsfg g0 v
        simpa using this

/-- **Convolution ignores `g`'s steep part.** For `sf ≤ sg`, slope-sorted `fsegs` (all slopes `≤ sf`)
and `gsegs` (all slopes `≤ sg`), convolving the flatter-asymptote `F = convexSegEval f0 sf fsegs`
with `G = convexSegEval g0 sg gsegs` is the same as convolving it with the **truncated**
`Gt = convexSegEval g0 sf (truncSegs sf gsegs)` (asymptote lowered to `sf`, steep segments dropped):
the `(min,plus)` convolution never uses `g`'s segments steeper than `sf`. -/
theorem minConv_convexSegEval_truncSegs (sf sg f0 g0 : ℝ≥0)
    (fsegs gsegs : List (ℝ≥0 × ℝ≥0)) (hsfg : sf ≤ sg)
    (hgsort : List.Pairwise (fun a b => a.1 ≤ b.1) gsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ sf) (hgs : ∀ seg ∈ gsegs, seg.1 ≤ sg) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval f0 sf fsegs u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval g0 sg gsegs v : ℝ≥0) : ℝ) : EReal)) t
      = minConv (fun u => (((convexSegEval f0 sf fsegs u : ℝ≥0) : ℝ) : EReal))
                (fun v => (((convexSegEval g0 sf (truncSegs sf gsegs) v : ℝ≥0) : ℝ) : EReal)) t := by
  have coeadd : ∀ x y : ℝ≥0,
      (((x : ℝ) : EReal)) + (((y : ℝ) : EReal)) = (((x + y : ℝ≥0) : ℝ) : EReal) := by
    intro x y; rw [← EReal.coe_add, ← NNReal.coe_add]
  set F : ℝ≥0 → EReal := fun u => (((convexSegEval f0 sf fsegs u : ℝ≥0) : ℝ) : EReal) with hF
  set G : ℝ≥0 → EReal := fun v => (((convexSegEval g0 sg gsegs v : ℝ≥0) : ℝ) : EReal) with hG
  set Gt : ℝ≥0 → EReal :=
    fun v => (((convexSegEval g0 sf (truncSegs sf gsegs) v : ℝ≥0) : ℝ) : EReal) with hGt
  apply le_antisymm
  · -- `minConv F G ≤ minConv F Gt`, sliding the excess `g`-mass onto the flatter `F`
    refine le_minConv (fun u v huv => ?_)
    obtain ⟨w, hwle, hweq⟩ := convexSegEval_truncSegs_decomp sf sg gsegs g0 v
    -- split `t = (u + (v - w)) + w`
    have hsplit : (u + (v - w)) + w = t := by
      rw [add_assoc, tsub_add_cancel_of_le hwle, huv]
    refine le_trans (minConv_le_add F G hsplit) ?_
    simp only [hF, hG, hGt]
    rw [coeadd, coeadd, EReal.coe_le_coe_iff, NNReal.coe_le_coe, hweq]
    -- `F (u + (v-w)) + G w ≤ F u + (G w + sf·(v-w))` via the upper-rate of `F`
    have hFr : convexSegEval f0 sf fsegs (u + (v - w))
        ≤ convexSegEval f0 sf fsegs u + sf * (v - w) :=
      convexSegEval_upper_rate_of_le hfs u (v - w)
    calc convexSegEval f0 sf fsegs (u + (v - w)) + convexSegEval g0 sg gsegs w
        ≤ (convexSegEval f0 sf fsegs u + sf * (v - w)) + convexSegEval g0 sg gsegs w := by gcongr
      _ = convexSegEval f0 sf fsegs u + (convexSegEval g0 sg gsegs w + sf * (v - w)) := by ring
  · -- `minConv F Gt ≤ minConv F G`, via `Gt ≤ G` pointwise
    refine le_minConv (fun u v huv => ?_)
    refine le_trans (minConv_le_add F Gt huv) ?_
    simp only [hF, hG, hGt]
    rw [coeadd, coeadd, EReal.coe_le_coe_iff, NNReal.coe_le_coe]
    have hGt_le : convexSegEval g0 sf (truncSegs sf gsegs) v ≤ convexSegEval g0 sg gsegs v :=
      convexSegEval_truncSegs_le sf sg hsfg gsegs hgsort hgs g0 v
    exact add_le_add le_rfl hGt_le

/-- **Theorem 4.1, the unbalanced case** (different asymptotic slopes, `sf ≤ sg`). The `(min,plus)`
convolution of two convex PWLs with the flatter asymptote `sf` is the slope-merge from `f(0)+g(0)`
of `f`'s segments with `g`'s segments **truncated at slope `sf`** — every segment of `g` steeper
than `sf` is absorbed into the (flatter) asymptote `sf`. (Since `fsegs` already has all slopes `≤ sf`
it needs no truncation; only `g` is cut.) Proved by reducing to the balanced case
(`minConv_convexSegEval_eq_merge`) through `minConv_convexSegEval_truncSegs`. -/
theorem minConv_convexSegEval_unbalanced (sf sg f0 g0 : ℝ≥0)
    (fsegs gsegs : List (ℝ≥0 × ℝ≥0)) (hsfg : sf ≤ sg)
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hgsort : List.Pairwise (fun a b => a.1 ≤ b.1) gsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ sf) (hgs : ∀ seg ∈ gsegs, seg.1 ≤ sg) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval f0 sf fsegs u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval g0 sg gsegs v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval (f0 + g0) sf (mergeBySlope fsegs (truncSegs sf gsegs)) t : ℝ≥0)
            : ℝ) : EReal) := by
  rw [minConv_convexSegEval_truncSegs sf sg f0 g0 fsegs gsegs hsfg hgsort hfs hgs t]
  exact minConv_convexSegEval_eq_merge sf f0 g0 fsegs (truncSegs sf gsegs) hfsort
    (truncSegs_sorted hgsort) hfs (truncSegs_slope_le gsegs) t

/-- Faithfulness check: when `g` is already balanced (all its slopes `≤ sf = sg`), truncation is a
no-op (`truncSegs_eq_self`) and the unbalanced theorem collapses back onto the balanced merge. -/
example (s f0 g0 : ℝ≥0) (fsegs gsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a b => a.1 ≤ b.1) fsegs)
    (hgsort : List.Pairwise (fun a b => a.1 ≤ b.1) gsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ s) (hgs : ∀ seg ∈ gsegs, seg.1 ≤ s) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval f0 s fsegs u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval g0 s gsegs v : ℝ≥0) : ℝ) : EReal)) t
      = (((convexSegEval (f0 + g0) s (mergeBySlope fsegs gsegs) t : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_convexSegEval_unbalanced s s f0 g0 fsegs gsegs le_rfl hfsort hgsort hfs hgs t,
    truncSegs_eq_self hgs]

/-- Faithfulness check: a flat line `u ↦ a + sf·u` (no finite segments, asymptote `sf`) convolved
with a convex PWL `g` *all of whose slopes are steeper than `sf`* (so `g` is truncated to nothing)
absorbs all of `g`'s segments — the result is the line shifted by `g(0)`, recovering
`minConv_flatLine_convexSegEval` from the unbalanced theorem. -/
example (a sf sg g0 : ℝ≥0) (gsegs : List (ℝ≥0 × ℝ≥0)) (hsfg : sf ≤ sg)
    (hgsort : List.Pairwise (fun a b => a.1 ≤ b.1) gsegs)
    (hgs : ∀ seg ∈ gsegs, seg.1 ≤ sg) (hgsteep : ∀ seg ∈ gsegs, sf ≤ seg.1)
    (hgne : ∀ seg ∈ gsegs, sf ≠ seg.1) (t : ℝ≥0) :
    minConv (fun u => (((convexSegEval a sf [] u : ℝ≥0) : ℝ) : EReal))
            (fun v => (((convexSegEval g0 sg gsegs v : ℝ≥0) : ℝ) : EReal)) t
      = (((a + g0 + sf * t : ℝ≥0) : ℝ) : EReal) := by
  have htrunc : truncSegs sf gsegs = [] := by
    cases gsegs with
    | nil => rfl
    | cons hd tl =>
        obtain ⟨sb, ℓb⟩ := hd
        have : sf < sb :=
          lt_of_le_of_ne (hgsteep (sb, ℓb) List.mem_cons_self) (hgne (sb, ℓb) List.mem_cons_self)
        exact truncSegs_cons_gt (not_le.mpr this) tl
  rw [minConv_convexSegEval_unbalanced sf sg a g0 [] gsegs hsfg List.Pairwise.nil hgsort
    (by simp) hgs t, htrunc, mergeBySlope_nil_left, convexSegEval_nil]

end DeepWiki
