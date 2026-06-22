import DeepWiki.NetworkCalculus.ConvexConcaveCrossingPoint

/-! # The explicit crossing coordinate `u**` of the Theorem 4.2 token-bucket switch (§4.2.2)
`ConvexConcaveCrossingPoint` characterizes `f ∗ γ_{r,b}` as a *single switch* past the breakpoint
`u* = segLenSum (truncSegs r fsegs)`: `f` on an initial interval, the line `f(u*)+b+r·(t−u*)` on a
final one. This file makes *where* the switch happens explicit.

The driver is the **excess** `E(d) := f(u*+d) − f(u*) − r·d` (ℝ≥0, an honest difference because
`convexSegEval_rate_past_breakpoint` gives `f(u*)+r·d ≤ f(u*+d)`). It is `0` at `d = 0` and
nondecreasing in `d`. The crossing is the first offset `d*` with `E(d*) = b`; then `u** = u* + d*`
and `f ∗ γ_{r,b} t = f t` for `u* ≤ t ≤ u**`, `= line t` for `t ≥ u**`.

This file delivers:
* **(1)** `excess` with its additive characterization (`excess_add_eq`), base value (`excess_zero`),
  monotonicity (`excess_mono`), and the bridge `lineCont_le_iff_b_le_excess` /
  `le_lineCont_iff_excess_le_b` rewriting "line vs `f`" as "`b` vs `E(d)`".
* **(2)** the **single-steep-segment tail** crossing offset: when `dropSegs r fsegs = [(s, ℓ)]`
  (one steep segment then the asymptote `fs`), the excess is the explicit ramp `(s−r)·d` on `[0, ℓ]`,
  saturating to `(fs−r)·d` beyond — so the crossing offset solves `(s−r)·δ = b` inside that segment
  (`excess_singleTail_eq`, `crossingOffset_singleTail`).
* **(3)** the explicit piecewise value at `u** = u* + d*` off `excess … d* = b`
  (`minConv_tbEReal_eq_f_of_excess_le` / `…_eq_line_of_le_excess`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## (1) The excess function `E(d) = f(u*+d) − f(u*) − r·d` -/

/-- The **excess** past the breakpoint: `E(d) = f(u*+d) − (f(u*) + r·d)` in `ℝ≥0` (truncated `-`),
with `u* = segLenSum (truncSegs r fsegs)`. It measures how far the curve `f` has pulled ahead of the
rate-`r` line by offset `d`; the crossing of Theorem 4.2 is the first `d` with `E(d) = b`. -/
noncomputable def excess (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0)) (d : ℝ≥0) : ℝ≥0 :=
  convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs) + d)
    - (convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + r * d)

/-- **Additive characterization of the excess.** Because `f(u*) + r·d ≤ f(u*+d)` past the breakpoint
(`convexSegEval_rate_past_breakpoint`), the truncated difference is honest:
`E(d) + (f(u*) + r·d) = f(u*+d)`. This is the workhorse — every other excess fact is `add`-cancellation
off it. -/
theorem excess_add_eq (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs) (d : ℝ≥0) :
    excess f0 fs r fsegs d
        + (convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + r * d)
      = convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs) + d) := by
  rw [excess]
  refine tsub_add_cancel_of_le ?_
  -- `convexSegEval_rate_past_breakpoint` at `t = u* + d`, where `t − u* = d`
  have h := convexSegEval_rate_past_breakpoint f0 fs r fsegs hfsort hrf
    (t := segLenSum (truncSegs r fsegs) + d) le_self_add
  rwa [add_tsub_cancel_left] at h

/-- The excess vanishes at the breakpoint: `E(0) = 0` (`f(u*) − f(u*) = 0`). -/
@[simp] theorem excess_zero (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0)) :
    excess f0 fs r fsegs 0 = 0 := by
  rw [excess, add_zero, mul_zero, add_zero, tsub_self]

/-- **The excess is nondecreasing.** For `d₁ ≤ d₂`, `E(d₁) ≤ E(d₂)`: past the breakpoint the curve
grows at rate `≥ r` (`convexSegEval_rate_from_breakpoint`), so the gap to the rate-`r` line only
widens. -/
theorem excess_mono (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs) :
    Monotone (excess f0 fs r fsegs) := by
  intro d₁ d₂ h
  set us := segLenSum (truncSegs r fsegs) with hus
  set fu := convexSegEval f0 fs fsegs us with hfu
  -- cancel the common `(fu + r·d₁)` after padding both excesses to the same base
  have e1 := excess_add_eq f0 fs r fsegs hfsort hrf d₁
  have e2 := excess_add_eq f0 fs r fsegs hfsort hrf d₂
  rw [← hus, ← hfu] at e1 e2
  -- `E(d₁) + (fu + r·d₁) = f(u*+d₁)`, `E(d₂) + (fu + r·d₂) = f(u*+d₂)`
  -- the curve grows by `≥ r·(d₂−d₁)` from `u*+d₁` to `u*+d₂`
  have hgrow0 := convexSegEval_rate_from_breakpoint f0 fs r fsegs hfsort hrf
    (t₁ := us + d₁) (t₂ := us + d₂) le_self_add (by gcongr)
  rw [add_tsub_add_eq_tsub_left us d₂ d₁] at hgrow0
  have hgrow : convexSegEval f0 fs fsegs (us + d₁) + r * (d₂ - d₁)
      ≤ convexSegEval f0 fs fsegs (us + d₂) := hgrow0
  -- combine and cancel `(fu + r·d₂)`
  rw [← add_le_add_iff_right (fu + r * d₂)]
  calc excess f0 fs r fsegs d₁ + (fu + r * d₂)
      = (excess f0 fs r fsegs d₁ + (fu + r * d₁)) + r * (d₂ - d₁) := by
        rw [show r * d₂ = r * d₁ + r * (d₂ - d₁) from by
          rw [← mul_add, add_tsub_cancel_of_le h]]; ring
    _ = convexSegEval f0 fs fsegs (us + d₁) + r * (d₂ - d₁) := by rw [e1]
    _ ≤ convexSegEval f0 fs fsegs (us + d₂) := hgrow
    _ = excess f0 fs r fsegs d₂ + (fu + r * d₂) := e2.symm

/-- **`line ≤ f` iff `b ≤ E(t − u*)` past the breakpoint.** Rewrites the binding test of Theorem 4.2
at `t ≥ u*`: the line continuation has fallen under the curve exactly when the burst `b` is at most
the excess accumulated by offset `t − u*`. -/
theorem lineCont_le_iff_b_le_excess (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t) :
    lineCont f0 fs r b fsegs t ≤ convexSegEval f0 fs fsegs t
      ↔ b ≤ excess f0 fs r fsegs (t - segLenSum (truncSegs r fsegs)) := by
  set us := segLenSum (truncSegs r fsegs) with hus
  set d := t - us with hd
  have htd : us + d = t := add_tsub_cancel_of_le ht
  rw [lineCont_apply, ← hus, ← hd]
  have e := excess_add_eq f0 fs r fsegs hfsort hrf d
  rw [← hus] at e
  -- both sides compare `f(u*) + b + r·d` with `f(u*+d) = E(d) + (f(u*) + r·d)`
  rw [← htd, ← e]
  constructor
  · intro h
    -- `f(u*) + b + r·d ≤ E(d) + (f(u*) + r·d)`  ⟹  `b ≤ E(d)`
    rw [← add_le_add_iff_right (convexSegEval f0 fs fsegs us + r * d)]
    calc b + (convexSegEval f0 fs fsegs us + r * d)
        = convexSegEval f0 fs fsegs us + b + r * d := by ring
      _ ≤ excess f0 fs r fsegs d + (convexSegEval f0 fs fsegs us + r * d) := h
  · intro h
    calc convexSegEval f0 fs fsegs us + b + r * d
        = b + (convexSegEval f0 fs fsegs us + r * d) := by ring
      _ ≤ excess f0 fs r fsegs d + (convexSegEval f0 fs fsegs us + r * d) := by gcongr

/-- **`f ≤ line` iff `E(t − u*) ≤ b` past the breakpoint.** The slack-test dual of
`lineCont_le_iff_b_le_excess`: the curve stays under the line exactly when the excess at offset
`t − u*` has not yet reached the burst `b`. -/
theorem le_lineCont_iff_excess_le_b (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t) :
    convexSegEval f0 fs fsegs t ≤ lineCont f0 fs r b fsegs t
      ↔ excess f0 fs r fsegs (t - segLenSum (truncSegs r fsegs)) ≤ b := by
  set us := segLenSum (truncSegs r fsegs) with hus
  set d := t - us with hd
  have htd : us + d = t := add_tsub_cancel_of_le ht
  rw [lineCont_apply, ← hus, ← hd]
  have e := excess_add_eq f0 fs r fsegs hfsort hrf d
  rw [← hus] at e
  rw [← htd, ← e]
  constructor
  · intro h
    rw [← add_le_add_iff_right (convexSegEval f0 fs fsegs us + r * d)]
    calc excess f0 fs r fsegs d + (convexSegEval f0 fs fsegs us + r * d)
        ≤ convexSegEval f0 fs fsegs us + b + r * d := h
      _ = b + (convexSegEval f0 fs fsegs us + r * d) := by ring
  · intro h
    calc excess f0 fs r fsegs d + (convexSegEval f0 fs fsegs us + r * d)
        ≤ b + (convexSegEval f0 fs fsegs us + r * d) := by gcongr
      _ = convexSegEval f0 fs fsegs us + b + r * d := by ring

/-! ## (2) The excess over a single-steep-segment tail

When `dropSegs r fsegs = [(s, ℓ)]` — one steep segment of slope `s > r`, then the asymptote `fs` —
the excess is the explicit ramp `(s − r)·d` for `d ≤ ℓ`, then `(s − r)·ℓ + (fs − r)·(d − ℓ)` beyond
(`fs ≥ r` keeps it nondecreasing). The crossing offset solves `(s − r)·δ = b` inside the segment,
when `b ≤ (s − r)·ℓ`; otherwise saturation continues on the asymptote. -/

/-- On the first steep segment, `f` past `u*` reads `f(u*) + s·d` (`d ≤ ℓ`), so the excess is the
explicit ramp `E(d) = (s − r)·d`. (Uses `convexSegEval_split_truncSegs` to restart the dropped tail
at `u*`, then the leading-segment branch of `convexSegEval_cons`.) -/
theorem excess_singleTail_on_seg (f0 fs r s ℓ : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    (htail : dropSegs r fsegs = (s, ℓ) :: [])
    {d : ℝ≥0} (hd : d ≤ ℓ) :
    excess f0 fs r fsegs d = (s - r) * d := by
  set us := segLenSum (truncSegs r fsegs) with hus
  set fu := convexSegEval f0 fs fsegs us with hfu
  -- the steep segment has slope `s ≥ r` (it survived `dropSegs`)
  have hrs : r ≤ s := by
    have hmem : (s, ℓ) ∈ dropSegs r fsegs := by rw [htail]; exact List.mem_cons_self
    exact dropSegs_slope_ge (s := r) fsegs hfsort (s, ℓ) hmem
  -- evaluate `f(u*+d)` via the split: the tail `[(s,ℓ)]` restarted at `u*`, on its first segment
  have hsplit := convexSegEval_split_truncSegs fs r fsegs f0
    (t := us + d) (by rw [← hus]; exact le_self_add)
  rw [← hus, ← hfu, add_tsub_cancel_left, htail, convexSegEval_cons, if_pos hd] at hsplit
  -- `E(d) + (fu + r·d) = f(u*+d) = fu + s·d`, then cancel and read off `(s−r)·d`
  have e := excess_add_eq f0 fs r fsegs hfsort hrf d
  rw [← hus, ← hfu, hsplit] at e
  -- e : E(d) + (fu + r·d) = fu + s·d
  have hsr : s * d = (s - r) * d + r * d := by
    rw [← add_mul, tsub_add_cancel_of_le hrs]
  -- solve E(d) = (s−r)·d by cancelling `(fu + r·d)`
  have hcancel : excess f0 fs r fsegs d + (fu + r * d) = (s - r) * d + (fu + r * d) := by
    rw [e, hsr]; ring
  exact add_right_cancel hcancel

/-- **Total excess of the single steep segment.** At `d = ℓ` (the segment's far end), the excess is
`E(ℓ) = (s − r)·ℓ` — the most the segment alone can contribute toward the burst `b`. Beyond it the
asymptote (slope `fs ≥ r`) keeps adding `(fs − r)` per unit, so `(s − r)·ℓ` is the threshold deciding
whether the crossing lands inside the segment. -/
theorem excess_singleTail_at_end (f0 fs r s ℓ : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    (htail : dropSegs r fsegs = (s, ℓ) :: []) :
    excess f0 fs r fsegs ℓ = (s - r) * ℓ :=
  excess_singleTail_on_seg f0 fs r s ℓ fsegs hfsort hrf htail le_rfl

/-- **The crossing offset inside the single steep segment.** With `dropSegs r fsegs = [(s, ℓ)]` and a
reachable burst `b ≤ (s − r)·ℓ` (`r < s`, so `s − r ≠ 0`), the offset `δ := b / (s − r)` lands inside
the segment (`δ ≤ ℓ`) and hits the burst exactly: `E(δ) = b`. (ℝ≥0 division is exact here:
`(s − r)·(b / (s − r)) = b` because `s − r ≠ 0`.) -/
noncomputable def crossingOffset_singleTail (r s b : ℝ≥0) : ℝ≥0 := b / (s - r)

/-- `crossingOffset_singleTail` stays inside the steep segment: `δ ≤ ℓ` when `b ≤ (s − r)·ℓ`. -/
theorem crossingOffset_singleTail_le (r s b ℓ : ℝ≥0) (hrs : r < s) (hb : b ≤ (s - r) * ℓ) :
    crossingOffset_singleTail r s b ≤ ℓ := by
  rw [crossingOffset_singleTail, div_le_iff₀ (tsub_pos_of_lt hrs), mul_comm]
  exact hb

/-- **The single-tail crossing hits the burst.** `E(δ) = b` at `δ = b / (s − r)`, when
`dropSegs r fsegs = [(s, ℓ)]`, `r < s`, and `b ≤ (s − r)·ℓ` (reachable inside the segment). -/
theorem excess_singleTail_crossingOffset (f0 fs r s ℓ b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    (htail : dropSegs r fsegs = (s, ℓ) :: []) (hrs : r < s) (hb : b ≤ (s - r) * ℓ) :
    excess f0 fs r fsegs (crossingOffset_singleTail r s b) = b := by
  rw [excess_singleTail_on_seg f0 fs r s ℓ fsegs hfsort hrf htail
        (crossingOffset_singleTail_le r s b ℓ hrs hb),
    crossingOffset_singleTail, mul_div_cancel₀]
  exact (tsub_pos_of_lt hrs).ne'

/-! ## (3) The explicit piecewise value at the crossing `u** = u* + d*` -/

/-- **Slack regime via the excess.** Where the excess at `t − u*` has not reached the burst
(`E(t − u*) ≤ b`, `t ≥ u*`), the bucket convolution is `f`: `f ∗ γ_{r,b} t = f t`. (Restates
`minConv_tbEReal_convexSegEval_eq_f` through `le_lineCont_iff_excess_le_b`.) -/
theorem minConv_tbEReal_eq_f_of_excess_le (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t)
    (hexc : excess f0 fs r fsegs (t - segLenSum (truncSegs r fsegs)) ≤ b) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) := by
  apply minConv_tbEReal_convexSegEval_eq_f f0 fs r b fsegs hfsort hfs hrf
  have h := (le_lineCont_iff_excess_le_b f0 fs r b fsegs hfsort hrf ht).mpr hexc
  rwa [lineCont_apply] at h

/-- **Binding regime via the excess.** Where the excess at `t − u*` has reached the burst
(`b ≤ E(t − u*)`, `t ≥ u*`), the bucket binds: `f ∗ γ_{r,b} t = f(u*) + b + r·(t − u*)`. (Restates
`minConv_tbEReal_convexSegEval_eq_line` through `lineCont_le_iff_b_le_excess`.) -/
theorem minConv_tbEReal_eq_line_of_le_excess (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t)
    (hexc : b ≤ excess f0 fs r fsegs (t - segLenSum (truncSegs r fsegs))) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal) := by
  apply minConv_tbEReal_convexSegEval_eq_line f0 fs r b fsegs hfsort hfs hrf
  have h := (lineCont_le_iff_b_le_excess f0 fs r b fsegs hfsort hrf ht).mpr hexc
  rwa [lineCont_apply] at h

/-- **The explicit crossing value, slack side.** With the single-steep-segment tail
`dropSegs r fsegs = [(s, ℓ)]`, `r < s`, reachable `b ≤ (s − r)·ℓ`, and `u** = u* + b/(s−r)`: for
`u* ≤ t ≤ u**` the convolution is `f` itself. The threshold `u**` is *explicit* — its offset is
`b / (s − r)`. -/
theorem minConv_tbEReal_eq_f_below_crossing (f0 fs r s ℓ b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    (htail : dropSegs r fsegs = (s, ℓ) :: []) (hrs : r < s) (hb : b ≤ (s - r) * ℓ)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t)
    (htu : t ≤ segLenSum (truncSegs r fsegs) + crossingOffset_singleTail r s b) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) := by
  apply minConv_tbEReal_eq_f_of_excess_le f0 fs r b fsegs hfsort hfs hrf ht
  -- `t − u* ≤ δ ≤ ℓ`, so `E(t − u*) = (s−r)·(t−u*) ≤ (s−r)·δ = b`
  set us := segLenSum (truncSegs r fsegs) with hus
  have hdℓ : t - us ≤ ℓ := by
    refine le_trans (tsub_le_iff_left.mpr ?_) (crossingOffset_singleTail_le r s b ℓ hrs hb)
    rwa [hus] at htu
  rw [excess_singleTail_on_seg f0 fs r s ℓ fsegs hfsort hrf htail hdℓ]
  calc (s - r) * (t - us) ≤ (s - r) * crossingOffset_singleTail r s b := by
        gcongr
        rw [hus] at htu
        exact tsub_le_iff_left.mpr htu
    _ = b := by
        rw [crossingOffset_singleTail, mul_div_cancel₀]
        exact (tsub_pos_of_lt hrs).ne'

/-- **The explicit crossing value, binding side.** With `dropSegs r fsegs = [(s, ℓ)]`, `r < s`,
reachable `b ≤ (s − r)·ℓ`, and `u** = u* + b/(s−r)`: for `t ≥ u**` the bucket binds and
`f ∗ γ_{r,b} t = f(u*) + b + r·(t − u*)`. Together with `minConv_tbEReal_eq_f_below_crossing` this is
Theorem 4.2 with the switch coordinate `u**` written out. -/
theorem minConv_tbEReal_eq_line_above_crossing (f0 fs r s ℓ b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    (htail : dropSegs r fsegs = (s, ℓ) :: []) (hrs : r < s) (hb : b ≤ (s - r) * ℓ)
    {t : ℝ≥0} (htu : segLenSum (truncSegs r fsegs) + crossingOffset_singleTail r s b ≤ t) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal) := by
  set us := segLenSum (truncSegs r fsegs) with hus
  have ht : us ≤ t := le_trans le_self_add htu
  apply minConv_tbEReal_eq_line_of_le_excess f0 fs r b fsegs hfsort hfs hrf ht
  -- `b = E(δ) ≤ E(t − u*)` by monotonicity, since `δ ≤ t − u*`
  have hδle : crossingOffset_singleTail r s b ≤ t - us := by
    rw [le_tsub_iff_left ht]
    calc us + crossingOffset_singleTail r s b
        = segLenSum (truncSegs r fsegs) + crossingOffset_singleTail r s b := by rw [hus]
      _ ≤ t := htu
  have hcross := excess_singleTail_crossingOffset f0 fs r s ℓ b fsegs hfsort hrf htail hrs hb
  calc b = excess f0 fs r fsegs (crossingOffset_singleTail r s b) := hcross.symm
    _ ≤ excess f0 fs r fsegs (t - us) := excess_mono f0 fs r fsegs hfsort hrf hδle

/-! ## Faithfulness checks -/

/-- Faithfulness: the excess is `0` at the breakpoint and nondecreasing afterward. -/
example (f0 fs r : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    {d₁ d₂ : ℝ≥0} (h : d₁ ≤ d₂) :
    excess f0 fs r fsegs 0 = 0 ∧ excess f0 fs r fsegs d₁ ≤ excess f0 fs r fsegs d₂ :=
  ⟨excess_zero f0 fs r fsegs, excess_mono f0 fs r fsegs hfsort hrf h⟩

/-- Faithfulness: over a single steep segment, the excess is the explicit ramp `(s − r)·d`. -/
example (f0 fs r s ℓ : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    (htail : dropSegs r fsegs = (s, ℓ) :: []) {d : ℝ≥0} (hd : d ≤ ℓ) :
    excess f0 fs r fsegs d = (s - r) * d :=
  excess_singleTail_on_seg f0 fs r s ℓ fsegs hfsort hrf htail hd

/-- Faithfulness: the crossing offset `δ = b / (s − r)` hits the burst exactly, `E(δ) = b`. -/
example (f0 fs r s ℓ b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    (htail : dropSegs r fsegs = (s, ℓ) :: []) (hrs : r < s) (hb : b ≤ (s - r) * ℓ) :
    excess f0 fs r fsegs (crossingOffset_singleTail r s b) = b :=
  excess_singleTail_crossingOffset f0 fs r s ℓ b fsegs hfsort hrf htail hrs hb

/-- Faithfulness: at the explicit crossing `t = u** = u* + b/(s−r)` the two regimes agree — the
slack form `f t` and the binding form `f(u*) + b + r·(t − u*)` give the same value (the meet is
single-valued at the crossing). -/
example (f0 fs r s ℓ b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    (htail : dropSegs r fsegs = (s, ℓ) :: []) (hrs : r < s) (hb : b ≤ (s - r) * ℓ) :
    (((convexSegEval f0 fs fsegs
          (segLenSum (truncSegs r fsegs) + crossingOffset_singleTail r s b) : ℝ≥0) : ℝ) : EReal)
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * ((segLenSum (truncSegs r fsegs) + crossingOffset_singleTail r s b)
                - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal) := by
  have hf := minConv_tbEReal_eq_f_below_crossing f0 fs r s ℓ b fsegs hfsort hfs hrf htail hrs hb
    (t := segLenSum (truncSegs r fsegs) + crossingOffset_singleTail r s b) le_self_add le_rfl
  have hline := minConv_tbEReal_eq_line_above_crossing f0 fs r s ℓ b fsegs hfsort hfs hrf htail hrs hb
    (t := segLenSum (truncSegs r fsegs) + crossingOffset_singleTail r s b) le_rfl
  rw [hf] at hline
  exact hline

end DeepWiki
