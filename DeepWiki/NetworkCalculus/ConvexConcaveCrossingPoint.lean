import DeepWiki.NetworkCalculus.ConvexSegEvalSplit

/-! # The single switch of the Theorem 4.2 token-bucket crossing, made structural (§4.2.2)
`minConv_tbEReal_convexSegEval_eq` reduces `f ∗ γ_{r,b}` to a pointwise meet
`f(t) ⊓ (f(u*) + b + r·(t − u*))`, and `convexSegEval_le_lineCont_downset` shows the comparison
"`f` vs the line" flips at most once past the breakpoint `u* = segLenSum (truncSegs r fsegs)`. This
file packages that single switch as **contiguous regimes** (no explicit coordinate): the slack region
`{t | f ∗ γ = f}` is an interval reaching down to `u*`, the binding region `{t | f ∗ γ = line}` is a
final interval, and the up-set form (binding stays binding) is the contrapositive of the down-set.

It then resolves the two edge cases of the threshold honestly:
* **`r = fs` — slack forever.** When the bucket rate equals `f`'s asymptotic slope the line never
  binds: `f ∗ γ_{r,b} = f` for *all* `t` (`convexSegEval_upper_rate` caps `f`'s growth at `fs = r`,
  so `f ≤ line` everywhere).
* **`r < fs` — eventual binding.** The existence of a finite binding threshold is **not** assumed:
  it holds iff `f` ever overtakes the line, which it does once a steep segment of slope `> r`
  contributes more than `b` of excess. The conditional "if `f` reaches the line at some `τ ≥ u*`,
  it stays bound beyond `τ`" is stated unconditionally (it is the up-set), and the genuine
  sufficient condition (a single segment past `u*` whose excess exceeds `b`) is given. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## The single switch as contiguous regimes (no explicit coordinate) -/

/-- The line continuation `c(t) = f(u*) + b + r·(t − u*)`, `u* = segLenSum (truncSegs r fsegs)`,
abbreviated for the regime statements. -/
noncomputable def lineCont (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) : ℝ≥0 :=
  convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
    + r * (t - segLenSum (truncSegs r fsegs))

@[simp] theorem lineCont_apply (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    lineCont f0 fs r b fsegs t
      = convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
          + r * (t - segLenSum (truncSegs r fsegs)) := rfl

/-- **Binding stays binding (up-set form).** The dual of `convexSegEval_le_lineCont_downset`: if the
line continuation has fallen under the curve at `t₁` (`c t₁ ≤ f t₁`) with `u* ≤ t₁ ≤ t₂`, then it
stays under at `t₂` (`c t₂ ≤ f t₂`). (`c t₂ = c t₁ + r·(t₂ − t₁) ≤ f t₁ + r·(t₂ − t₁) ≤ f t₂`,
the last step the minimum growth rate past the breakpoint; equivalently `c − f` is nonincreasing.) -/
theorem lineCont_le_convexSegEval_upset (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs) (hrf : r ≤ fs)
    {t₁ t₂ : ℝ≥0} (h1 : segLenSum (truncSegs r fsegs) ≤ t₁) (h12 : t₁ ≤ t₂)
    (h : lineCont f0 fs r b fsegs t₁ ≤ convexSegEval f0 fs fsegs t₁) :
    lineCont f0 fs r b fsegs t₂ ≤ convexSegEval f0 fs fsegs t₂ := by
  rw [lineCont_apply] at h ⊢
  set us := segLenSum (truncSegs r fsegs) with hus
  set fu := convexSegEval f0 fs fsegs us with hfu
  -- the line splits additively: `c t₂ = c t₁ + r·(t₂ − t₁)`
  have hsum : t₂ - us = (t₁ - us) + (t₂ - t₁) := by
    rw [add_comm]; exact (tsub_add_tsub_cancel h12 h1).symm
  have hline : fu + b + r * (t₂ - us) = (fu + b + r * (t₁ - us)) + r * (t₂ - t₁) := by
    rw [hsum, mul_add]; ring
  -- `f` grows by at least `r·(t₂ − t₁)` from `t₁` to `t₂`
  have hgrow : convexSegEval f0 fs fsegs t₁ + r * (t₂ - t₁) ≤ convexSegEval f0 fs fsegs t₂ :=
    convexSegEval_rate_from_breakpoint f0 fs r fsegs hfsort hrf h1 h12
  calc fu + b + r * (t₂ - us)
      = (fu + b + r * (t₁ - us)) + r * (t₂ - t₁) := hline
    _ ≤ convexSegEval f0 fs fsegs t₁ + r * (t₂ - t₁) := by gcongr
    _ ≤ convexSegEval f0 fs fsegs t₂ := hgrow

/-- **Slack region is an initial interval (down to `u*`).** If `f ∗ γ_{r,b}` equals `f` at some
`t₂ ≥ u*` (the slack/`f`-wins regime), then it equals `f` at *every* `t₁` with `u* ≤ t₁ ≤ t₂`. The
single switch packaged as an interval: once the bucket starts binding it never goes slack again, so
the slack times past `u*` are contiguous. -/
theorem minConv_tbEReal_convexSegEval_eq_f_of_le (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t₁ t₂ : ℝ≥0} (h1 : segLenSum (truncSegs r fsegs) ≤ t₁) (h12 : t₁ ≤ t₂)
    (h2 : convexSegEval f0 fs fsegs t₂ ≤ lineCont f0 fs r b fsegs t₂) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t₁
      = (((convexSegEval f0 fs fsegs t₁ : ℝ≥0) : ℝ) : EReal) := by
  rw [lineCont_apply] at h2
  exact minConv_tbEReal_convexSegEval_eq_f f0 fs r b fsegs hfsort hfs hrf
    (convexSegEval_le_lineCont_downset f0 fs r b fsegs hfsort hrf h1 h12 h2)

/-- **Binding region is a final interval.** If `f ∗ γ_{r,b}` runs at the bucket rate (equals the line
continuation) at some `t₁ ≥ u*` (the binding/`line`-wins regime), then it equals the line at *every*
`t₂ ≥ t₁`. The other half of the single switch: once binding, always binding — the binding times form
a final interval `[τ, ∞)`. -/
theorem minConv_tbEReal_convexSegEval_eq_line_of_le (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t₁ t₂ : ℝ≥0} (h1 : segLenSum (truncSegs r fsegs) ≤ t₁) (h12 : t₁ ≤ t₂)
    (h1bind : lineCont f0 fs r b fsegs t₁ ≤ convexSegEval f0 fs fsegs t₁) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t₂
      = (((lineCont f0 fs r b fsegs t₂ : ℝ≥0) : ℝ) : EReal) := by
  have hbind := lineCont_le_convexSegEval_upset f0 fs r b fsegs hfsort hrf h1 h12 h1bind
  rw [lineCont_apply] at hbind ⊢
  exact minConv_tbEReal_convexSegEval_eq_line f0 fs r b fsegs hfsort hfs hrf hbind

/-! ## Edge case `r = fs`: the bucket is slack forever -/

/-- **`r = fs` ⇒ `f ≤ line` everywhere.** When the bucket rate equals `f`'s asymptotic slope, the
curve never overtakes the line continuation: `f t ≤ f(u*) + b + r·(t − u*)` for *all* `t`. (Past
`u*`, `convexSegEval_upper_rate` caps `f`'s growth at `fs = r`, so `f t ≤ f(u*) + fs·(t − u*) ≤
f(u*) + b + r·(t − u*)`; below `u*` it follows from monotonicity since `t − u* = 0`.) -/
theorem convexSegEval_le_lineCont_of_rate_eq (f0 fs b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (t : ℝ≥0) :
    convexSegEval f0 fs fsegs t ≤ lineCont f0 fs fs b fsegs t := by
  rw [lineCont_apply]
  set us := segLenSum (truncSegs fs fsegs) with hus
  by_cases ht : t ≤ us
  · -- below the breakpoint: `t − u* = 0`, so the line is `f(u*) + b ≥ f(u*) ≥ f(t)`
    rw [tsub_eq_zero_of_le ht, mul_zero, add_zero]
    exact le_trans (monotone_convexSegEval fs fsegs f0 ht) le_self_add
  · rw [not_le] at ht
    -- write `t = u* + (t − u*)` and cap growth at `fs`
    have hsplit : convexSegEval f0 fs fsegs t
        = convexSegEval f0 fs fsegs (us + (t - us)) := by
      rw [add_tsub_cancel_of_le (le_of_lt ht)]
    rw [hsplit]
    calc convexSegEval f0 fs fsegs (us + (t - us))
        ≤ convexSegEval f0 fs fsegs us + fs * (t - us) :=
          convexSegEval_upper_rate fs fs fsegs hfs le_rfl f0 us (t - us)
      _ ≤ convexSegEval f0 fs fsegs us + b + fs * (t - us) := by
          rw [add_right_comm]; exact le_self_add

/-- **Theorem 4.2, `r = fs` (bucket slack forever).** When the token-bucket rate equals `f`'s
asymptotic slope, the bucket never binds: `f ∗ γ_{fs,b} = f` for *every* `t`. (The slack regime
`minConv_tbEReal_convexSegEval_eq_f` applies at all `t` because `f ≤ line` everywhere by
`convexSegEval_le_lineCont_of_rate_eq`.) -/
theorem minConv_tbEReal_convexSegEval_eq_f_of_rate_eq (f0 fs b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (t : ℝ≥0) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal fs b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) := by
  have h := convexSegEval_le_lineCont_of_rate_eq f0 fs b fsegs hfs t
  rw [lineCont_apply] at h
  exact minConv_tbEReal_convexSegEval_eq_f f0 fs fs b fsegs hfsort hfs le_rfl h

/-! ## Edge case `r < fs`: existence of a finite binding threshold is conditional

A finite binding threshold exists **iff** `f` eventually overtakes the line — which it does precisely
when some accumulated excess past `u*` exceeds `b`. We do *not* assume it; instead:
* the conditional "if `f` reaches the line at `τ`, the bucket binds for all `t ≥ τ`" is exactly
  `minConv_tbEReal_convexSegEval_eq_line_of_le`;
* a concrete sufficient witness is recorded below (a point past `u*` where `f`'s excess `≥ b`). -/

/-- **Sufficient condition for the binding regime to start.** If past the breakpoint the curve's
own growth `f(t) − f(u*)` exceeds the rate-`r` line's growth by at least `b` (i.e.
`f(u*) + b + r·(t − u*) ≤ f(t)`), then the bucket binds at `t` and at all later times: for every
`t' ≥ t`, `f ∗ γ_{r,b} t' = f(u*) + b + r·(t' − u*)`. This is the genuine entry criterion to the
final binding interval — no finite threshold is presumed, only this verifiable excess bound. -/
theorem minConv_tbEReal_convexSegEval_eq_line_of_excess (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t t' : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t) (htt' : t ≤ t')
    (hexcess : lineCont f0 fs r b fsegs t ≤ convexSegEval f0 fs fsegs t) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t'
      = (((lineCont f0 fs r b fsegs t' : ℝ≥0) : ℝ) : EReal) :=
  minConv_tbEReal_convexSegEval_eq_line_of_le f0 fs r b fsegs hfsort hfs hrf ht htt' hexcess

/-! ## Faithfulness checks -/

/-- Faithfulness: `r = fs` collapses the meet to `f` for all `t` (bucket never binds). -/
example (f0 fs b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (t : ℝ≥0) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal fs b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) :=
  minConv_tbEReal_convexSegEval_eq_f_of_rate_eq f0 fs b fsegs hfsort hfs t

/-- Faithfulness: the slack region is downward closed (an initial interval) past `u*`. -/
example (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t₁ t₂ : ℝ≥0} (h1 : segLenSum (truncSegs r fsegs) ≤ t₁) (h12 : t₁ ≤ t₂)
    (h2 : convexSegEval f0 fs fsegs t₂ ≤ lineCont f0 fs r b fsegs t₂) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t₁
      = (((convexSegEval f0 fs fsegs t₁ : ℝ≥0) : ℝ) : EReal) :=
  minConv_tbEReal_convexSegEval_eq_f_of_le f0 fs r b fsegs hfsort hfs hrf h1 h12 h2

/-- Faithfulness: the binding region is upward closed (a final interval) past `u*`. -/
example (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t₁ t₂ : ℝ≥0} (h1 : segLenSum (truncSegs r fsegs) ≤ t₁) (h12 : t₁ ≤ t₂)
    (h1bind : lineCont f0 fs r b fsegs t₁ ≤ convexSegEval f0 fs fsegs t₁) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t₂
      = (((lineCont f0 fs r b fsegs t₂ : ℝ≥0) : ℝ) : EReal) :=
  minConv_tbEReal_convexSegEval_eq_line_of_le f0 fs r b fsegs hfsort hfs hrf h1 h12 h1bind

end DeepWiki
