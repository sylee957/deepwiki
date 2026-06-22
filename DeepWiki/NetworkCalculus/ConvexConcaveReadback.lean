import DeepWiki.NetworkCalculus.ConcaveSegmentMerge
import DeepWiki.NetworkCalculus.ConvexConvByLine

/-! # Reading a convex-by-concave convolution back into PWL pieces (toward Theorem 4.2)
The distribution engine (`minConv_concaveNFEval_foldr`) plus the per-bucket readback
(`minConv_tbEReal_eq_inf`) express `f ∗ (concave PWL)` as a meet of `(f ∗ lineⱼ) ⊓ f`. This file
plugs in the convex side: each line `lineᵣᵦ = r·t + b` is the empty-segment convex curve
`convexSegEval b r []`, so `f ∗ lineᵣᵦ` is the closed form of the Lemma 4.1 engine. The concrete
payoff: below a bucket's breakpoint the token bucket is inactive, `f ∗ γ_{r,b} = f`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The `EReal` coe of any `ℝ≥0`-valued curve is never `⊥` (every value is a finite coe). -/
theorem isNeverBot_coe_nnreal (g : ℝ≥0 → ℝ≥0) :
    IsNeverBot (fun t => (((g t : ℝ≥0) : ℝ) : EReal)) :=
  fun _ => EReal.coe_ne_bot _

/-- The token-bucket line `r·t + b` is the empty-segment convex curve `convexSegEval b r []`
(base `b`, slope `r`): `rateEReal r + b = fun u ↦ ↑↑(convexSegEval b r [] u)`. -/
theorem rateEReal_add_const_eq_convexSegEval (r b : ℝ≥0) :
    rateEReal r + Function.const ℝ≥0 ((b : ℝ) : EReal)
      = fun u => (((convexSegEval b r [] u : ℝ≥0) : ℝ) : EReal) := by
  funext u
  simp only [Pi.add_apply, rateEReal_apply, Function.const_apply, convexSegEval_nil]
  rw [← EReal.coe_add]
  norm_cast
  ring

/-- Per-bucket readback with the line in convex-curve form: `f ∗ γ_{r,b} = (f ∗ convexSegEval b r [])
⊓ f`, so the Lemma 4.1 engine (`minConv_line_convexSegEval_*`) computes the line factor. -/
theorem minConv_tbEReal_eq_line_inf {f : ℝ≥0 → EReal} (hf : IsNeverBot f) (r b : ℝ≥0) :
    minConv f (tbEReal r b)
      = minConv f (fun u => (((convexSegEval b r [] u : ℝ≥0) : ℝ) : EReal)) ⊓ f := by
  rw [minConv_tbEReal_eq_inf hf, rateEReal_add_const_eq_convexSegEval]

/-- **Theorem 4.2 readback, below a breakpoint.** For a convex PWL `f = convexSegEval f0 fs fsegs`
(with `r ≤ fs`), below the bucket's breakpoint `u* = segLenSum (truncSegs r fsegs)` the token bucket
`γ_{r,b}` is inactive: `f ∗ γ_{r,b} = f`. (The line factor is `f + b ≥ f` there, so the meet with
`f` returns `f`.) -/
theorem minConv_tbEReal_convexSegEval_below (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : t ≤ segLenSum (truncSegs r fsegs)) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_tbEReal_eq_line_inf (isNeverBot_coe_nnreal _), Pi.inf_apply, minConv_comm,
    minConv_line_convexSegEval_below f0 fs b r fsegs hfsort hfs hrf ht, inf_eq_right]
  exact_mod_cast le_self_add

/-- **Theorem 4.2 readback, above a breakpoint.** For a convex PWL `f = convexSegEval f0 fs fsegs`
(`r ≤ fs`), at or beyond the bucket's breakpoint `u* = segLenSum (truncSegs r fsegs)` the token
bucket convolution is the meet of the line continuation `f(u*) + b + r·(t − u*)` and `f` itself —
neither dominates in general (the line starts above by `b`, then `f` overtakes it). -/
theorem minConv_tbEReal_convexSegEval_above (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs)
    {t : ℝ≥0} (ht : segLenSum (truncSegs r fsegs) ≤ t) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
            + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal)
          ⊓ (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_tbEReal_eq_line_inf (isNeverBot_coe_nnreal _), Pi.inf_apply, minConv_comm,
    minConv_line_convexSegEval_above f0 fs b r fsegs hfsort hfs hrf ht]

/-- **Toward the global ordering (outer Lemma 4.1).** Below the *lower*-rate bucket's breakpoint
`u*(r)` (with `r ≤ r'`, so `u*(r) ≤ u*(r')` by `segLenSum_truncSegs_mono`), *both* token buckets are
inactive and convolve to `f`, so they tie: `f ∗ γ_{r,b} = f ∗ γ_{r',b'}` there. The first
where-which-bucket-dominates region of the ordering — a tie. -/
theorem minConv_tbEReal_convexSegEval_eq_below (f0 fs r r' b b' : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs) (hr'f : r' ≤ fs) (hrr' : r ≤ r')
    {t : ℝ≥0} (ht : t ≤ segLenSum (truncSegs r fsegs)) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r' b') t := by
  rw [minConv_tbEReal_convexSegEval_below f0 fs r b fsegs hfsort hfs hrf ht,
    minConv_tbEReal_convexSegEval_below f0 fs r' b' fsegs hfsort hfs hr'f
      (le_trans ht (segLenSum_truncSegs_mono hrr' fsegs))]

/-- Convolving by a token bucket can only lower the curve: `f ∗ γ_{r,b} ≤ f`, since the readback
`(f ∗ lineᵣᵦ) ⊓ f` is a meet with `f`. General over `IsNeverBot f`. -/
theorem minConv_tbEReal_le_self {f : ℝ≥0 → EReal} (hf : IsNeverBot f) (r b : ℝ≥0) :
    minConv f (tbEReal r b) ≤ f := by
  rw [minConv_tbEReal_eq_inf hf]; exact inf_le_right

/-- **Toward the global ordering — domination.** Up to the *higher*-rate bucket's breakpoint
`u*(r')`, the lower-rate bucket's convolution dominates (is `≤`): `f ∗ γ_{r,b} t ≤ f ∗ γ_{r',b'} t`
for `t ≤ u*(r')`. There the higher bucket is still inactive (`f ∗ γ_{r',b'} = f`) while
`f ∗ γ_{r,b} ≤ f` always — so on the whole region `[0, u*(r')]` the lower-rate bucket is the one that
appears in the min. -/
theorem minConv_tbEReal_convexSegEval_le_below (f0 fs r r' b b' : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hr'f : r' ≤ fs)
    {t : ℝ≥0} (ht' : t ≤ segLenSum (truncSegs r' fsegs)) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      ≤ minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r' b') t := by
  rw [minConv_tbEReal_convexSegEval_below f0 fs r' b' fsegs hfsort hfs hr'f ht']
  exact minConv_tbEReal_le_self (isNeverBot_coe_nnreal _) r b t

/-! ## The crossing, base case: `f` a single rate (`fsegs = []`) -/

/-- **Crossing base case — explicit value.** For `f` a single-rate line `convexSegEval f0 fs []`
(`r ≤ fs`), the breakpoint is at the origin, so the bucket convolution is the meet of the two
affines for *all* `t`: `f ∗ γ_{r,b} t = (f0 + b + r·t) ⊓ (f0 + fs·t)`. -/
theorem minConv_tbEReal_line (f0 fs r b : ℝ≥0) (hrf : r ≤ fs) (t : ℝ≥0) :
    minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((f0 + b + r * t : ℝ≥0) : ℝ) : EReal) ⊓ (((f0 + fs * t : ℝ≥0) : ℝ) : EReal) := by
  have h0 : segLenSum (truncSegs r ([] : List (ℝ≥0 × ℝ≥0))) = 0 := by simp
  rw [minConv_tbEReal_convexSegEval_above f0 fs r b [] (by simp) (by simp) hrf
      (by rw [h0]; positivity)]
  rw [h0]
  simp only [convexSegEval_nil, mul_zero, add_zero, tsub_zero]

/-- **Crossing base case — left of the crossing.** While `fs·t ≤ r·t + b` (i.e. `(fs−r)·t ≤ b`,
left of the crossing `t = b/(fs−r)`), the bucket is inactive and `f ∗ γ_{r,b} = f` (`= f0 + fs·t`). -/
theorem minConv_tbEReal_line_eq_f (f0 fs r b : ℝ≥0) (hrf : r ≤ fs) {t : ℝ≥0}
    (h : fs * t ≤ r * t + b) :
    minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((f0 + fs * t : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_tbEReal_line f0 fs r b hrf, inf_eq_right]
  have hle : f0 + fs * t ≤ f0 + b + r * t :=
    calc f0 + fs * t ≤ f0 + (r * t + b) := add_le_add le_rfl h
      _ = f0 + b + r * t := by ring
  exact_mod_cast hle

/-- **Crossing base case — right of the crossing.** Once `r·t + b ≤ fs·t` (right of the crossing),
the token-bucket line takes over and `f ∗ γ_{r,b} = f0 + b + r·t` (slope `r`, the bucket's rate). -/
theorem minConv_tbEReal_line_eq_line (f0 fs r b : ℝ≥0) (hrf : r ≤ fs) {t : ℝ≥0}
    (h : r * t + b ≤ fs * t) :
    minConv (fun v => (((convexSegEval f0 fs [] v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((f0 + b + r * t : ℝ≥0) : ℝ) : EReal) := by
  rw [minConv_tbEReal_line f0 fs r b hrf, inf_eq_left]
  have hle : f0 + b + r * t ≤ f0 + fs * t :=
    calc f0 + b + r * t = f0 + (r * t + b) := by ring
      _ ≤ f0 + fs * t := add_le_add le_rfl h
  exact_mod_cast hle

/-- **Crossing, general convex `f` — unified meet form.** For any convex PWL
`f = convexSegEval f0 fs fsegs` (`r ≤ fs`), the bucket convolution is, for *all* `t`, the pointwise
meet of `f` and the truncated line through the breakpoint: `f ∗ γ_{r,b} t = f(t) ⊓ (f(u*) + b +
r·(t − u*))`, `u* = segLenSum (truncSegs r fsegs)`. Below `u*` the truncated `t − u* = 0` makes the
line `f(u*) + b ≥ f`, so the meet returns `f`. Generalizes `minConv_tbEReal_line` (the `fsegs = []`
case) to arbitrary segments. (Locating *which* term wins — the single crossing point inside `f`'s
segments — needs `f`'s minimum-growth-rate beyond `u*` and is the remaining piece.) -/
theorem minConv_tbEReal_convexSegEval_eq (f0 fs r b : ℝ≥0) (fsegs : List (ℝ≥0 × ℝ≥0))
    (hfsort : List.Pairwise (fun a c => a.1 ≤ c.1) fsegs)
    (hfs : ∀ seg ∈ fsegs, seg.1 ≤ fs) (hrf : r ≤ fs) (t : ℝ≥0) :
    minConv (fun v => (((convexSegEval f0 fs fsegs v : ℝ≥0) : ℝ) : EReal)) (tbEReal r b) t
      = (((convexSegEval f0 fs fsegs t : ℝ≥0) : ℝ) : EReal)
        ⊓ (((convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b
              + r * (t - segLenSum (truncSegs r fsegs)) : ℝ≥0) : ℝ) : EReal) := by
  by_cases ht : t ≤ segLenSum (truncSegs r fsegs)
  · rw [minConv_tbEReal_convexSegEval_below f0 fs r b fsegs hfsort hfs hrf ht,
      tsub_eq_zero_of_le ht, mul_zero, add_zero]
    have hle : convexSegEval f0 fs fsegs t
        ≤ convexSegEval f0 fs fsegs (segLenSum (truncSegs r fsegs)) + b :=
      le_trans (monotone_convexSegEval fs fsegs f0 ht) le_self_add
    exact (inf_of_le_left (by exact_mod_cast hle)).symm
  · rw [not_le] at ht
    rw [minConv_tbEReal_convexSegEval_above f0 fs r b fsegs hfsort hfs hrf (le_of_lt ht), inf_comm]

end DeepWiki
