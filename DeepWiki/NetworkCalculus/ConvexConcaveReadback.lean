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

end DeepWiki
