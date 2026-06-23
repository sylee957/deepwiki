import DeepWiki.NetworkCalculus.PwlThetaDecomp
import DeepWiki.NetworkCalculus.PwlBreakpoints
import DeepWiki.NetworkCalculus.ConvexPWLNormalForm
import DeepWiki.NetworkCalculus.ConvexSegmentMerge

/-! # Prop 4.4 [4.13], convex companion — `f̲ = ⨆ᵢ β_{sᵢ, Tᵢ}` from segment tangents
The convex side of [4.13]: a slope-sorted convex PWL `f̲ = convexSegEval f0 fs segs` is the
pointwise *supremum of its segment tangent rate-latencies*, `f̲ = ⨆ᵢ β_{sᵢ, Tᵢ}` ("a convex
function is the sup of its tangent lines"). The `≤` inclusion and the asymptotic-region equality
live in `PwlThetaDecomp` (`convexNFEval_le_convexSegEval`, `convexNFEval_eq_past_rank_of_mem_tangent`);
this file adds the **per-segment `≥`**.

* **Segment-affine value.** On its `i`-th finite segment `[τᵢ, τᵢ+ℓᵢ]` (slope `sᵢ`) the curve is
  exactly the affine piece `f̲(t) = f̲(τᵢ) + sᵢ·(t − τᵢ)` (`convexSegEval_affine_on_seg`).
* **Per-segment tangent latency** `segTangentLatency`: `Tᵢ = τᵢ − f̲(τᵢ)/sᵢ`, the x-intercept of
  segment `i`'s affine extension. On segment `i` (with `sᵢ > 0`) the tangent reaches the curve,
  `β_{sᵢ, Tᵢ}(t) = f̲(t)` (`rateLatencyEReal_segTangent_eq_on_seg`).
* **The `≥` direction and full equality.** Combined with `PwlThetaDecomp`'s `≤`, the tangent
  generators (segment tangents + the asymptotic tangent) realise `f̲` exactly on all of `[0,∞)`
  when every slope is positive (`convexNFEval_eq_convexSegEval`). -/

namespace DeepWiki

open scoped Classical NNReal

/-! ## Segment-affine value: the curve is its affine piece on each segment

A convex PWL split as `segs = pre ++ (s, ℓ) :: post` is affine of slope `s` on the `pre`-anchored
segment `[segLenSum pre, segLenSum pre + ℓ]`. -/

/-- **The curve is affine on each finite segment.** Splitting `segs = pre ++ (s, ℓ) :: post`, the
segment after the cumulative length `τ = segLenSum pre` has slope `s`; for `τ ≤ t ≤ τ + ℓ` the curve
is the affine piece `f̲(t) = f̲(τ) + s·(t − τ)`. -/
theorem convexSegEval_affine_on_seg (f0 fs s ℓ : ℝ≥0) (pre post : List (ℝ≥0 × ℝ≥0)) {t : ℝ≥0}
    (hlo : segLenSum pre ≤ t) (hhi : t ≤ segLenSum pre + ℓ) :
    convexSegEval f0 fs (pre ++ (s, ℓ) :: post) t
      = convexSegEval f0 fs (pre ++ (s, ℓ) :: post) (segLenSum pre) + s * (t - segLenSum pre) := by
  induction pre generalizing f0 t with
  | nil =>
      -- `τ = 0`, the leading segment is `(s, ℓ)`; for `t ≤ ℓ` the value is `f0 + s·t`
      simp only [List.nil_append, segLenSum_nil, tsub_zero, convexSegEval_zero] at *
      rw [zero_add] at hhi
      rw [convexSegEval_cons, if_pos hhi]
  | cons hd tl ih =>
      obtain ⟨sa, ℓa⟩ := hd
      rw [List.cons_append, segLenSum_cons]
      rw [segLenSum_cons] at hlo hhi
      have hℓat : ℓa ≤ t := le_trans le_self_add hlo
      -- peel the leading `(sa, ℓa)` segment, apply IH to the tail at `t - ℓa`
      have hpeel : convexSegEval f0 fs ((sa, ℓa) :: (tl ++ (s, ℓ) :: post)) t
          = convexSegEval (f0 + sa * ℓa) fs (tl ++ (s, ℓ) :: post) (t - ℓa) := by
        rw [← convexSegEval_cons_peel f0 fs sa ℓa (t - ℓa) (tl ++ (s, ℓ) :: post),
          add_tsub_cancel_of_le hℓat]
      have hpeelτ : convexSegEval f0 fs ((sa, ℓa) :: (tl ++ (s, ℓ) :: post)) (ℓa + segLenSum tl)
          = convexSegEval (f0 + sa * ℓa) fs (tl ++ (s, ℓ) :: post) (segLenSum tl) :=
        convexSegEval_cons_peel f0 fs sa ℓa (segLenSum tl) (tl ++ (s, ℓ) :: post)
      have hlo' : segLenSum tl ≤ t - ℓa := by rw [le_tsub_iff_left hℓat]; exact hlo
      have hhi' : t - ℓa ≤ segLenSum tl + ℓ := by
        rw [tsub_le_iff_left]
        refine le_trans hhi (le_of_eq ?_); ring
      rw [hpeel, hpeelτ, ih (f0 + sa * ℓa) hlo' hhi']
      -- `t - ℓa - segLenSum tl = t - (ℓa + segLenSum tl)`
      rw [tsub_tsub]

/-- **The curve value at the start of a segment depends only on the prefix.** Splitting
`segs = pre ++ rest`, the value at the cumulative length `τ = segLenSum pre` is the value of the
prefix curve there: `f̲(τ) = convexSegEval f0 fs pre τ = f0 + cornerSum pre`. (The suffix segments
start after `τ`, so they do not affect the value at `τ`.) -/
theorem convexSegEval_append_at_segLenSum (f0 fs : ℝ≥0) (pre rest : List (ℝ≥0 × ℝ≥0)) :
    convexSegEval f0 fs (pre ++ rest) (segLenSum pre) = f0 + cornerSum pre := by
  induction pre generalizing f0 with
  | nil => simp
  | cons hd tl ih =>
      obtain ⟨sa, ℓa⟩ := hd
      rw [segLenSum_cons, cornerSum_cons, List.cons_append,
        convexSegEval_cons_peel, ih]
      ring

/-! ## Per-segment tangent latency and own-segment exactness -/

/-- The **per-segment tangent latency** of segment `i` (split `segs = pre ++ (s, ℓ) :: post`, with
`τ = segLenSum pre`, `v = f̲(τ) = f0 + cornerSum pre`): `Tᵢ = τ − v/s`, the abscissa where segment
`i`'s affine extension (slope `s` through `(τ, v)`) crosses zero. Depends only on the prefix `pre`
(and `f0`), not on the segment or what follows. -/
noncomputable def segTangentLatency (f0 : ℝ≥0) (pre : List (ℝ≥0 × ℝ≥0)) (s : ℝ≥0) : ℝ≥0 :=
  segLenSum pre - (f0 + cornerSum pre) / s

end DeepWiki
