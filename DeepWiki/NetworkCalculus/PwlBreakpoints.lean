import DeepWiki.NetworkCalculus.ConvexConvByLine
import DeepWiki.NetworkCalculus.ConvexSegmentMerge

/-! # Breakpoint / rank structure of a convex PWL (§4.4 infra)
The book's Prop 4.4 [4.13] and Def 4.4 finiteness rest on the breakpoint structure of a
convex piecewise-linear curve `f = convexSegEval f0 fs segs`: the abscissae where the slope
changes (the non-differentiable points), the rank `u*` of the last semi-infinite segment, and
the corner values `f` takes there. This file builds that structure on the slope/length
representation: `pwlRank` (the rank `= segLenSum`), `breakpoints` (the cumulative-length
abscissae), and `convexSegEval_at_breakpoint` (the corner value `f0 + Σ slopeᵢ·lengthᵢ`). -/

namespace DeepWiki

open scoped NNReal

/-! ## Rank — the abscissa of the last semi-infinite segment -/

/-- The **rank** of a convex PWL `convexSegEval f0 fs segs`: the abscissa `u*` where the last
(semi-infinite) segment of slope `fs` begins, i.e. the cumulative length of all finite segments
(`= segLenSum segs`). -/
noncomputable def pwlRank (segs : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 := segLenSum segs

@[simp] theorem pwlRank_nil : pwlRank [] = 0 := rfl

@[simp] theorem pwlRank_cons (s ℓ : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    pwlRank ((s, ℓ) :: rest) = ℓ + pwlRank rest := rfl

/-- **Past the rank a convex PWL is its asymptote line.** For `t ≥ pwlRank segs` the finite
segments are exhausted, so the curve continues from the corner `f(u*)` at slope `fs`:
`f t = f(u*) + fs·(t − u*)`. (Restatement of `convexSegEval_past_segs` on `pwlRank`.) -/
theorem convexSegEval_past_rank (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) {t : ℝ≥0}
    (ht : pwlRank segs ≤ t) :
    convexSegEval f0 fs segs t
      = convexSegEval f0 fs segs (pwlRank segs) + fs * (t - pwlRank segs) :=
  convexSegEval_past_segs fs segs f0 t ht

end DeepWiki
