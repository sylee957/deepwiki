import DeepWiki.NetworkCalculus.PwlBreakpoints
import DeepWiki.NetworkCalculus.ConvexSegmentMerge
import DeepWiki.NetworkCalculus.ConvexPWLNormalForm

/-! # Proposition 4.4 [4.13] — the canonical upper bound `Ω_f̲` of a convex PWL
Two companion representations of a convex piecewise-linear curve `f̲ = convexSegEval f0 fs segs`
along its breakpoints (the non-differentiable points `(τᵢ, κᵢ)`):

* **[4.13] (concave-companion side) — the `Θ`-meet `Ω_f̲`.** The book's canonical *upper bound*
  `Ω_f̲ = ⋀ᵢ Θ^{κᵢ}_{τᵢ}` (eq. [4.13], p. 86) is the `(min,+)` meet (dioid `+ = ⊓`) of the
  piecewise-constant elementary functions `Θ^{κᵢ}_{τᵢ}` (eq. [4.5]: `κᵢ` on `[0, τᵢ]`, `⊤`
  after) pinned at the breakpoints with `κᵢ = f̲(τᵢ)`. It is *piecewise constant*, lies above
  `f̲` everywhere (`f̲ ≤ Ω_f̲`), samples `f̲` exactly at the breakpoints, and is `⊤` past the
  rank. (The generator data is built in `PwlBreakpoints`; this file packages the named upper
  bound and the book's `Θ^{κ₀}_{τ₀} = Θ^{κ_f̲}_{τ_f̲}` identity.)

* **convex side — the sup of rate-latencies `convexNFEval`.** The convex representative `f̲`
  itself is the pointwise *supremum* of rate-latency curves `β_{Rᵢ, Tᵢ}(t) = Rᵢ·(t − Tᵢ)₊`
  (`convexNFEval`, `isConvexEReal_convexNFEval`). The breakpoint-anchored generators
  `β_{sᵢ, τᵢ}` (slope `sᵢ` of the segment after breakpoint `τᵢ`) each lie *below* `f̲`, giving
  one inclusion of the convex sup-of-rate-latencies decomposition. -/

namespace DeepWiki

open scoped Classical NNReal

/-! ## [4.13] — the canonical upper bound `Ω_f̲` as the `Θ`-meet over breakpoints -/

/-- **The canonical upper bound `Ω_f̲`** (eq. [4.13]): the `(min,+)` meet `⋀ᵢ Θ^{κᵢ}_{τᵢ}` of the
elementary functions pinned at the non-differentiable points `(τᵢ, κᵢ)` of the convex PWL
`convexSegEval f0 fs segs`, with corner value `κᵢ = ↑(f̲(τᵢ))`. A piecewise-constant function. -/
noncomputable def canonicalUpperBound (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 → EReal :=
  meetSpots (breakpointThetas f0 fs segs)

/-- `Ω_f̲` unfolds to the `Θ`-meet of the breakpoint generators. -/
theorem canonicalUpperBound_eq (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) :
    canonicalUpperBound f0 fs segs = meetSpots (breakpointThetas f0 fs segs) := rfl

/-- **[4.13]: `f̲ ≤ Ω_f̲`.** The canonical upper bound dominates the curve everywhere — the book's
`∀ f̄ ∈ [f̲, f̄]_𝓛, f̲ ≤ Ω_f̲`. (Each `Θ`-generator caps the curve at a corner `≥ f̲(t)` by
monotonicity; past the rank every generator is `⊤`.) -/
theorem convexSegEval_le_canonicalUpperBound (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) :
    ((convexSegEval f0 fs segs t : ℝ≥0) : EReal) ≤ canonicalUpperBound f0 fs segs t :=
  convexSegEval_le_meet_breakpointThetas f0 fs segs t

/-- **[4.13]: `Ω_f̲` samples `f̲` exactly at each breakpoint.** At a non-differentiable point
`τ ∈ breakpoints` the upper bound equals the corner value `f̲(τ)` — the generators pin `Ω_f̲` to
the curve at the breakpoints. -/
theorem canonicalUpperBound_eq_at_breakpoint (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0))
    {τ : ℝ≥0} (hτ : τ ∈ breakpoints segs) :
    canonicalUpperBound f0 fs segs τ = ((convexSegEval f0 fs segs τ : ℝ≥0) : EReal) :=
  meet_breakpointThetas_eq_at_breakpoint f0 fs segs hτ

/-- **[4.13]: `Ω_f̲ = ⊤` past the rank.** For `pwlRank segs < t` no generator's prefix covers `t`,
so the upper bound is `⊤ = +∞` (the book's `∀ t > tₙ, Ω_f̲(t) = +∞`): the meet of *constant*
elementary functions bounds only the finite region. -/
theorem canonicalUpperBound_eq_top_past_rank (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0))
    {t : ℝ≥0} (ht : pwlRank segs < t) :
    canonicalUpperBound f0 fs segs t = ⊤ :=
  meet_breakpointThetas_eq_top_past_rank f0 fs segs ht

/-- **[4.13]: the first generator is the prefix elementary function `Θ^{κ_f̲}_{τ_f̲}`.** When the
first finite segment has length `ℓ`, the leading breakpoint is `τ₀ = ℓ` with corner value
`κ₀ = ↑f0` (the prefix value `κ_f̲` of `f̲` on `[0, τ_f̲]`): the book's `Θ^{κ₀}_{τ₀} = Θ^{κ_f̲}_{τ_f̲}`.
Here `f̲(τ₀) = f0 + s₀·ℓ`; the prefix value `f0` is recovered as `f̲(0)`. -/
theorem head_breakpointTheta_eq (f0 fs s ℓ : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    (breakpointThetas f0 fs ((s, ℓ) :: rest)).head?
      = some (Theta ((convexSegEval f0 fs ((s, ℓ) :: rest) ℓ : ℝ≥0) : EReal) ℓ) := by
  rw [breakpointThetas, breakpoints_cons, List.map_cons, List.head?_cons]

end DeepWiki
