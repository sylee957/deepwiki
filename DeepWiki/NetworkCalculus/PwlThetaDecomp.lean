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

/-! ## Convex side — the sup of rate-latencies (`convexNFEval`), the `≤` inclusion

The convex representative `f̲` itself is the pointwise supremum of rate-latency curves; this is
the dual of [4.13]'s `Θ`-meet. Each generator is anchored at a breakpoint `τ` with slope `p` no
larger than every slope of `f̲` from `τ` on, so `β_{p, τ}(t) = p·(t − τ)₊` lies below `f̲`. -/

/-- **A breakpoint-anchored rate-latency lies below the convex PWL.** If the slope `p` is `≤` every
finite slope of `convexSegEval f0 fs segs` and `≤` its asymptotic slope `fs`, then the rate-latency
`β_{p, T}(t) = p·(t − T)₊` is `≤ ↑(f̲(t))` everywhere: before `T` the generator is `0`, and from
`T` on `f̲` grows at rate `≥ p` off a non-negative base (`convexSegEval_rate_of_le`). -/
theorem rateLatencyEReal_le_convexSegEval (f0 fs p T : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0))
    (hall : ∀ seg ∈ segs, p ≤ seg.1) (hfs : p ≤ fs) (t : ℝ≥0) :
    rateLatencyEReal p T t ≤ (((convexSegEval f0 fs segs t : ℝ≥0) : ℝ) : EReal) := by
  rw [rateLatencyEReal_apply, EReal.coe_le_coe_iff, NNReal.coe_le_coe]
  -- reduce the `EReal` comparison to the underlying `ℝ≥0` order
  rcases le_or_gt t T with hle | hlt
  · -- before the latency the generator is `p·0 = 0 ≤ f̲(t)`
    rw [tsub_eq_zero_of_le hle, mul_zero]
    exact bot_le
  · -- from `T` on: `p·(t − T) ≤ f̲(T) + p·(t − T) ≤ f̲(t)`
    have hrate : convexSegEval f0 fs segs T + p * (t - T)
        ≤ convexSegEval f0 fs segs (T + (t - T)) :=
      convexSegEval_rate_of_le hall hfs T (t - T)
    rw [add_tsub_cancel_of_le hlt.le] at hrate
    calc p * (t - T) ≤ convexSegEval f0 fs segs T + p * (t - T) := le_add_self
      _ ≤ convexSegEval f0 fs segs t := hrate

/-- **The convex sup-of-rate-latencies lies below the curve (the `≤` inclusion of [4.13]'s convex
companion).** If every generator `(Rᵢ, Tᵢ)` in `gens` has rate `Rᵢ` no larger than every finite
slope of `convexSegEval f0 fs segs` and no larger than its asymptotic slope `fs`, then the convex
normal form `convexNFEval gens = ⨆ᵢ β_{Rᵢ, Tᵢ}` is `≤ ↑(f̲)` everywhere. (Each generator lies
below `f̲` by `rateLatencyEReal_le_convexSegEval`, hence so does their supremum.) -/
theorem convexNFEval_le_convexSegEval (f0 fs : ℝ≥0) (segs gens : List (ℝ≥0 × ℝ≥0))
    (hrate : ∀ g ∈ gens, ∀ seg ∈ segs, g.1 ≤ seg.1) (hfs : ∀ g ∈ gens, g.1 ≤ fs) (t : ℝ≥0) :
    convexNFEval gens t ≤ (((convexSegEval f0 fs segs t : ℝ≥0) : ℝ) : EReal) := by
  induction gens with
  | nil => rw [convexNFEval_nil]; exact bot_le
  | cons g gs ih =>
      rw [convexNFEval_cons]
      apply sup_le
      · exact rateLatencyEReal_le_convexSegEval f0 fs g.1 g.2 segs
          (fun seg hseg => hrate g List.mem_cons_self seg hseg)
          (hfs g List.mem_cons_self) t
      · exact ih (fun g' hg' seg hseg => hrate g' (List.mem_cons_of_mem _ hg') seg hseg)
          (fun g' hg' => hfs g' (List.mem_cons_of_mem _ hg'))

/-! ### The asymptotic tangent rate-latency — exact equality past the rank

For a convex PWL null at the origin (`f0 = 0`) with positive asymptotic slope `fs`, the
rate-latency anchored at the *asymptotic tangent latency* `T∞ = u* − f̲(u*)/fs` (where `u*` is the
rank) coincides with `f̲` past the rank and lies below it before — the single sloped generator that
carries the asymptote, which [4.13]'s constant `Θ`-meet (`= ⊤` past the rank) cannot. -/

/-- **The asymptotic-tangent latency is well-defined and `≤` the rank.** For `f0 = 0` and positive
`fs`, `f̲(u*)/fs ≤ u*` (since `cornerSum ≤ fs·segLenSum`), so the tangent of the asymptote crosses
zero at an abscissa `T∞ = u* − f̲(u*)/fs ≥ 0` no later than the rank `u* = pwlRank segs`. -/
theorem asymptoteTangentLatency_le_rank (fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0))
    (hall : ∀ seg ∈ segs, seg.1 ≤ fs) :
    (convexSegEval 0 fs segs (pwlRank segs) : ℝ) ≤ (fs : ℝ) * (pwlRank segs : ℝ) := by
  rw [convexSegEval_pwlRank, zero_add]
  -- `cornerSum = Σ sᵢ·ℓᵢ ≤ Σ fs·ℓᵢ = fs · segLenSum = fs · pwlRank`
  have hcs : (cornerSum segs : ℝ) ≤ (fs : ℝ) * (segLenSum segs : ℝ) := by
    induction segs with
    | nil => simp
    | cons hd tl ih =>
        obtain ⟨s, ℓ⟩ := hd
        have hsfs : (s : ℝ) ≤ (fs : ℝ) := by
          exact_mod_cast hall (s, ℓ) List.mem_cons_self
        have htl : ∀ seg ∈ tl, seg.1 ≤ fs := fun seg h => hall seg (List.mem_cons_of_mem _ h)
        rw [cornerSum_cons, segLenSum_cons]
        push_cast
        have : (s : ℝ) * ℓ ≤ (fs : ℝ) * ℓ := by
          apply mul_le_mul_of_nonneg_right hsfs ℓ.coe_nonneg
        calc (s : ℝ) * ℓ + cornerSum tl
            ≤ (fs : ℝ) * ℓ + (fs : ℝ) * segLenSum tl := by
              exact add_le_add this (ih htl)
          _ = (fs : ℝ) * (ℓ + segLenSum tl) := by ring
  rw [pwlRank]; exact hcs

end DeepWiki
