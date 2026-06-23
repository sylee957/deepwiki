import DeepWiki.NetworkCalculus.WorstCaseLPTandemChain
import DeepWiki.NetworkCalculus.WorstCaseLPInstance

/-! # The exact heterogeneous tandem worst-case delay in closed form
The arbitrary-length single-flow tandem with a token-bucket source `γ_{r,b}` and
*heterogeneous* rate-latency servers `β_{Rₕ,Tₕ}`.  The chain convolution of
rate-latency curves collapses to a single rate-latency curve at the **minimum
rate** and **sum latency** (`minConvChain_rateLatencyNN`):
`β_{R₀,T₀} ∗ β_{R₁,T₁} ∗ ⋯ ∗ β_{Rₙ,Tₙ} = β_{minₕRₕ, ∑ₕTₕ}`.  Feeding this through
the chain worst-case theorem `worstCaseChainDelay_eq_hDev_minConvChain` and the
deviation closed form `hDevENN_tokenBucketNN_rateLatencyNN` (`T + b/R`) gives the
**exact** worst-case end-to-end delay of the heterogeneous tandem as the explicit
closed form `(∑ₕ Tₕ) + b/(minₕ Rₕ)` — no homogeneity assumption, the true tight
value (unlike the SFA bottleneck objective `objectiveValue`, which over-estimates a
heterogeneous tandem). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-! ## The chain convolution of rate-latency curves -/

/-- The `⊓`-fold accumulator commutes with the head value: `foldr ⊓ a ps` swaps `a`
out front (`⊓` is commutative and associative, so the initial accumulator commutes
through the fold). -/
private theorem foldr_inf_init_comm (a b : ℝ≥0) (ps : List (ℝ≥0 × ℝ≥0)) :
    a ⊓ ps.foldr (fun p R => p.1 ⊓ R) b
      = b ⊓ ps.foldr (fun p R => p.1 ⊓ R) a := by
  induction ps with
  | nil => exact inf_comm a b
  | cons q qs ih =>
    simp only [List.foldr_cons]
    rw [inf_left_comm a q.1, ih, inf_left_comm b q.1]

/-- **The chain convolution of rate-latency curves is a single rate-latency curve**
at the **minimum rate** and **sum latency**:
`β_{R₀,T₀} ∗ β_{R₁,T₁} ∗ ⋯ = β_{R₀ ⊓ minₕRₕ, T₀ + ∑ₕTₕ}`.  Inductive iteration of
the two-curve law `conv_rateLatencyNN_rateLatencyNN` along the chain, the rates
meeting under `⊓` (associativity/commutativity collapse to a `List.foldr min`) and
the latencies summing. -/
theorem minConvChain_rateLatencyNN (R₀ T₀ : ℝ≥0) (ps : List (ℝ≥0 × ℝ≥0)) :
    minConvChain (rateLatencyNN R₀ T₀)
        (ps.map (fun p => rateLatencyNN p.1 p.2))
      = rateLatencyNN (ps.foldr (fun p R => p.1 ⊓ R) R₀)
          (T₀ + (ps.map Prod.snd).sum) := by
  induction ps generalizing R₀ T₀ with
  | nil => simp
  | cons p rest ih =>
    rw [List.map_cons, minConvChain_cons, ih p.1 p.2]
    rw [conv_rateLatencyNN_rateLatencyNN]
    have hlat : T₀ + (p.2 + (rest.map Prod.snd).sum)
        = T₀ + ((p :: rest).map Prod.snd).sum := by
      simp only [List.map_cons, List.sum_cons]
    rw [hlat]
    congr 1
    simp only [List.foldr_cons]
    exact foldr_inf_init_comm R₀ p.1 rest

/-! ## The exact heterogeneous tandem worst-case delay -/

/-- **Exact worst-case delay of a heterogeneous tandem** (the true tight value,
no homogeneity).  A token-bucket flow `γ_{r,b}` (`b > 0`) crossing the rate-latency
tandem `β_{R₀,T₀} :: [β_{R₁,T₁}, …]` has worst-case end-to-end delay exactly
`(T₀ + ∑ₕ Tₕ) + b / (R₀ ⊓ minₕ Rₕ)` over **all** feasible trajectories: the chain
collapses to `β_{minR,∑T}` (`minConvChain_rateLatencyNN`) and its deviation against
the token bucket is the textbook `T + b/R` (`hDevENN_tokenBucketNN_rateLatencyNN`).
Generalizes the two-server `worstCaseTandemDelay_tokenBucketNN_rateLatencyNN`; the
exact value is the chain `hDev`, *not* the SFA bottleneck objective. -/
theorem worstCaseChainDelay_tokenBucketNN_rateLatencyNN (r b R₀ T₀ : ℝ≥0)
    (ps : List (ℝ≥0 × ℝ≥0)) (hb : 0 < b)
    (hRmin : 0 < ps.foldr (fun p R => p.1 ⊓ R) R₀)
    (hrR : r ≤ ps.foldr (fun p R => p.1 ⊓ R) R₀) :
    worstCaseChainDelay (tokenBucketArrival r b) (rateLatencyNN R₀ T₀)
        (ps.map (fun p => rateLatencyNN p.1 p.2))
      = (((T₀ + (ps.map Prod.snd).sum) + b / (ps.foldr (fun p R => p.1 ⊓ R) R₀)
          : ℝ≥0) : ℝ≥0∞) := by
  rw [worstCaseChainDelay_eq_hDev_minConvChain (tokenBucketArrival_mono r b)
      (tokenBucketArrival_nullAtOrigin r b) (tokenBucketArrival_subadditive r b)
      (rateLatencyNN_mono R₀ T₀)
      (fun γ hγ => by
        obtain ⟨p, _, hp⟩ := List.mem_map.mp hγ
        exact hp ▸ rateLatencyNN_mono p.1 p.2)
      (rateLatencyNN_zero_eq R₀ T₀)
      (fun γ hγ => by
        obtain ⟨p, _, hp⟩ := List.mem_map.mp hγ
        exact hp ▸ rateLatencyNN_zero_eq p.1 p.2),
    liftENN_tokenBucketArrival, minConvChain_rateLatencyNN]
  exact hDevENN_tokenBucketNN_rateLatencyNN r b _ _ hRmin hb hrR

/-! ## Restatements (the theorems say what the book says) -/

-- The chain convolution of three rate-latency curves is `β` at the min rate, sum latency.
example (R₀ T₀ R₁ T₁ R₂ T₂ : ℝ≥0) :
    minConvChain (rateLatencyNN R₀ T₀) [rateLatencyNN R₁ T₁, rateLatencyNN R₂ T₂]
      = rateLatencyNN (R₁ ⊓ (R₂ ⊓ R₀)) (T₀ + (T₁ + T₂)) := by
  have := minConvChain_rateLatencyNN R₀ T₀ [(R₁, T₁), (R₂, T₂)]
  simpa using this

-- Exact heterogeneous two-server worst-case delay: `(T₀+T₁) + b/(R₁⊓R₀)`, no homogeneity.
example (r b R₀ T₀ R₁ T₁ : ℝ≥0) (hb : 0 < b) (hRmin : 0 < R₁ ⊓ R₀) (hrR : r ≤ R₁ ⊓ R₀) :
    worstCaseChainDelay (tokenBucketArrival r b) (rateLatencyNN R₀ T₀)
        [rateLatencyNN R₁ T₁]
      = (((T₀ + T₁) + b / (R₁ ⊓ R₀) : ℝ≥0) : ℝ≥0∞) := by
  have := worstCaseChainDelay_tokenBucketNN_rateLatencyNN r b R₀ T₀ [(R₁, T₁)] hb
    (by simpa using hRmin) (by simpa using hrR)
  simpa using this

end DeepWiki
