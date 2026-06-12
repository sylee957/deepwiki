import Book.RealCurvesConv
import Book.RealCurvesDeviations
import Book.DeviationsComposition

/-! # Pay burst only once: the rate-latency delay arithmetic
For a token-bucket arrival `γ_{r,b}` crossing two rate-latency servers
`β_{R₁,T₁}`, `β_{R₂,T₂}`, the per-hop delay bounds are `d₁ = T₁ + b/R₁` and
`d₂ = T₂ + (b + r*T₁)/R₂`, while the concatenation gives
`d = T₁ + T₂ + b/(R₁ ⊓ R₂)`; the per-hop sum exceeds `d` by
`b/(R₁ ⊔ R₂) + r*T₁/R₂`, paying the burst a second time. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Hop-2 delay closed form: the deconvolved arrival `γ_{r,b} ⊘ β_{R₁,T₁}`
has `hDev (γ_{r,b} ⊘ β_{R₁,T₁}) β_{R₂,T₂} = T₂ + (b + r*T₁)/R₂`. -/
theorem hDevENN_minDeconv_tokenBucketNN_rateLatencyNN
    (r b R₁ T₁ R₂ T₂ : ℝ≥0) (hrR₁ : r ≤ R₁) (hT₁ : 0 < T₁)
    (hR₂ : 0 < R₂) (hrR₂ : r ≤ R₂) (hb : 0 < b) :
    hDevENN (minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁))
        (rateLatencyNN R₂ T₂)
      = ((T₂ + (b + r*T₁)/R₂ : ℝ≥0):ℝ≥0∞) := by
  rw [minDeconv_tokenBucketNN_rateLatencyNN r b R₁ T₁ hrR₁ hT₁,
    hDevENN_affine_rateLatencyNN r (b + r*T₁) R₂ T₂ hR₂
      (lt_of_lt_of_le hb le_self_add) hrR₂]

/-- End-to-end delay through the concatenation:
`hDev γ_{r,b} (β_{R₁,T₁} ∗ β_{R₂,T₂}) = T₁ + T₂ + b/(R₁ ⊓ R₂)`. -/
theorem hDevENN_tokenBucketNN_conv_rateLatencyNN
    (r b R₁ T₁ R₂ T₂ : ℝ≥0) (hR₁ : 0 < R₁) (hrR₁ : r ≤ R₁)
    (hR₂ : 0 < R₂) (hrR₂ : r ≤ R₂) (hb : 0 < b) :
    hDevENN (tokenBucketNN r b)
        (minConv (rateLatencyNN R₁ T₁) (rateLatencyNN R₂ T₂))
      = ((T₁ + T₂ + b/(R₁ ⊓ R₂) : ℝ≥0):ℝ≥0∞) := by
  rw [conv_rateLatencyNN_rateLatencyNN R₁ R₂ T₁ T₂,
    hDevENN_tokenBucketNN_rateLatencyNN r b (R₁ ⊓ R₂) (T₁ + T₂)
      (lt_inf_iff.mpr ⟨hR₁, hR₂⟩) hb (le_inf hrR₁ hrR₂)]

/-- The sum of individual delays:
`hDev γ_{r,b} β_{R₁,T₁} + hDev (γ_{r,b} ⊘ β_{R₁,T₁}) β_{R₂,T₂}
= T₁ + T₂ + b/R₁ + b/R₂ + r*T₁/R₂` — the burst is paid at both hops. -/
theorem hDevENN_tokenBucketNN_rateLatencyNN_add_minDeconv
    (r b R₁ T₁ R₂ T₂ : ℝ≥0) (hR₁ : 0 < R₁) (hrR₁ : r ≤ R₁) (hT₁ : 0 < T₁)
    (hR₂ : 0 < R₂) (hrR₂ : r ≤ R₂) (hb : 0 < b) :
    hDevENN (tokenBucketNN r b) (rateLatencyNN R₁ T₁)
        + hDevENN (minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁))
            (rateLatencyNN R₂ T₂)
      = ((T₁ + T₂ + b/R₁ + b/R₂ + r*T₁/R₂ : ℝ≥0):ℝ≥0∞) := by
  rw [hDevENN_tokenBucketNN_rateLatencyNN r b R₁ T₁ hR₁ hb hrR₁,
    hDevENN_minDeconv_tokenBucketNN_rateLatencyNN r b R₁ T₁ R₂ T₂
      hrR₁ hT₁ hR₂ hrR₂ hb,
    ← ENNReal.coe_add, ENNReal.coe_inj, add_div]
  ring

/-- The per-hop sum against the concatenation route: the sum of individual
delays exceeds the end-to-end delay by `b/(R₁ ⊔ R₂) + r*T₁/R₂` — one extra
burst term and one order-dependent term. -/
theorem hDevENN_tokenBucketNN_rateLatencyNN_add_minDeconv_eq_conv_add
    (r b R₁ T₁ R₂ T₂ : ℝ≥0) (hR₁ : 0 < R₁) (hrR₁ : r ≤ R₁) (hT₁ : 0 < T₁)
    (hR₂ : 0 < R₂) (hrR₂ : r ≤ R₂) (hb : 0 < b) :
    hDevENN (tokenBucketNN r b) (rateLatencyNN R₁ T₁)
        + hDevENN (minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁))
            (rateLatencyNN R₂ T₂)
      = hDevENN (tokenBucketNN r b)
            (minConv (rateLatencyNN R₁ T₁) (rateLatencyNN R₂ T₂))
          + ((b/(R₁ ⊔ R₂) + r*T₁/R₂ : ℝ≥0):ℝ≥0∞) := by
  rw [hDevENN_tokenBucketNN_rateLatencyNN_add_minDeconv r b R₁ T₁ R₂ T₂
      hR₁ hrR₁ hT₁ hR₂ hrR₂ hb,
    hDevENN_tokenBucketNN_conv_rateLatencyNN r b R₁ T₁ R₂ T₂
      hR₁ hrR₁ hR₂ hrR₂ hb,
    ← ENNReal.coe_add, ENNReal.coe_inj]
  rcases le_total R₁ R₂ with h | h
  · rw [inf_eq_left.mpr h, sup_eq_right.mpr h]; ring
  · rw [inf_eq_right.mpr h, sup_eq_left.mpr h]; ring

/-! ## Book restatement (quantifying pay burst only once)
With rate-latency services `βᵢ = β_{Rᵢ,Tᵢ}` and token-bucket arrival
`α = γ_{r,b}` (`r ≤ Rᵢ`): `d₁ = hDev(α, β₁) = T₁ + b/R₁`, the deconvolution
is `α ⊘ β₁ = affine r (b+rT₁)` with closure `α' = (α ⊘ β₁)* = γ_{r,b+rT₁}`,
and `d₂ = hDev(α', β₂) = T₂ + (b+rT₁)/R₂`, so the sum of individual delays
is `d₁ + d₂ = T₁ + T₂ + b/R₁ + b/R₂ + rT₁/R₂`. The concatenation offers
`β₁ ∗ β₂ = β_{R₁⊓R₂, T₁+T₂}`, leading to
`d = hDev(α, β₁ ∗ β₂) = T₁ + T₂ + b/(R₁ ⊓ R₂)`, and
`d₁ + d₂ = d + b/(R₁ ⊔ R₂) + rT₁/R₂`: computing the delay through the
concatenation pays only one burst term. -/

example {r b R₁ T₁ : ℝ≥0} (hR₁ : 0 < R₁) (hrR₁ : r ≤ R₁) (hb : 0 < b) :
    hDevENN (tokenBucketNN r b) (rateLatencyNN R₁ T₁)
      = ((T₁ + b/R₁ : ℝ≥0):ℝ≥0∞) :=
  hDevENN_tokenBucketNN_rateLatencyNN r b R₁ T₁ hR₁ hb hrR₁

example {r b R₁ T₁ : ℝ≥0} (hrR₁ : r ≤ R₁) (hT₁ : 0 < T₁) :
    minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁)
      = affine r (b + r*T₁) :=
  minDeconv_tokenBucketNN_rateLatencyNN r b R₁ T₁ hrR₁ hT₁

example {r b R₁ T₁ : ℝ≥0} (hrR₁ : r ≤ R₁) (hT₁ : 0 < T₁) :
    subadditiveClosureENN
        (minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁))
      = tokenBucketNN r (b + r*T₁) :=
  subadditiveClosureENN_minDeconv_tokenBucketNN_rateLatencyNN
    r b R₁ T₁ hrR₁ hT₁

example {r b R₁ T₁ R₂ T₂ : ℝ≥0} (hrR₁ : r ≤ R₁) (hT₁ : 0 < T₁)
    (hR₂ : 0 < R₂) (hrR₂ : r ≤ R₂) (hb : 0 < b) :
    hDevENN (subadditiveClosureENN
        (minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁)))
        (rateLatencyNN R₂ T₂)
      = ((T₂ + (b + r*T₁)/R₂ : ℝ≥0):ℝ≥0∞) := by
  rw [subadditiveClosureENN_minDeconv_tokenBucketNN_rateLatencyNN
      r b R₁ T₁ hrR₁ hT₁,
    hDevENN_tokenBucketNN_rateLatencyNN r (b + r*T₁) R₂ T₂ hR₂
      (lt_of_lt_of_le hb le_self_add) hrR₂]

example {r b R₁ T₁ R₂ T₂ : ℝ≥0} (hrR₁ : r ≤ R₁) (hT₁ : 0 < T₁)
    (hR₂ : 0 < R₂) (hrR₂ : r ≤ R₂) (hb : 0 < b) :
    hDevENN (minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁))
        (rateLatencyNN R₂ T₂)
      = ((T₂ + (b + r*T₁)/R₂ : ℝ≥0):ℝ≥0∞) :=
  hDevENN_minDeconv_tokenBucketNN_rateLatencyNN r b R₁ T₁ R₂ T₂
    hrR₁ hT₁ hR₂ hrR₂ hb

example {r b R₁ T₁ R₂ T₂ : ℝ≥0} (hR₁ : 0 < R₁) (hrR₁ : r ≤ R₁)
    (hT₁ : 0 < T₁) (hR₂ : 0 < R₂) (hrR₂ : r ≤ R₂) (hb : 0 < b) :
    hDevENN (tokenBucketNN r b) (rateLatencyNN R₁ T₁)
        + hDevENN (minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁))
            (rateLatencyNN R₂ T₂)
      = ((T₁ + T₂ + b/R₁ + b/R₂ + r*T₁/R₂ : ℝ≥0):ℝ≥0∞) :=
  hDevENN_tokenBucketNN_rateLatencyNN_add_minDeconv r b R₁ T₁ R₂ T₂
    hR₁ hrR₁ hT₁ hR₂ hrR₂ hb

example {R₁ T₁ R₂ T₂ : ℝ≥0} :
    minConv (rateLatencyNN R₁ T₁) (rateLatencyNN R₂ T₂)
      = rateLatencyNN (R₁ ⊓ R₂) (T₁ + T₂) :=
  conv_rateLatencyNN_rateLatencyNN R₁ R₂ T₁ T₂

example {r b R₁ T₁ R₂ T₂ : ℝ≥0} (hR₁ : 0 < R₁) (hrR₁ : r ≤ R₁)
    (hR₂ : 0 < R₂) (hrR₂ : r ≤ R₂) (hb : 0 < b) :
    hDevENN (tokenBucketNN r b)
        (minConv (rateLatencyNN R₁ T₁) (rateLatencyNN R₂ T₂))
      = ((T₁ + T₂ + b/(R₁ ⊓ R₂) : ℝ≥0):ℝ≥0∞) :=
  hDevENN_tokenBucketNN_conv_rateLatencyNN r b R₁ T₁ R₂ T₂
    hR₁ hrR₁ hR₂ hrR₂ hb

example {r b R₁ T₁ R₂ T₂ : ℝ≥0} (hR₁ : 0 < R₁) (hrR₁ : r ≤ R₁)
    (hT₁ : 0 < T₁) (hR₂ : 0 < R₂) (hrR₂ : r ≤ R₂) (hb : 0 < b) :
    hDevENN (tokenBucketNN r b) (rateLatencyNN R₁ T₁)
        + hDevENN (minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁))
            (rateLatencyNN R₂ T₂)
      = hDevENN (tokenBucketNN r b)
            (minConv (rateLatencyNN R₁ T₁) (rateLatencyNN R₂ T₂))
          + ((b/(R₁ ⊔ R₂) + r*T₁/R₂ : ℝ≥0):ℝ≥0∞) :=
  hDevENN_tokenBucketNN_rateLatencyNN_add_minDeconv_eq_conv_add
    r b R₁ T₁ R₂ T₂ hR₁ hrR₁ hT₁ hR₂ hrR₂ hb

example {r b R₁ T₁ R₂ T₂ : ℝ≥0} :
    hDevENN (tokenBucketNN r b)
        (minConv (rateLatencyNN R₁ T₁) (rateLatencyNN R₂ T₂))
      ≤ hDevENN (tokenBucketNN r b) (rateLatencyNN R₁ T₁)
        + hDevENN (minDeconv (tokenBucketNN r b) (rateLatencyNN R₁ T₁))
            (rateLatencyNN R₂ T₂) :=
  hDev_minConv_le_add_hDev_minDeconv (tokenBucketNN_mono r b)
    (rateLatencyNN_mono R₁ T₁) (rateLatencyNN_mono R₂ T₂)

end DeepWiki
