import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstant
import DeepWiki.NetworkCalculus.RealCurvesDeconv

/-! # Grounding the §12.4.2 scaling burst recursion in the NC machinery
`Stability.exists_scalingFixpointPair_iff` takes the §12.4.2 coupled burst system
`σ'₁ = 1 + m₄σ'₂/(1−m₄)`, `σ'₂ = 1 + m₂σ'₁/(1−m₂)` as an abstract fix-point. Here that recursion is
*derived* from the actual network-calculus operations of the book's Figure 12.5 cyclic scaling
network, for one flow's hop: the **residual** of the rate-`1` server under its scaled cross-traffic is
a reduced-rate rate-latency (Lemma 12.6 / blind multiplexing), and the **output** of the scaled flow
through that residual is a token-bucket whose descaled burst is exactly `1 + m₄σ/(1−m₄)` (Theorem 7.1,
output `= input ⊘ service`). The flow's scaling `m₁` cancels under the descaling `1/m₁` — which is why
the recursion sees only the cross-scalings `m₂, m₄` — and `m₁ ≤ 1 − m₄` is precisely the local
stability of the hop. -/

namespace DeepWiki

open scoped NNReal ENNReal

/-- **The §12.4.2 residual (Lemma 12.6 / blind multiplexing)**: the residual of the rate-`1` server
`λ₁ = β_{1,0}` under scaled cross-traffic `m₄·γ_{1,σ}` (affine `v ↦ m₄v + m₄σ`) is the reduced-rate
rate-latency `β_{1−m₄, m₄σ/(1−m₄)}` — the latency `m₄σ/(1−m₄)` is the burst the cross-flow imposes. -/
theorem scalingResidual_rateLatency {m4 σ : ℝ≥0} (h4 : m4 < 1) :
    residualCurve (rateLatency 1 0) (fun v => m4 * v + m4 * σ)
      = rateLatency (1 - m4) (m4 * σ / (1 - m4)) := by
  rw [residualCurve_rateLatency_affine 1 0 m4 (m4 * σ) h4, mul_zero, zero_add]

/-- **The §12.4.2 burst recursion, grounded (Theorem 7.1 output)**: the descaled output of the scaled
flow `m₁·γ_{1,1}` through its residual rate-latency `β_{1−m₄, m₄σ/(1−m₄)}` is the token-bucket curve
`t ↦ t + (1 + m₄σ/(1−m₄))`, i.e. rate `1`, burst `σ'₁ = 1 + m₄σ/(1−m₄)`. The output arrival is
`input ⊘ service = γ_{m₁, m₁ + m₁·m₄σ/(1−m₄)}` (`minDeconv_tokenBucketNN_rateLatencyNN`, valid since
`m₁ ≤ 1−m₄` is local stability), and the descaling `1/m₁` cancels `m₁`, leaving the recursion's
right-hand side. So the abstract `σ'₁`-equation of `exists_scalingFixpointPair_iff` *is* the per-flow
output burstiness. -/
theorem descaledOutputBurst_scalingResidual {m1 m4 σ : ℝ≥0}
    (hm1 : 0 < m1) (hm4 : 0 < m4) (h4 : m4 < 1) (hσ : 0 < σ) (hstab : m1 ≤ 1 - m4) (t : ℝ≥0) :
    (↑(1 / m1) : ℝ≥0∞) *
        minDeconv (tokenBucketNN m1 m1) (rateLatencyNN (1 - m4) (m4 * σ / (1 - m4))) t
      = affine 1 (1 + m4 * σ / (1 - m4)) t := by
  set T : ℝ≥0 := m4 * σ / (1 - m4) with hTdef
  have hT : (0 : ℝ≥0) < T := by rw [hTdef]; exact div_pos (mul_pos hm4 hσ) (tsub_pos_of_lt h4)
  rw [minDeconv_tokenBucketNN_rateLatencyNN m1 m1 (1 - m4) T hstab hT]
  simp only [affine_coe]
  rw [← ENNReal.coe_mul, ENNReal.coe_inj, ← NNReal.coe_inj]
  have hm1' : (m1 : ℝ) ≠ 0 := by exact_mod_cast hm1.ne'
  push_cast
  field_simp

/-- **The grounded burstiness equals the fix-point map value** (evaluate the output curve at the
origin): the descaled output burst is `1 + m₄σ/(1−m₄)`, the right-hand side of the `σ'₁`-equation in
`exists_scalingFixpointPair_iff`. The §12.4.2 coupled fix-point is the inter-server burstiness
recursion, now read off the genuine NC output operation rather than postulated. -/
theorem descaledOutputBurst_zero {m1 m4 σ : ℝ≥0}
    (hm1 : 0 < m1) (hm4 : 0 < m4) (h4 : m4 < 1) (hσ : 0 < σ) (hstab : m1 ≤ 1 - m4) :
    (↑(1 / m1) : ℝ≥0∞) *
        minDeconv (tokenBucketNN m1 m1) (rateLatencyNN (1 - m4) (m4 * σ / (1 - m4))) 0
      = ((1 + m4 * σ / (1 - m4) : ℝ≥0) : ℝ≥0∞) := by
  rw [descaledOutputBurst_scalingResidual hm1 hm4 h4 hσ hstab 0, affine_coe, mul_zero, zero_add]

end DeepWiki
