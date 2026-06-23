import DeepWiki.NetworkCalculus.ServersResidualPmooRateLatency
import DeepWiki.NetworkCalculus.ServersResidualSpPmoo

/-! # SP-PMOO on the nested tandem (worked example)
The nested tandem at the bottom of Figure 10.1: three servers `1 → 2 → 3`,
with flow `1` on `{2}`, flow `2` on `{1,2}`, flow `3` on `{1,2,3}` — the paths
nest, `p₁ ⊆ p₂ ⊆ p₃`. The PMOO-for-static-priority algorithm peels the flows
from the innermost out, paying each cross-flow's burst only once. With the
arrival curves `α₁, α₂` of the inner flows and the per-server strict service
curves `β⁽¹⁾, β⁽²⁾, β⁽³⁾`, the residual service curves are
`β̃₁ = β⁽²⁾`,
`β̃₂ = β⁽¹⁾ ∗ [β̃₁ − α₁]⁺↑ = β⁽¹⁾ ∗ [β⁽²⁾ − α₁]⁺↑`,
`β̃₃ = [β̃₂ − α₂]⁺↑ ∗ β⁽³⁾ = [β⁽¹⁾ ∗ [β⁽²⁾ − α₁]⁺↑ − α₂]⁺↑ ∗ β⁽³⁾`,
where `[· − α]⁺↑ = residualCurve · α` is the non-decreasing closure of the
clamped difference and `∗ = minConvProj` the min-plus convolution.

This file fixes the recursion as definitions (`nestedBeta₁/₂/₃`), proves the
book's substituted forms, and works the closed form for identical rate-latency
servers `β_{R,T}` and affine (token-bucket) inner arrivals `γ_{r₁,b₁}`,
`γ_{r₂,b₂}` — `β̃₃` is again rate-latency. -/

namespace DeepWiki

open scoped NNReal

/-! ## The nested-tandem SP-PMOO recursion (peeling inner flows out)
For a three-server nested tandem with per-server service curves `β₁,β₂,β₃` and
inner-flow arrivals `α₁` (flow on `{1,2}`) and `α₂` (flow on `{1,2}`), the
service curves of the three flows, computed innermost-first. The full path
flow `3` gets `β̃₃`. -/

/-- `β̃₁ = β⁽²⁾`: the innermost flow (on `{2}`) sees only server `2`. -/
noncomputable def nestedBeta₁ (β₂ : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 := β₂

/-- `β̃₂ = β⁽¹⁾ ∗ [β̃₁ − α₁]⁺↑`: flow `2` (on `{1,2}`) convolves server `1`'s
curve with the residual of `β̃₁` after removing the inner flow `1`. -/
noncomputable def nestedBeta₂ (β₁ β₂ α₁ : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  minConvProj β₁ (residualCurve (nestedBeta₁ β₂) α₁)

/-- `β̃₃ = [β̃₂ − α₂]⁺↑ ∗ β⁽³⁾`: the full-path flow `3` convolves server `3`'s
curve with the residual of `β̃₂` after removing the inner flow `2`. -/
noncomputable def nestedBeta₃ (β₁ β₂ β₃ α₁ α₂ : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  minConvProj (residualCurve (nestedBeta₂ β₁ β₂ α₁) α₂) β₃

/-- `β̃₁ = β⁽²⁾` (the book's first line). -/
theorem nestedBeta₁_eq (β₂ : ℝ≥0 → ℝ≥0) : nestedBeta₁ β₂ = β₂ := rfl

/-- `β̃₂ = β⁽¹⁾ ∗ [β⁽²⁾ − α₁]⁺↑` (substituting `β̃₁ = β⁽²⁾`). -/
theorem nestedBeta₂_eq (β₁ β₂ α₁ : ℝ≥0 → ℝ≥0) :
    nestedBeta₂ β₁ β₂ α₁ = minConvProj β₁ (residualCurve β₂ α₁) := rfl

/-- `β̃₃ = [β⁽¹⁾ ∗ [β⁽²⁾ − α₁]⁺↑ − α₂]⁺↑ ∗ β⁽³⁾` (the book's fully substituted
third line). -/
theorem nestedBeta₃_eq (β₁ β₂ β₃ α₁ α₂ : ℝ≥0 → ℝ≥0) :
    nestedBeta₃ β₁ β₂ β₃ α₁ α₂
      = minConvProj (residualCurve (minConvProj β₁ (residualCurve β₂ α₁)) α₂) β₃ :=
  rfl

/-! ## Worked closed form: identical rate-latency servers, affine arrivals
With `β⁽¹⁾ = β⁽²⁾ = β⁽³⁾ = β_{R,T}` and affine inner arrivals
`α₁ : t ↦ r₁·t + b₁`, `α₂ : t ↦ r₂·t + b₂` (token-buckets away from the
origin), the residual of a rate-latency against an affine is again
rate-latency (`rateLatency_sub_affine`, then `ndClosure_eq_self`), and the
convolution of rate-latency curves is rate-latency (`minConvProj_rateLatency`).
So `β̃₂` and `β̃₃` are rate-latency, computed below. -/

/-- The residual of a rate-latency curve against an affine arrival is again
rate-latency: `[β_{R,T} − (ρ·t + b)]⁺↑ = β_{R−ρ, T + (ρT+b)/(R−ρ)}`
(`rateLatency_sub_affine` is already non-decreasing, so its closure is
itself). -/
theorem residualCurve_rateLatency_affine_splitLatency (R T ρ b : ℝ≥0) (hR : ρ < R) :
    residualCurve (rateLatency R T) (fun t => ρ * t + b)
      = rateLatency (R - ρ) (T + (ρ * T + b) / (R - ρ)) := by
  rw [residualCurve, show (fun v => rateLatency R T v - (ρ * v + b))
      = rateLatency (R - ρ) (T + (ρ * T + b) / (R - ρ)) from
    rateLatency_sub_affine R T ρ b hR]
  exact ndClosure_eq_self (rateLatency_mono _ _)

/-- The effective latency of `β̃₂` for identical rate-latency servers:
`T + (T + (r₁·T + b₁)/(R − r₁))` (server `1` latency plus the inner residual
latency). -/
noncomputable def nestedBeta₂Latency (R T r₁ b₁ : ℝ≥0) : ℝ≥0 :=
  T + (T + (r₁ * T + b₁) / (R - r₁))

/-- **`β̃₂` is rate-latency** `β_{R−r₁, nestedBeta₂Latency}` for identical
rate-latency servers `β_{R,T}` and affine inner arrival `γ_{r₁,b₁}`
(`r₁ < R`). -/
theorem nestedBeta₂_rateLatency (R T r₁ b₁ : ℝ≥0) (hR : r₁ < R) :
    nestedBeta₂ (rateLatency R T) (rateLatency R T) (fun t => r₁ * t + b₁)
      = rateLatency (R - r₁) (nestedBeta₂Latency R T r₁ b₁) := by
  rw [nestedBeta₂_eq, residualCurve_rateLatency_affine_splitLatency R T r₁ b₁ hR,
    minConvProj_rateLatency, nestedBeta₂Latency]
  congr 1
  exact inf_eq_right.mpr tsub_le_self

/-- The bottleneck rate of `β̃₃`: `R − r₁ − r₂` (the slowest of `β̃₂`'s rate
`R − r₁` and server `3`'s residual rate `R − r₂`, both under `R`, with `β̃₂`'s
the smaller once both inner flows are removed). For `r₁ + r₂ < R`. -/
noncomputable def nestedBeta₃Rate (R r₁ r₂ : ℝ≥0) : ℝ≥0 := R - r₁ - r₂

/-- The effective latency of `β̃₃`: `nestedBeta₂Latency + (the inner-2 residual
latency) + T` — the residual of `β̃₂` against `γ_{r₂,b₂}` adds
`(r₂·L₂ + b₂)/(R−r₁−r₂)` (with `L₂ = nestedBeta₂Latency`), then server `3`
adds `T`. -/
noncomputable def nestedBeta₃Latency (R T r₁ b₁ r₂ b₂ : ℝ≥0) : ℝ≥0 :=
  let L₂ := nestedBeta₂Latency R T r₁ b₁
  (L₂ + (r₂ * L₂ + b₂) / ((R - r₁) - r₂)) + T

/-- **`β̃₃` is rate-latency** `β_{R−r₁−r₂, nestedBeta₃Latency}` for identical
rate-latency servers `β_{R,T}` and affine inner arrivals `γ_{r₁,b₁}`,
`γ_{r₂,b₂}`, under stability `r₂ < R − r₁` (so `r₁ + r₂ < R`). This is the
worked end-to-end residual service curve for the full-path flow `3` of the
nested tandem. -/
theorem nestedBeta₃_rateLatency (R T r₁ b₁ r₂ b₂ : ℝ≥0) (hR : r₁ < R)
    (hR₂ : r₂ < R - r₁) :
    nestedBeta₃ (rateLatency R T) (rateLatency R T) (rateLatency R T)
        (fun t => r₁ * t + b₁) (fun t => r₂ * t + b₂)
      = rateLatency (nestedBeta₃Rate R r₁ r₂) (nestedBeta₃Latency R T r₁ b₁ r₂ b₂) := by
  rw [nestedBeta₃, nestedBeta₂_rateLatency R T r₁ b₁ hR,
    residualCurve_rateLatency_affine_splitLatency _ _ r₂ b₂ hR₂,
    minConvProj_rateLatency, nestedBeta₃Rate, nestedBeta₃Latency]
  congr 1
  exact inf_eq_left.mpr (le_trans tsub_le_self tsub_le_self)

/-! ## A numeric instance
`R = 4, T = 1`, inner arrivals `γ_{1,1}` and `γ_{1,1}`: the full-path flow `3`
gets `β̃₃ = β_{2, T₃}` with rate `4 − 1 − 1 = 2`. -/

/-- `β̃₃` for `R = 4, T = 1, r₁ = b₁ = r₂ = b₂ = 1` has bottleneck rate `2`. -/
theorem nestedBeta₃Rate_numeric : nestedBeta₃Rate 4 1 1 = 2 := by
  rw [nestedBeta₃Rate, show (4 : ℝ≥0) = 2 + 1 + 1 from by norm_num,
    add_tsub_cancel_right, add_tsub_cancel_right]

/-! ## Book restatement (Example 10.2)
For the nested tandem at the bottom of Figure 10.1 — flow `1` on `{2}`, flow
`2` on `{1,2}`, flow `3` on `{1,2,3}` — the SP-PMOO algorithm gives flow `3`
the end-to-end residual service curve
`β̃₃ = [β⁽¹⁾ ∗ [β⁽²⁾ − α₁]⁺↑ − α₂]⁺↑ ∗ β⁽³⁾`, paying each inner flow's burst
once as the paths are peeled from the inside out. -/
example (β₁ β₂ β₃ α₁ α₂ : ℝ≥0 → ℝ≥0) :
    nestedBeta₃ β₁ β₂ β₃ α₁ α₂
      = minConvProj (residualCurve (minConvProj β₁ (residualCurve β₂ α₁)) α₂) β₃ :=
  nestedBeta₃_eq β₁ β₂ β₃ α₁ α₂

end DeepWiki
