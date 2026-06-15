import DeepWiki.NetworkCalculus.ServersResidualTdma
import DeepWiki.NetworkCalculus.DeviationsBoundsServerRateLatency

/-! # A rate-latency lower bound for the TDMA residual; per-flow delay / backlog under TDMA
The TDMA residual `tdmaResidual c o T R = ν_{c,o,−T} ∗ λ_R` is a *staircase*, not rate-latency, but
it dominates the rate-latency `β_{min(o/c, R), T}` (`rateLatency_le_tdmaResidual`): the ceiling
staircase exceeds its long-term rate `o/c` and the line `λ_R` is rate `R`, so each convolution split
clears `min(o/c, R)`. A smaller curve is still a strict service curve
(`IsStrictMinimalServiceCurve.mono`), so a flow served by TDMA with token-bucket input below its
share rate has finite delay and backlog (via the server bounds). -/

namespace DeepWiki

open scoped NNReal ENNReal BigOperators

/-- **A rate-latency lower bound for the TDMA residual**: `β_{min(o/c, R), T} ≤ tdmaResidual c o T R`.
Each convolution split `a + b = τ` clears at least `min(o/c, R)·(τ − T)`: the delayed ceiling
staircase clears `(o/c)(a − T)` (`rateLatency_le_staircaseFun`) and the line clears `R·b`. -/
theorem rateLatency_le_tdmaResidual (c o T R : ℝ≥0) :
    rateLatency (min (o / c) R) T ≤ tdmaResidual c o T R := by
  intro τ
  rw [tdmaResidual_apply]
  refine le_minConv fun a b hab => ?_
  refine le_trans ?_ (add_le_add (rateLatency_le_staircaseFun c o T a) (le_refl (rate R b)))
  rw [rate_apply]
  show min (o / c) R * (τ - T) ≤ o / c * (a - T) + R * b
  subst hab
  rcases le_or_gt T a with hTa | hTa
  · have hsplit : a + b - T = (a - T) + b := by
      rw [add_comm a b, add_tsub_assoc_of_le hTa, add_comm]
    rw [hsplit, mul_add]
    gcongr
    · exact min_le_left _ _
    · exact min_le_right _ _
  · rw [tsub_eq_zero_of_le hTa.le, mul_zero, zero_add]
    have hab_le : a + b - T ≤ b := by
      rw [tsub_le_iff_right, add_comm a b]; exact add_le_add_right hTa.le b
    calc min (o / c) R * (a + b - T) ≤ R * (a + b - T) := by gcongr; exact min_le_right _ _
      _ ≤ R * b := by gcongr

/-- **Per-flow delay under TDMA**: a flow `i` served by a TDMA server (cycle `c`, quantum `oᵢ`,
latency `Tᵢ`, line rate `R`) with token-bucket input `γ_{r,b}`, `r` below its share rate
`min(oᵢ/c, R)`, has finite virtual delay. The TDMA residual dominates `β_{min(oᵢ/c,R), Tᵢ}`, which is
therefore a strict service curve for flow `i`. -/
theorem isFlowDelayBounded_tdma {ι : Type*} {S : (ι → Curve) → (ι → Curve) → Prop}
    {c R : ℝ≥0} {o T : ι → ℝ≥0} {i : ι} {Ai Di : Curve} {r b : ℝ≥0}
    (hcaus : IsCausalN S) (htdma : IsTdmaServerN c o T R S) (hp : residualServer S i Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hr : r ≤ min (o i / c) R) (hR' : 0 < min (o i / c) R) :
    ∃ d : ℝ≥0, Deviation.delay (⇑Ai) (⇑Di) ≤ (d : ℝ≥0∞) := by
  have hstrict := (isStrictMinimalServiceCurve_tdmaResidual_of_isTdma htdma (i := i)).mono
    (rateLatency_le_tdmaResidual c (o i) (T i) R)
  exact ⟨_, delay_le_of_strictRateLatency_affine (isCausal_residualServer hcaus i) hstrict hp harr
    hR' hr⟩

/-- **Per-flow backlog under TDMA**: the same flow has finite backlog. -/
theorem isFlowBacklogBounded_tdma {ι : Type*} {S : (ι → Curve) → (ι → Curve) → Prop}
    {c R : ℝ≥0} {o T : ι → ℝ≥0} {i : ι} {Ai Di : Curve} {r b : ℝ≥0}
    (hcaus : IsCausalN S) (htdma : IsTdmaServerN c o T R S) (hp : residualServer S i Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hr : r ≤ min (o i / c) R) :
    ∃ cc : ℝ≥0, Deviation.backlog (⇑Ai) (⇑Di) ≤ (cc : ℝ≥0∞) := by
  have hstrict := (isStrictMinimalServiceCurve_tdmaResidual_of_isTdma htdma (i := i)).mono
    (rateLatency_le_tdmaResidual c (o i) (T i) R)
  exact ⟨_, backlog_le_of_strictRateLatency_affine (isCausal_residualServer hcaus i) hstrict hp harr
    hr⟩

end DeepWiki
