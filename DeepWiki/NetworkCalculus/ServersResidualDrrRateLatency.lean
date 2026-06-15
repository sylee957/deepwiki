import DeepWiki.NetworkCalculus.ServersResidualDrr
import DeepWiki.NetworkCalculus.ServersResidualPmooRateLatency
import DeepWiki.NetworkCalculus.DeviationsBoundsServerRateLatency

/-! # DRR residual is rate-latency; per-flow delay / backlog under DRR
When the aggregate service is rate-latency `β_{R,T}`, the DRR residual `drrResidual` is again a
rate-latency curve (`drrResidual_rateLatency`): flow `i`'s rate is its quantum share `(Qᵢ/∑Q)·R`,
its latency `T` increased by the round-robin price. Combined with the strict-service guarantee
(`isStrictMinimalServiceCurve_drrResidual_of_isDrr`) and the server delay/backlog bounds, a
token-bucket flow through a DRR server has finite delay and backlog. -/

namespace DeepWiki

open scoped NNReal ENNReal BigOperators

/-- **DRR residual of a rate-latency aggregate is rate-latency**: `drrResidual Q lmax i β_{R,T}` is
`β_{R',T'}` with quantum-share rate `R' = (Qᵢ/∑Q)·R` and latency `T'` = `T` plus the DRR price
divided by `R'` (the price being `[Qᵢ(L−ℓᵢ) + (∑Q−Qᵢ)(Qᵢ+ℓᵢ)]/∑Q`), assuming `0 < R'`. Via
`const_mul_rateLatency` (the share) and `rateLatency_sub_affine` with `ρ = 0` (the constant price). -/
theorem drrResidual_rateLatency {ι : Type*} [Fintype ι] (Q lmax : ι → ℝ≥0) (i : ι) (R T : ℝ≥0)
    (hR' : 0 < (Q i / ∑ j, Q j) * R) :
    drrResidual Q lmax i (rateLatency R T)
      = rateLatency ((Q i / ∑ j, Q j) * R)
          (T + (Q i * ((∑ j, lmax j) - lmax i) + ((∑ j, Q j) - Q i) * (Q i + lmax i)) / (∑ j, Q j)
              / ((Q i / ∑ j, Q j) * R)) := by
  set c : ℝ≥0 := Q i / ∑ j, Q j with hc
  set price : ℝ≥0 :=
    (Q i * ((∑ j, lmax j) - lmax i) + ((∑ j, Q j) - Q i) * (Q i + lmax i)) / (∑ j, Q j) with hprice
  have h1 : drrResidual Q lmax i (rateLatency R T)
      = fun τ => rateLatency (c * R) T τ - (0 * τ + price) := by
    funext τ
    rw [drrResidual_apply, ← hc, ← hprice,
      congrFun (const_mul_rateLatency c R T) τ, zero_mul, zero_add]
  rw [h1, rateLatency_sub_affine (c * R) T 0 price hR', tsub_zero, zero_mul, zero_add]

/-- **Per-flow delay under DRR**: a flow `i` served by a DRR server with rate-latency aggregate
`β_{R,T}`, token-bucket input `γ_{r,b}` with `r` below its quantum-share rate `(Qᵢ/∑Q)·R`, has
finite virtual delay (bounded by `T' + b/R'` of its rate-latency residual). -/
theorem isFlowDelayBounded_drr {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {Q lmax : ι → ℝ≥0} {i : ι} {R T : ℝ≥0}
    {Ai Di : Curve} {r b : ℝ≥0}
    (hcaus : IsCausalN S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) (aggregateServer S))
    (hdrr : IsDrrServerN Q lmax S) (hp : residualServer S i Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hr : r ≤ (Q i / ∑ j, Q j) * R) (hR' : 0 < (Q i / ∑ j, Q j) * R) :
    ∃ d : ℝ≥0, Deviation.delay (⇑Ai) (⇑Di) ≤ (d : ℝ≥0∞) := by
  have hstrict := isStrictMinimalServiceCurve_drrResidual_of_isDrr hcaus hβ hdrr (i := i)
  rw [drrResidual_rateLatency Q lmax i R T hR'] at hstrict
  exact ⟨_, delay_le_of_strictRateLatency_affine (isCausal_residualServer hcaus i) hstrict hp harr
    hR' hr⟩

/-- **Per-flow backlog under DRR**: the same flow has finite backlog (bounded by `r·T' + b` of its
rate-latency residual). -/
theorem isFlowBacklogBounded_drr {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {Q lmax : ι → ℝ≥0} {i : ι} {R T : ℝ≥0}
    {Ai Di : Curve} {r b : ℝ≥0}
    (hcaus : IsCausalN S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) (aggregateServer S))
    (hdrr : IsDrrServerN Q lmax S) (hp : residualServer S i Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hr : r ≤ (Q i / ∑ j, Q j) * R) (hR' : 0 < (Q i / ∑ j, Q j) * R) :
    ∃ c : ℝ≥0, Deviation.backlog (⇑Ai) (⇑Di) ≤ (c : ℝ≥0∞) := by
  have hstrict := isStrictMinimalServiceCurve_drrResidual_of_isDrr hcaus hβ hdrr (i := i)
  rw [drrResidual_rateLatency Q lmax i R T hR'] at hstrict
  exact ⟨_, backlog_le_of_strictRateLatency_affine (isCausal_residualServer hcaus i) hstrict hp harr
    hr⟩

end DeepWiki
