import DeepWiki.NetworkCalculus.ServersResidualWrr
import DeepWiki.NetworkCalculus.ServersResidualPmooRateLatency
import DeepWiki.NetworkCalculus.DeviationsBoundsServerRateLatency

/-! # WRR residual is rate-latency; per-flow delay / backlog under WRR
When the aggregate service is rate-latency `β_{R,T}`, the WRR residual `wrrResidual` is again a
rate-latency curve (`wrrResidual_rateLatency`): flow `i`'s rate is its weight share
`qᵢ/(qᵢ+Qᵢ)·R`, its latency `T` increased by `Qᵢ/R` (the other flows' per-round price). With the
strict-service guarantee and the server delay/backlog bounds, a token-bucket flow through a WRR
server has finite delay and backlog. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-- **WRR residual of a rate-latency aggregate is rate-latency**: `wrrResidual w lmin lmax i β_{R,T}`
is `β_{R',T'}` with weight-share rate `R' = qᵢ/(qᵢ+Qᵢ)·R` (`qᵢ = wᵢℓᵢˡ`, `Qᵢ = ∑_{j≠i} wⱼℓⱼᵘ`) and
latency `T' = T + Qᵢ/R`, assuming `0 < R`. Via `rateLatency_sub_affine` (`ρ = 0`, the constant `Qᵢ`)
then `const_mul_rateLatency` (the share). -/
theorem wrrResidual_rateLatency {ι : Type*} [Fintype ι] (w : ι → ℕ) (lmin lmax : ι → ℝ≥0) (i : ι)
    (R T : ℝ≥0) (hR : 0 < R) :
    wrrResidual w lmin lmax i (rateLatency R T)
      = rateLatency
          ((w i : ℝ≥0) * lmin i / ((w i : ℝ≥0) * lmin i
              + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) * R)
          (T + (∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) / R) := by
  set Q : ℝ≥0 := ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j with hQ
  set ratio : ℝ≥0 := (w i : ℝ≥0) * lmin i / ((w i : ℝ≥0) * lmin i + Q) with hratio
  have h1 : (fun τ => rateLatency R T τ - Q) = rateLatency R (T + Q / R) := by
    have hsub := rateLatency_sub_affine R T 0 Q hR
    simpa [tsub_zero, zero_mul, zero_add] using hsub
  funext τ
  rw [wrrResidual_apply, ← hQ, ← hratio,
    show rateLatency R T τ - Q = rateLatency R (T + Q / R) τ from congrFun h1 τ,
    congrFun (const_mul_rateLatency ratio R (T + Q / R)) τ]

/-- **Per-flow delay under WRR**: a flow `i` served by a WRR server with rate-latency aggregate
`β_{R,T}`, token-bucket input `γ_{r,b}` with `r` below its weight-share rate, has finite virtual
delay (bounded by `T' + b/R'` of its rate-latency residual). -/
theorem isFlowDelayBounded_wrr {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {w : ι → ℕ} {lmin lmax : ι → ℝ≥0} {i : ι} {R T : ℝ≥0}
    {Ai Di : Curve} {r b : ℝ≥0}
    (hcaus : IsCausalN S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) (aggregateServer S))
    (hwrr : IsWrrServerN w lmin lmax S) (hp : residualServer S i Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b)) (hR : 0 < R)
    (hr : r ≤ (w i : ℝ≥0) * lmin i / ((w i : ℝ≥0) * lmin i
            + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) * R)
    (hR' : 0 < (w i : ℝ≥0) * lmin i / ((w i : ℝ≥0) * lmin i
            + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) * R) :
    ∃ d : ℝ≥0, Deviation.delay (⇑Ai) (⇑Di) ≤ (d : ℝ≥0∞) := by
  have hstrict := isStrictMinimalServiceCurve_wrrResidual_of_isWrr hcaus hβ hwrr (i := i)
  rw [wrrResidual_rateLatency w lmin lmax i R T hR] at hstrict
  exact ⟨_, delay_le_of_strictRateLatency_affine (isCausal_residualServer hcaus i) hstrict hp harr
    hR' hr⟩

/-- **Per-flow backlog under WRR**: the same flow has finite backlog (bounded by `r·T' + b` of its
rate-latency residual). -/
theorem isFlowBacklogBounded_wrr {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {w : ι → ℕ} {lmin lmax : ι → ℝ≥0} {i : ι} {R T : ℝ≥0}
    {Ai Di : Curve} {r b : ℝ≥0}
    (hcaus : IsCausalN S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) (aggregateServer S))
    (hwrr : IsWrrServerN w lmin lmax S) (hp : residualServer S i Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b)) (hR : 0 < R)
    (hr : r ≤ (w i : ℝ≥0) * lmin i / ((w i : ℝ≥0) * lmin i
            + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) * R) :
    ∃ c : ℝ≥0, Deviation.backlog (⇑Ai) (⇑Di) ≤ (c : ℝ≥0∞) := by
  have hstrict := isStrictMinimalServiceCurve_wrrResidual_of_isWrr hcaus hβ hwrr (i := i)
  rw [wrrResidual_rateLatency w lmin lmax i R T hR] at hstrict
  exact ⟨_, backlog_le_of_strictRateLatency_affine (isCausal_residualServer hcaus i) hstrict hp harr
    hr⟩

end DeepWiki
