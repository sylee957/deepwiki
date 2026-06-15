import DeepWiki.NetworkCalculus.ServersResidualPriority
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstant
import DeepWiki.NetworkCalculus.RealCurves

/-! # Static-priority networks with constant rates: the per-server peel step
The static-priority analogue of the GPS-constant engine
(`StabilityNetworkGpsConstant`). Under a preemptive static-priority policy a flow `i`
is preempted only by the strictly-higher-priority flows `j < i`, so at a server with
strict rate-latency aggregate `β_{R,T}` and token-bucket higher-priority arrivals it sees
the blind residual `β_{R,T} − ∑_{j<i} γ_{rⱼ,bⱼ}`, which — a rate-latency minus a token
bucket — is again a rate-latency `β_{R − ∑_{j<i} rⱼ, ·}` with the rate reduced by the
higher-priority load (`residualCurve_rateLatency_affine`). This is the SP peeling step; the
network assembly (Theorem 12.3 / FDF) processes flows in priority order. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-- **SP peel step**: at a static-priority server with strict rate-latency aggregate `β_{R,T}`,
restricting to families whose strictly-higher-priority flows `j < i` are token-bucket
`rⱼ·v + bⱼ`-bounded (summed higher-priority rate `< R`), flow `i` is served by the reduced-rate
rate-latency strict service curve `β_{R − ∑_{j<i} rⱼ, (R·T + ∑_{j<i} bⱼ)/(R − ∑_{j<i} rⱼ)}`:
preemptive priority subtracts only the higher-priority token buckets, and the blind residual of
a rate-latency by a token bucket is again rate-latency. The SP analogue of
`isStrictMinimalServiceCurve_residualServer_gpsPeel`. -/
theorem isStrictMinimalServiceCurve_residualServer_spPeel {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {R T : ℝ≥0} {r b : ι → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve (rateLatency R T) (aggregateServer S))
    (hSP : IsStaticPriorityServerN S)
    (hρR : (∑ j ∈ Finset.univ.filter (fun j => j < i), r j) < R) :
    IsStrictMinimalServiceCurve
      (rateLatency (R - ∑ j ∈ Finset.univ.filter (fun j => j < i), r j)
        ((R * T + ∑ j ∈ Finset.univ.filter (fun j => j < i), b j)
          / (R - ∑ j ∈ Finset.univ.filter (fun j => j < i), r j)))
      (residualServer (fun As Ds => S As Ds ∧
        ∀ j, j < i → IsMaximalArrivalBound (⇑(As j)) (fun v => r j * v + b j)) i) := by
  have hlc : IsLeftContinuous (rateLatency R T) :=
    isLeftContinuous_of_continuous _ (rateLatency_continuous R T)
  have h := isStrictMinimalServiceCurve_residualServer_of_isStaticPriority
    (α := fun j => fun v => r j * v + b j) (i := i) hcaus hlc hβ hSP
  -- the subtracted higher-priority aggregate is a single affine
  have hsum : (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), (r j * v + b j))
      = (fun v => (∑ j ∈ Finset.univ.filter (fun j => j < i), r j) * v
          + ∑ j ∈ Finset.univ.filter (fun j => j < i), b j) := by
    funext v
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hsum, residualCurve_rateLatency_affine R T _ _ hρR] at h
  exact h

end DeepWiki
