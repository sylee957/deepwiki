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

/-- **SP per-flow path stability (book setting)**: a token-bucket flow `γ_{r,b}` crossing a path
of static-priority servers — hop `k`'s aggregate offering strict rate-latency `β_{R k,T k}`, the
strictly-higher-priority flows `j < i` token-bucket `rHP j·v + bHP k j`-bounded at that hop — is
globally stable at every server on its path, given only that its rate stays below the
higher-priority-reduced rate `r < R k − ∑_{j<i} rHP j` at each hop. The SP analogue of
`isGloballyStable_gpsPathOn_tokenBucket`: each hop's SP residual is the reduced-rate rate-latency
`β_{R k − ∑_{j<i}rHP, ·}` (the peel step `isStrictMinimalServiceCurve_residualServer_spPeel`), and
the per-hop token-bucket propagation is closed-form (`minDeconv_affine_rateLatencyNN`), so the
`αs`/`hprop`/`hstab` of `isGloballyStable_path` are discharged from local stability alone. -/
theorem isGloballyStable_spPath_tokenBucket {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    {Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop} {i : ι} {r b : ℝ≥0}
    {R T : ℕ → ℝ≥0} {rHP : ι → ℝ≥0} {bHP : ℕ → ι → ℝ≥0}
    (hcaus : ∀ k, IsCausalN (Sf k))
    (hβf : ∀ k, IsStrictMinimalServiceCurve (rateLatency (R k) (T k)) (aggregateServer (Sf k)))
    (hSP : ∀ k, IsStaticPriorityServerN (Sf k))
    (hρ : ∀ k, (∑ j ∈ Finset.univ.filter (fun j => j < i), rHP j) < R k)
    (proc : ℕ → Curve)
    (hchain : ∀ k, k < n → residualServer (fun As Ds => Sf k As Ds ∧
      ∀ j, j < i → IsMaximalArrivalBound (⇑(As j)) (fun v => rHP j * v + bHP k j)) i
      (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (fun t => r * t + b))
    (hr : ∀ k, k < n → r ≤ R k - ∑ j ∈ Finset.univ.filter (fun j => j < i), rHP j)
    (hstab : ∀ k, k < n → r < R k - ∑ j ∈ Finset.univ.filter (fun j => j < i), rHP j) :
    ∀ k, k < n → IsGloballyStableServer (⇑(proc k)) (⇑(proc (k + 1))) := by
  set Rred : ℕ → ℝ≥0 := fun k => R k - ∑ j ∈ Finset.univ.filter (fun j => j < i), rHP j with hRred
  set Tred : ℕ → ℝ≥0 := fun k => (R k * T k + ∑ j ∈ Finset.univ.filter (fun j => j < i), bHP k j)
    / (R k - ∑ j ∈ Finset.univ.filter (fun j => j < i), rHP j) with hTred
  refine isGloballyStable_path
    (S := fun k => residualServer (fun As Ds => Sf k As Ds ∧
      ∀ j, j < i → IsMaximalArrivalBound (⇑(As j)) (fun v => rHP j * v + bHP k j)) i)
    (β := fun k => rateLatency (Rred k) (Tred k))
    (fun k => isCausal_residualServer (fun A D hAD => hcaus k A D hAD.1) i)
    (fun k => isStrictMinimalServiceCurve_residualServer_spPeel (hcaus k) (hβf k) (hSP k) (hρ k))
    id proc (fun k t => r * t + (b + r * ∑ j ∈ Finset.range k, Tred j)) hchain ?_ ?_ ?_
  · simpa using harr0
  · intro k hk
    show minDeconv (Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, Tred j)))
        (Deviation.liftENN (rateLatency (Rred k) (Tred k)))
      ≤ Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range (k + 1), Tred j))
    have hres : Deviation.liftENN (rateLatency (Rred k) (Tred k)) = rateLatencyNN (Rred k) (Tred k) := by
      funext v; rw [rateLatencyNN_coe]; rfl
    have hαk : Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, Tred j))
        = affine r (b + r * ∑ j ∈ Finset.range k, Tred j) := by funext t; rw [affine_coe]
    rw [hres, hαk, minDeconv_affine_rateLatencyNN r _ (Rred k) (Tred k) (hr k hk)]
    have hαk1 : Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range (k + 1), Tred j))
        = affine r (b + r * ∑ j ∈ Finset.range k, Tred j + r * Tred k) := by
      funext t; rw [affine_coe, Finset.sum_range_succ]; push_cast; ring_nf
    rw [hαk1]
  · intro k hk
    show longTermArrivalRate (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, Tred j))
        < longTermServiceRate (rateLatency (Rred k) (Tred k))
    rw [longTermArrivalRate_affine, longTermServiceRate_rateLatency]
    exact_mod_cast hstab k hk

end DeepWiki
