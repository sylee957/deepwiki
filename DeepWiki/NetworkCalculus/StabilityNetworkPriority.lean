import DeepWiki.NetworkCalculus.StabilityGlobal
import DeepWiki.NetworkCalculus.StabilityResidualRate
import DeepWiki.NetworkCalculus.ServersResidualPriority

/-! # Per-flow stability under static priority
The static-priority analogue of the blind-multiplexing residual stability: in a
preemptive static-priority server, flow `i` sees the residual service curve
`β ⊖ ∑_{j<i} αⱼ` (the leftover after the higher-priority flows,
`isStrictMinimalServiceCurve_residualServer_of_isStaticPriority`). So flow `i`
is globally stable once it is locally stable against that residual — and, via
the residual-rate bound, once its own rate plus the higher-priority rates stays
below the service rate, `r(αᵢ) + ∑_{j<i} r(αⱼ) < R(β)` (the book's static-priority
local-stability condition for flow `i`, Theorem 12.2). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Static-priority per-flow global stability**: in a preemptive SP server with
left-continuous strict aggregate service `β` whose higher-priority flows are
`αⱼ`-arrival-constrained, flow `i` — locally stable against its residual
`β ⊖ ∑_{j<i} αⱼ` — has a bounded backlogged period. The residual being a strict
service curve and the residual server's causality are derived. -/
theorem isGloballyStableServer_staticPriority {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β αi : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S)) (hSP : IsStaticPriorityServerN S)
    {As Ds : ι → Curve} (hp : S As Ds)
    (hhi : ∀ j, j < i → IsMaximalArrivalBound (⇑(As j)) (α j))
    (harr : IsMaximalArrivalBound (⇑(As i)) αi)
    (hstab : IsLocallyStableServer αi
      (residualCurve β (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v))) :
    IsGloballyStableServer (⇑(As i)) (⇑(Ds i)) :=
  have hcaus' : IsCausalN (fun As Ds => S As Ds ∧
      ∀ j, j < i → IsMaximalArrivalBound (⇑(As j)) (α j)) :=
    fun _ _ hAD => hcaus _ _ hAD.1
  isGloballyStableServer_of_isLocallyStableServer
    (isCausal_residualServer hcaus' i)
    (isStrictMinimalServiceCurve_residualServer_of_isStaticPriority hcaus hβlc hβ hSP)
    ⟨As, Ds, ⟨hp, hhi⟩, rfl, rfl⟩ harr hstab

/-- **Static-priority stability from the rate condition** (Theorem 12.2 form):
in a preemptive SP server with monotone left-continuous strict aggregate service
`β`, flow `i` is globally stable as soon as its rate plus the higher-priority
rates stays below the service rate, `r(αᵢ) + r(∑_{j<i} αⱼ) < R(β)` — the
residual-rate bound derives local stability against the priority residual. -/
theorem isGloballyStableServer_staticPriority_of_rate_lt {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β αi : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβlc : IsLeftContinuous β) (hβmono : Monotone β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S)) (hSP : IsStaticPriorityServerN S)
    {As Ds : ι → Curve} (hp : S As Ds)
    (hhi : ∀ j, j < i → IsMaximalArrivalBound (⇑(As j)) (α j))
    (harr : IsMaximalArrivalBound (⇑(As i)) αi)
    (hcrossfin : longTermArrivalRate
      (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v) < ⊤)
    (hrate : longTermArrivalRate αi
        + longTermArrivalRate (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
        < longTermServiceRate β) :
    IsGloballyStableServer (⇑(As i)) (⇑(Ds i)) :=
  isGloballyStableServer_staticPriority hcaus hβlc hβ hSP hp hhi harr
    (isLocallyStableServer_residualCurve_of_rate_lt hβmono hcrossfin hrate)

end DeepWiki
