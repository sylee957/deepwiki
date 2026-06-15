import DeepWiki.NetworkCalculus.StabilityGlobal
import DeepWiki.NetworkCalculus.ServersResidualDrr
import DeepWiki.NetworkCalculus.ServersResidualWrr
import DeepWiki.NetworkCalculus.ServersResidualTdma

/-! # Per-flow stability under fair/frame schedulers
The stability consequence of the scheduler residual service curves: a flow
served by DRR, WRR, or TDMA sees a strict residual service curve
(`isStrictMinimalServiceCurve_*Residual_of_*`), so it is globally stable as soon
as it is locally stable against that residual — the same compose-the-residual
pattern as the blind-multiplexing, static-priority, and GPS stability results. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **DRR per-flow global stability**: under DRR with strict aggregate service
`β`, flow `i` — locally stable against its DRR residual `drrResidual Q lmax i β`
— has a bounded backlogged period. -/
theorem isGloballyStableServer_drr {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β αi : ℝ≥0 → ℝ≥0} {Q lmax : ι → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hdrr : IsDrrServerN Q lmax S)
    {As Ds : ι → Curve} (hp : S As Ds)
    (harr : IsMaximalArrivalBound (⇑(As i)) αi)
    (hstab : IsLocallyStableServer αi (drrResidual Q lmax i β)) :
    IsGloballyStableServer (⇑(As i)) (⇑(Ds i)) :=
  isGloballyStableServer_of_isLocallyStableServer
    (isCausal_residualServer hcaus i)
    (isStrictMinimalServiceCurve_drrResidual_of_isDrr hcaus hβ hdrr)
    (residualServer_apply hp i) harr hstab

/-- **WRR per-flow global stability**: under WRR with strict aggregate service
`β`, flow `i` — locally stable against its WRR residual
`wrrResidual w lmin lmax i β` — has a bounded backlogged period. -/
theorem isGloballyStableServer_wrr {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β αi : ℝ≥0 → ℝ≥0}
    {w : ι → ℕ} {lmin lmax : ι → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hwrr : IsWrrServerN w lmin lmax S)
    {As Ds : ι → Curve} (hp : S As Ds)
    (harr : IsMaximalArrivalBound (⇑(As i)) αi)
    (hstab : IsLocallyStableServer αi (wrrResidual w lmin lmax i β)) :
    IsGloballyStableServer (⇑(As i)) (⇑(Ds i)) :=
  isGloballyStableServer_of_isLocallyStableServer
    (isCausal_residualServer hcaus i)
    (isStrictMinimalServiceCurve_wrrResidual_of_isWrr hcaus hβ hwrr)
    (residualServer_apply hp i) harr hstab

/-- **TDMA per-flow global stability**: under TDMA with guaranteed rate `R`,
flow `i` — locally stable against its TDMA residual
`tdmaResidual c (o i) (T i) R` — has a bounded backlogged period. -/
theorem isGloballyStableServer_tdma {ι : Type*}
    {S : (ι → Curve) → (ι → Curve) → Prop} {c R : ℝ≥0} {o T : ι → ℝ≥0} {αi : ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (htdma : IsTdmaServerN c o T R S)
    {As Ds : ι → Curve} (hp : S As Ds)
    (harr : IsMaximalArrivalBound (⇑(As i)) αi)
    (hstab : IsLocallyStableServer αi (tdmaResidual c (o i) (T i) R)) :
    IsGloballyStableServer (⇑(As i)) (⇑(Ds i)) :=
  isGloballyStableServer_of_isLocallyStableServer
    (isCausal_residualServer hcaus i)
    (isStrictMinimalServiceCurve_tdmaResidual_of_isTdma htdma)
    (residualServer_apply hp i) harr hstab

end DeepWiki
