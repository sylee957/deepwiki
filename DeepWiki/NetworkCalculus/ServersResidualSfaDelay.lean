import DeepWiki.NetworkCalculus.ServersResidualSfa
import DeepWiki.NetworkCalculus.ServersConcatenationRateLatency
import DeepWiki.NetworkCalculus.DeviationsBoundsServerRateLatency
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstant

/-! # SFA end-to-end delay / backlog over arbitrary `List` routing
Separated-flow analysis end-to-end performance: flow `i` crosses a (nonempty) `List` path of strict
rate-latency servers `β_{R h, T h}`, seeing at each hop its blind-multiplexing residual against the
other flows' arrival curves; when those aggregate to an affine `ρ h·v + bc h`, the per-hop residual
is the rate-latency `β_{R h − ρ h, ·}` (`residualCurve_rateLatency_affine`), and the chain folds to
the single end-to-end rate-latency `β_{⨅(R h − ρ h), ∑ T'_h}` (`concatConv_liftEReal_rateLatency`).
A token-bucket flow `γ_{r,b}` with `r ≤ ⨅(R h − ρ h)` then has finite end-to-end delay and backlog —
the network-calculus end-to-end performance bound over arbitrary routing (not just a linear tandem). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-- **SFA end-to-end delay bound**: flow `i` across a nonempty `List` path of strict rate-latency
servers `β_{R h, T h}`, with per-hop cross-traffic aggregating to the affine `ρ h·v + bc h` and
flow `i` token-bucket `γ_{r,b}` with `r ≤ ⨅(R h − ρ h)`, has end-to-end delay at most
`∑ T'_h + b/⨅(R h − ρ h)` where `T'_h = (R h·T h + bc h)/(R h − ρ h)` is the per-hop residual
latency. -/
theorem delay_le_sfa_rateLatency
    {ι κ : Type*} [Fintype ι] {S : κ → (ι → Curve) → (ι → Curve) → Prop}
    {R T : κ → ℝ≥0} {α : κ → ι → ℝ≥0 → ℝ≥0} {i : ι} {ρ bc : κ → ℝ≥0}
    {Ai Di : Curve} {r b : ℝ≥0} {head : κ} {tail : List κ}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (rateLatency (R h) (T h)) (aggregateServer (S h)))
    (hcross : ∀ h, (fun v => ∑ j ∈ Finset.univ.erase i, α h j v) = fun v => ρ h * v + bc h)
    (hstab : ∀ h, ρ h < R h)
    (hp : concatComp (fun h => residualServer (fun A D => S h A D ∧
      ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(A j) (α h j)) i) (head :: tail) Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hRpos : 0 < pathMinRate (fun h => R h - ρ h) head tail)
    (hr : r ≤ pathMinRate (fun h => R h - ρ h) head tail) :
    Deviation.delay (⇑Ai) (⇑Di)
      ≤ ((pathSumLatency (fun h => (R h * T h + bc h) / (R h - ρ h)) head tail
          + b / pathMinRate (fun h => R h - ρ h) head tail : ℝ≥0) : ℝ≥0∞) := by
  have hserv := isMinimalServiceCurve_concatConv_residualServer
    (S := S) (β := fun h => rateLatency (R h) (T h)) (α := α) (i := i) hcaus hβ (head :: tail)
  have heq : (fun h => liftEReal (residualCurve (rateLatency (R h) (T h))
        (fun v => ∑ j ∈ Finset.univ.erase i, α h j v)))
      = (fun h => liftEReal (rateLatency (R h - ρ h) ((R h * T h + bc h) / (R h - ρ h)))) := by
    funext h
    rw [hcross h, residualCurve_rateLatency_affine (R h) (T h) (ρ h) (bc h) (hstab h)]
  rw [heq, concatConv_liftEReal_rateLatency] at hserv
  exact delay_le_of_minRateLatency_affine hserv hp harr hRpos hr

/-- **SFA end-to-end backlog bound**: under the same hypotheses, flow `i`'s end-to-end backlog is at
most `r·(∑ T'_h) + b`. -/
theorem backlog_le_sfa_rateLatency
    {ι κ : Type*} [Fintype ι] {S : κ → (ι → Curve) → (ι → Curve) → Prop}
    {R T : κ → ℝ≥0} {α : κ → ι → ℝ≥0 → ℝ≥0} {i : ι} {ρ bc : κ → ℝ≥0}
    {Ai Di : Curve} {r b : ℝ≥0} {head : κ} {tail : List κ}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (rateLatency (R h) (T h)) (aggregateServer (S h)))
    (hcross : ∀ h, (fun v => ∑ j ∈ Finset.univ.erase i, α h j v) = fun v => ρ h * v + bc h)
    (hstab : ∀ h, ρ h < R h)
    (hp : concatComp (fun h => residualServer (fun A D => S h A D ∧
      ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(A j) (α h j)) i) (head :: tail) Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hr : r ≤ pathMinRate (fun h => R h - ρ h) head tail) :
    Deviation.backlog (⇑Ai) (⇑Di)
      ≤ ((r * pathSumLatency (fun h => (R h * T h + bc h) / (R h - ρ h)) head tail + b : ℝ≥0)
          : ℝ≥0∞) := by
  have hserv := isMinimalServiceCurve_concatConv_residualServer
    (S := S) (β := fun h => rateLatency (R h) (T h)) (α := α) (i := i) hcaus hβ (head :: tail)
  have heq : (fun h => liftEReal (residualCurve (rateLatency (R h) (T h))
        (fun v => ∑ j ∈ Finset.univ.erase i, α h j v)))
      = (fun h => liftEReal (rateLatency (R h - ρ h) ((R h * T h + bc h) / (R h - ρ h)))) := by
    funext h
    rw [hcross h, residualCurve_rateLatency_affine (R h) (T h) (ρ h) (bc h) (hstab h)]
  rw [heq, concatConv_liftEReal_rateLatency] at hserv
  exact backlog_le_of_minRateLatency_affine hserv hp harr hr

end DeepWiki
