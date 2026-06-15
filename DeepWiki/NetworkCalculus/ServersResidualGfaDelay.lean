import DeepWiki.NetworkCalculus.ServersResidualGfa
import DeepWiki.NetworkCalculus.ServersConcatenationRateLatency
import DeepWiki.NetworkCalculus.DeviationsBoundsServerRateLatency
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstant

/-! # GFA end-to-end delay / backlog over arbitrary `List` routing
Group-flow analysis end-to-end performance: like SFA, but flow `i`'s residual at each hop is taken
against a grouped cross-traffic aggregate `η h` (any curve bounding the other flows' departure sum).
When the servers are rate-latency `β_{R h, T h}` and `η h` is affine `ρ h·v + bc h`, the same fold
(`concatConv_liftEReal_rateLatency`) gives the single end-to-end rate-latency `β_{⨅(R h − ρ h), ∑T'_h}`,
so a token-bucket flow has finite end-to-end delay/backlog. A tighter grouped `η` than `∑_{j≠i} α_j`
gives smaller residual rates and hence smaller (better) bounds than SFA. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-- **GFA end-to-end delay bound**: flow `i` across a nonempty `List` path of strict rate-latency
servers `β_{R h, T h}`, with grouped cross-traffic `η h = ρ h·v + bc h` and flow `i` token-bucket
`γ_{r,b}` with `r ≤ ⨅(R h − ρ h)`, has end-to-end delay at most `∑ T'_h + b/⨅(R h − ρ h)`. -/
theorem delay_le_gfa_rateLatency
    {ι κ : Type*} [Fintype ι] {S : κ → (ι → Curve) → (ι → Curve) → Prop}
    {R T : κ → ℝ≥0} {η : κ → ℝ≥0 → ℝ≥0} {i : ι} {ρ bc : κ → ℝ≥0} {Ai Di : Curve} {r b : ℝ≥0}
    {head : κ} {tail : List κ}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (rateLatency (R h) (T h)) (aggregateServer (S h)))
    (hη : ∀ h, η h = fun v => ρ h * v + bc h)
    (hstab : ∀ h, ρ h < R h)
    (hp : concatComp (fun h => residualServer (fun A D => S h A D ∧
      IsMaximalArrivalBound (fun x => ∑ j ∈ Finset.univ.erase i, (D j) x) (η h)) i)
      (head :: tail) Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hRpos : 0 < pathMinRate (fun h => R h - ρ h) head tail)
    (hr : r ≤ pathMinRate (fun h => R h - ρ h) head tail) :
    Deviation.delay (⇑Ai) (⇑Di)
      ≤ ((pathSumLatency (fun h => (R h * T h + bc h) / (R h - ρ h)) head tail
          + b / pathMinRate (fun h => R h - ρ h) head tail : ℝ≥0) : ℝ≥0∞) := by
  have hserv := isMinimalServiceCurve_concatConv_groupResidual
    (S := S) (β := fun h => rateLatency (R h) (T h)) (η := η) (i := i) hcaus hβ (head :: tail)
  have heq : (fun h => liftEReal (residualCurve (rateLatency (R h) (T h)) (η h)))
      = (fun h => liftEReal (rateLatency (R h - ρ h) ((R h * T h + bc h) / (R h - ρ h)))) := by
    funext h
    rw [hη h, residualCurve_rateLatency_affine (R h) (T h) (ρ h) (bc h) (hstab h)]
  rw [heq, concatConv_liftEReal_rateLatency] at hserv
  exact delay_le_of_minRateLatency_affine hserv hp harr hRpos hr

/-- **GFA end-to-end backlog bound**: under the same hypotheses, backlog at most `r·(∑ T'_h) + b`. -/
theorem backlog_le_gfa_rateLatency
    {ι κ : Type*} [Fintype ι] {S : κ → (ι → Curve) → (ι → Curve) → Prop}
    {R T : κ → ℝ≥0} {η : κ → ℝ≥0 → ℝ≥0} {i : ι} {ρ bc : κ → ℝ≥0} {Ai Di : Curve} {r b : ℝ≥0}
    {head : κ} {tail : List κ}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (rateLatency (R h) (T h)) (aggregateServer (S h)))
    (hη : ∀ h, η h = fun v => ρ h * v + bc h)
    (hstab : ∀ h, ρ h < R h)
    (hp : concatComp (fun h => residualServer (fun A D => S h A D ∧
      IsMaximalArrivalBound (fun x => ∑ j ∈ Finset.univ.erase i, (D j) x) (η h)) i)
      (head :: tail) Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hr : r ≤ pathMinRate (fun h => R h - ρ h) head tail) :
    Deviation.backlog (⇑Ai) (⇑Di)
      ≤ ((r * pathSumLatency (fun h => (R h * T h + bc h) / (R h - ρ h)) head tail + b : ℝ≥0)
          : ℝ≥0∞) := by
  have hserv := isMinimalServiceCurve_concatConv_groupResidual
    (S := S) (β := fun h => rateLatency (R h) (T h)) (η := η) (i := i) hcaus hβ (head :: tail)
  have heq : (fun h => liftEReal (residualCurve (rateLatency (R h) (T h)) (η h)))
      = (fun h => liftEReal (rateLatency (R h - ρ h) ((R h * T h + bc h) / (R h - ρ h)))) := by
    funext h
    rw [hη h, residualCurve_rateLatency_affine (R h) (T h) (ρ h) (bc h) (hstab h)]
  rw [heq, concatConv_liftEReal_rateLatency] at hserv
  exact backlog_le_of_minRateLatency_affine hserv hp harr hr

end DeepWiki
