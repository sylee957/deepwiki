import DeepWiki.NetworkCalculus.ServersResidualSpPmoo
import DeepWiki.NetworkCalculus.ServersConcatenationRateLatency
import DeepWiki.NetworkCalculus.DeviationsBoundsServerRateLatency
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstant

/-! # Static-priority PMOO end-to-end delay / backlog over arbitrary `List` routing
For static-priority multiplexing, flow `i`'s residual at each hop is the priority residual against
only the higher-priority flows `j < i`. When the servers are left-continuous strict rate-latency
`β_{R h, T h}` and the higher-priority cross-traffic aggregates to affine `ρ h·v + bc h`, the chain
folds (`concatConv_liftEReal_rateLatency`) to the single end-to-end rate-latency
`β_{⨅(R h − ρ h), ∑T'_h}`, so a token-bucket flow has finite end-to-end delay/backlog — the SP-PMOO
end-to-end performance bound over arbitrary `List` routing. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

variable {ι κ : Type*} [Fintype ι] [LinearOrder ι]

/-- **SP-PMOO end-to-end delay bound**: flow `i` across a nonempty `List` path of left-continuous
strict rate-latency static-priority servers `β_{R h, T h}`, with higher-priority cross-traffic
aggregating to affine `ρ h·v + bc h` and flow `i` token-bucket `γ_{r,b}` with `r ≤ ⨅(R h − ρ h)`,
has end-to-end delay at most `∑ T'_h + b/⨅(R h − ρ h)`. -/
theorem delay_le_spPmoo_rateLatency
    {S : κ → (ι → Curve) → (ι → Curve) → Prop} {R T : κ → ℝ≥0} {α : κ → ι → ℝ≥0 → ℝ≥0} {i : ι}
    {ρ bc : κ → ℝ≥0} {Ai Di : Curve} {r b : ℝ≥0} {head : κ} {tail : List κ}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβlc : ∀ h, IsLeftContinuous (rateLatency (R h) (T h)))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (rateLatency (R h) (T h)) (aggregateServer (S h)))
    (hSP : ∀ h, IsStaticPriorityServerN (S h))
    (hcross : ∀ h, (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α h j v)
      = fun v => ρ h * v + bc h)
    (hstab : ∀ h, ρ h < R h)
    (hp : concatComp (fun h => residualServer (fun As Ds => S h As Ds ∧
      ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α h j)) i) (head :: tail) Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hRpos : 0 < pathMinRate (fun h => R h - ρ h) head tail)
    (hr : r ≤ pathMinRate (fun h => R h - ρ h) head tail) :
    Deviation.delay (⇑Ai) (⇑Di)
      ≤ ((pathSumLatency (fun h => (R h * T h + bc h) / (R h - ρ h)) head tail
          + b / pathMinRate (fun h => R h - ρ h) head tail : ℝ≥0) : ℝ≥0∞) := by
  have hserv := isMinimalServiceCurve_concatConv_spResidual
    (S := S) (β := fun h => rateLatency (R h) (T h)) (α := α) (i := i)
    hcaus hβlc hβ hSP (head :: tail)
  have heq : (fun h => liftEReal (residualCurve (rateLatency (R h) (T h))
        (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α h j v)))
      = (fun h => liftEReal (rateLatency (R h - ρ h) ((R h * T h + bc h) / (R h - ρ h)))) := by
    funext h
    rw [hcross h, residualCurve_rateLatency_affine (R h) (T h) (ρ h) (bc h) (hstab h)]
  rw [heq, concatConv_liftEReal_rateLatency] at hserv
  exact delay_le_of_minRateLatency_affine hserv hp harr hRpos hr

/-- **SP-PMOO end-to-end backlog bound**: under the same hypotheses, backlog at most `r·(∑ T'_h) + b`. -/
theorem backlog_le_spPmoo_rateLatency
    {S : κ → (ι → Curve) → (ι → Curve) → Prop} {R T : κ → ℝ≥0} {α : κ → ι → ℝ≥0 → ℝ≥0} {i : ι}
    {ρ bc : κ → ℝ≥0} {Ai Di : Curve} {r b : ℝ≥0} {head : κ} {tail : List κ}
    (hcaus : ∀ h, IsCausalN (S h))
    (hβlc : ∀ h, IsLeftContinuous (rateLatency (R h) (T h)))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (rateLatency (R h) (T h)) (aggregateServer (S h)))
    (hSP : ∀ h, IsStaticPriorityServerN (S h))
    (hcross : ∀ h, (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α h j v)
      = fun v => ρ h * v + bc h)
    (hstab : ∀ h, ρ h < R h)
    (hp : concatComp (fun h => residualServer (fun As Ds => S h As Ds ∧
      ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α h j)) i) (head :: tail) Ai Di)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hr : r ≤ pathMinRate (fun h => R h - ρ h) head tail) :
    Deviation.backlog (⇑Ai) (⇑Di)
      ≤ ((r * pathSumLatency (fun h => (R h * T h + bc h) / (R h - ρ h)) head tail + b : ℝ≥0)
          : ℝ≥0∞) := by
  have hserv := isMinimalServiceCurve_concatConv_spResidual
    (S := S) (β := fun h => rateLatency (R h) (T h)) (α := α) (i := i)
    hcaus hβlc hβ hSP (head :: tail)
  have heq : (fun h => liftEReal (residualCurve (rateLatency (R h) (T h))
        (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α h j v)))
      = (fun h => liftEReal (rateLatency (R h - ρ h) ((R h * T h + bc h) / (R h - ρ h)))) := by
    funext h
    rw [hcross h, residualCurve_rateLatency_affine (R h) (T h) (ρ h) (bc h) (hstab h)]
  rw [heq, concatConv_liftEReal_rateLatency] at hserv
  exact backlog_le_of_minRateLatency_affine hserv hp harr hr

end DeepWiki
