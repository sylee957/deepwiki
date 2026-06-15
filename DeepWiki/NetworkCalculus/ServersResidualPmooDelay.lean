import DeepWiki.NetworkCalculus.ServersResidualPmooChain
import DeepWiki.NetworkCalculus.ServersResidualPmooRateLatency
import DeepWiki.NetworkCalculus.DeviationsBoundsServerRateLatency

/-! # PMOO end-to-end delay / backlog (tandem of rate-latency servers)
Flow `i` crosses a tandem of `n + 1` servers, each offering its aggregate a strict rate-latency
service `β_{Rₕ,Tₕ}`; the other flows (cross-traffic) are token-bucket constrained and their bursts
sum to `ρ·v + bc`. By pay-multiplexing-only-once, flow `i` is served end-to-end by the single
rate-latency residual `β_{(⨅Rₕ)−ρ, T'}` (`isMinimalServiceCurve_pmooResidualChain_of_strict_chain`
+ `pmooResidualChain_rateLatency`). If flow `i` is token-bucket `γ_{r,b}` with `r ≤ (⨅Rₕ)−ρ`, its
**end-to-end delay** is at most `T' + b/((⨅Rₕ)−ρ)` and its backlog at most `r·T' + b`, where
`T' = ∑Tₕ + (ρ·∑Tₕ + bc)/((⨅Rₕ)−ρ)`. This is the separated/grouped-flow end-to-end performance
bound — the headline network-calculus result. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The PMOO end-to-end residual relation: `(Ai, Di)` is flow `i`'s ingress/egress pair across the
tandem, the intermediate stage vectors existentially quantified, with the cross-traffic constrained
by `α`. (The relation served by the chain residual; see
`isMinimalServiceCurve_pmooResidualChain_of_strict_chain`.) -/
abbrev PmooChainRel (S : ℕ → (ι → Curve) → (ι → Curve) → Prop) (n : ℕ) (α : ι → ℝ≥0 → ℝ≥0)
    (i : ι) : Curve → Curve → Prop :=
  residualServer (fun A D =>
    (∃ G : ℕ → ι → Curve, G 0 = A ∧ G (n + 1) = D ∧ ∀ h, h ≤ n → S h (G h) (G (h + 1)))
      ∧ ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(A j) (α j)) i

/-- **PMOO end-to-end delay bound**: flow `i`'s delay across a tandem of `n+1` strict rate-latency
servers, with token-bucket cross-traffic summing to `ρ·v + bc` and token-bucket flow `r ≤ (⨅Rₕ)−ρ`,
is at most `T' + b/((⨅Rₕ)−ρ)`. -/
theorem delay_le_pmooChain_rateLatency
    {S : ℕ → (ι → Curve) → (ι → Curve) → Prop} {R T : ℕ → ℝ≥0} {n : ℕ} {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    {Ai Di : Curve} {r b ρ bc : ℝ≥0}
    (hcaus : ∀ h, h ≤ n → IsCausalN (S h))
    (hβ : ∀ h, h ≤ n → IsStrictMinimalServiceCurve (rateLatency (R h) (T h)) (aggregateServer (S h)))
    (hp : PmooChainRel S n α i Ai Di)
    (hcross : (fun v => ∑ j ∈ Finset.univ.erase i, α j v) = fun v => ρ * v + bc)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hstab : ρ < chainRate R n) (hr : r ≤ chainRate R n - ρ) :
    Deviation.delay (⇑Ai) (⇑Di)
      ≤ ((chainLatency T n + (ρ * chainLatency T n + bc) / (chainRate R n - ρ)
          + b / (chainRate R n - ρ) : ℝ≥0) : ℝ≥0∞) := by
  have hserv := isMinimalServiceCurve_pmooResidualChain_of_strict_chain
    (S := S) (β := fun h => rateLatency (R h) (T h)) (n := n) (α := α) (i := i) hcaus hβ
  rw [hcross, pmooResidualChain_rateLatency R T n ρ bc hstab] at hserv
  exact delay_le_of_minRateLatency_affine hserv hp harr (tsub_pos_of_lt hstab) hr

/-- **PMOO end-to-end backlog bound**: under the same hypotheses, flow `i`'s end-to-end backlog is
at most `r·T' + b`. -/
theorem backlog_le_pmooChain_rateLatency
    {S : ℕ → (ι → Curve) → (ι → Curve) → Prop} {R T : ℕ → ℝ≥0} {n : ℕ} {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    {Ai Di : Curve} {r b ρ bc : ℝ≥0}
    (hcaus : ∀ h, h ≤ n → IsCausalN (S h))
    (hβ : ∀ h, h ≤ n → IsStrictMinimalServiceCurve (rateLatency (R h) (T h)) (aggregateServer (S h)))
    (hp : PmooChainRel S n α i Ai Di)
    (hcross : (fun v => ∑ j ∈ Finset.univ.erase i, α j v) = fun v => ρ * v + bc)
    (harr : IsMaximalArrivalBound (⇑Ai) (fun s => r * s + b))
    (hstab : ρ < chainRate R n) (hr : r ≤ chainRate R n - ρ) :
    Deviation.backlog (⇑Ai) (⇑Di)
      ≤ ((r * (chainLatency T n + (ρ * chainLatency T n + bc) / (chainRate R n - ρ)) + b : ℝ≥0)
          : ℝ≥0∞) := by
  have hserv := isMinimalServiceCurve_pmooResidualChain_of_strict_chain
    (S := S) (β := fun h => rateLatency (R h) (T h)) (n := n) (α := α) (i := i) hcaus hβ
  rw [hcross, pmooResidualChain_rateLatency R T n ρ bc hstab] at hserv
  exact backlog_le_of_minRateLatency_affine hserv hp harr hr

end DeepWiki
