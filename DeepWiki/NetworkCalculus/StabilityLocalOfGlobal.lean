import DeepWiki.NetworkCalculus.StabilityGlobal
import DeepWiki.NetworkCalculus.RealCurvesRates

/-! # Local stability of a server with an infinite service rate, and the linear model
Two fragments of the global-vs-local theory of §12.1.

* The **engine of Lemma 12.2** (global ⟹ local): a server whose long-term service
  rate is `+∞` is locally stable against *any* arrival of finite rate. This is the
  literal content of the book's argument — replacing a strict service curve `β` by
  `β ∨ δ_T` (behaviour unchanged when the backlogged period is bounded by `T`) makes
  `R = ∞`, hence every server locally stable. The *model-equivalence* wrapper
  (`β ↦ β ∨ δ_T` preserves the network behaviour, Prop 5.13) and the `+∞`-valued
  service curve `δ_T` are not yet representable here, so only the rate-engine is
  formalized; see the catalog's `## NOT YET FORMALIZED`.

* The **per-server linear model**: for a token-bucket arrival curve `γ_{r,b} = r·t + b`
  and a rate-latency service curve `β_{R,T} = R·(t − T)`, local stability is *exactly*
  the rate inequality `r < R` (`isLocallyStableServer_affine_rateLatency_iff`), and
  `r < R` makes the server globally stable (the forward specialization of
  `isGloballyStableServer_of_isLocallyStableServer`). -/

namespace DeepWiki

open scoped NNReal ENNReal

/-! ## The Lemma 12.2 engine: infinite service rate ⟹ local stability -/

/-- **Engine of Lemma 12.2** (global ⟹ local): a server whose long-term service rate
is `+∞` is locally stable against any arrival of finite long-term rate. This is what
the book extracts when replacing `β` by `β ∨ δ_T`: the modified service rate is `∞`,
so `r(α) < ∞ = R(β ∨ δ_T)` trivially. -/
theorem isLocallyStableServer_of_serviceRate_top {α β : ℝ≥0 → ℝ≥0}
    (hβ : longTermServiceRate β = ⊤) (hα : longTermArrivalRate α ≠ ⊤) :
    IsLocallyStableServer α β := by
  rw [IsLocallyStableServer, hβ]
  exact hα.lt_top

/-- The arrival rate of a token-bucket curve is finite: `r(γ_{r,b}) = r < ∞`. -/
theorem longTermArrivalRate_affine_ne_top (r b : ℝ≥0) :
    longTermArrivalRate (fun t => r * t + b) ≠ ⊤ := by
  rw [longTermArrivalRate_affine]; exact ENNReal.coe_ne_top

/-! ## The per-server linear model: token-bucket arrival, rate-latency service -/

/-- **Per-server linear-model local stability ⟺ `r < R`**: a token-bucket arrival
curve `γ_{r,b} = r·t + b` against a rate-latency service curve `β_{R,T} = R·(t − T)`
is locally stable iff its rate is below the server rate, `r < R` (the closed-form
rates `r(γ_{r,b}) = r`, `R(β_{R,T}) = R`). -/
theorem isLocallyStableServer_affine_rateLatency_iff (r b R T : ℝ≥0) :
    IsLocallyStableServer (fun t => r * t + b) (rateLatency R T) ↔ r < R := by
  rw [IsLocallyStableServer, longTermArrivalRate_affine, longTermServiceRate_rateLatency,
    ENNReal.coe_lt_coe]

/-- A token-bucket flow `γ_{r,b}` against a rate-latency server `β_{R,T}` is locally
stable whenever `r < R`. -/
theorem isLocallyStableServer_affine_rateLatency (r b R T : ℝ≥0) (hlt : r < R) :
    IsLocallyStableServer (fun t => r * t + b) (rateLatency R T) :=
  (isLocallyStableServer_affine_rateLatency_iff r b R T).mpr hlt

/-- **Linear-model local ⟹ global** (forward of Lemma 12.3, per-server form): a
causal server with strict minimal rate-latency service curve `β_{R,T}`, carrying a
pair `(A, D)` whose arrival is bounded by the token-bucket curve `γ_{r,b}`, is
globally stable whenever `r < R`. Specializes
`isGloballyStableServer_of_isLocallyStableServer` to the linear model via the rate
iff. -/
theorem isGloballyStableServer_affine_rateLatency
    {S : Curve → Curve → Prop} (r b R T : ℝ≥0)
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve (rateLatency R T) S)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalBound (⇑A) (fun t => r * t + b))
    (hlt : r < R) :
    IsGloballyStableServer ⇑A ⇑D :=
  isGloballyStableServer_of_isLocallyStableServer hc hβ hp harr
    (isLocallyStableServer_affine_rateLatency r b R T hlt)

/-! ## Faithfulness checks against §12.1 -/

/-- Faithfulness: the linear-model local-stability condition is exactly `r < R`. -/
example (r b R T : ℝ≥0) :
    IsLocallyStableServer (fun t => r * t + b) (rateLatency R T) ↔ r < R :=
  isLocallyStableServer_affine_rateLatency_iff r b R T

/-- Faithfulness (engine of Lemma 12.2): an infinite service rate makes a
token-bucket-constrained server locally stable. -/
example (β : ℝ≥0 → ℝ≥0) (hβ : longTermServiceRate β = ⊤) (r b : ℝ≥0) :
    IsLocallyStableServer (fun t => r * t + b) β :=
  isLocallyStableServer_of_serviceRate_top hβ (longTermArrivalRate_affine_ne_top r b)

end DeepWiki
