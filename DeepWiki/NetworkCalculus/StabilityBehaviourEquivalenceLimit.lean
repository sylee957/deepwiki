import DeepWiki.NetworkCalculus.StabilityBehaviourEquivalence
import DeepWiki.NetworkCalculus.StabilityLinearModelReduction

/-! # The `R = ∞` limit of Lemma 12.2 and the same-flows linear-model reduction
Two residuals of §12.1 closed here.

* **Lemma 12.2, the `n → ∞` limit.** The behaviour-preserving surrogate raise
  `β ⊔ rateLatency n T` has service rate `≥ n`
  (`le_longTermServiceRate_sup_rateLatency`); as the surrogate rate `n → ∞` the
  raised service rate tends to `⊤`
  (`tendsto_longTermServiceRate_sup_rateLatency_atTop`), the faithful reading of
  the book's "`R(β ∨ δ_T) = ∞`" through an arbitrarily large *finite* surrogate.
  The clean consequence: for a globally stable strict server, **every** flow of
  finite arrival rate is made locally stable by some surrogate rate `n`
  (`exists_isLocallyStableServer_sup_rateLatency_of_globallyStable`).

* **Lemma 12.3, the `htraj` discharge for a same-flows linear model.** The
  reduction `Network.isGloballyStable_of_linearModel` takes the trajectory
  admissibility `htraj` as a hypothesis. When `netLin` is built on the **same
  flows** as `net` (same routing `paths`, same per-flow arrival processes
  `arrival`) — only the arrival/service *curves* replaced by linear bounds — the
  aggregate arrivals coincide *definitionally*, so `htraj` is `rfl` and the
  reduction discharges to `Network.isGloballyStable_of_sameArrivalLinearModel`.
  The residual genuine curve-replacement (replace a curve while *enlarging* the
  admissible trajectory set) is scoped at the foot of the file. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal Topology
open Filter

/-! ## (1) The `n → ∞` (R = ∞) limit of the surrogate raise -/

/-- `(n : ℝ≥0∞) → ⊤` as the surrogate rate `n : ℝ≥0` runs to `∞`. -/
theorem tendsto_coe_atTop_nhds_top :
    Tendsto (fun n : ℝ≥0 => (n : ℝ≥0∞)) atTop (𝓝 ⊤) :=
  ENNReal.tendsto_coe_nhds_top.mpr tendsto_id

/-- **The surrogate raise realizes `R = ∞` in the limit** (Lemma 12.2, `n → ∞`):
as the surrogate rate `n → ∞`, the long-term service rate of the
behaviour-preserving raise `β ⊔ rateLatency n T` tends to `⊤`. This is the
faithful reading of the book's `R(β ∨ δ_T) = ∞`: the finite surrogate rate `n`
is dominated by the raised service rate (`le_longTermServiceRate_sup_rateLatency`)
and `(n : ℝ≥0∞) → ⊤`, so the raised rate is squeezed to `⊤`. -/
theorem tendsto_longTermServiceRate_sup_rateLatency_atTop (β : ℝ≥0 → ℝ≥0) (T : ℝ≥0) :
    Tendsto (fun n : ℝ≥0 =>
        longTermServiceRate (fun t => β t ⊔ rateLatency n T t)) atTop (𝓝 ⊤) :=
  tendsto_nhds_top_mono tendsto_coe_atTop_nhds_top
    (Eventually.of_forall fun n => le_longTermServiceRate_sup_rateLatency β n T)

/-- **A finite arrival rate is made locally stable by a large enough surrogate**
(the clean `n → ∞` consequence of Lemma 12.2): for any flow `α` of *finite*
long-term arrival rate, some surrogate rate `n` makes the behaviour-preserving
raise `β ⊔ rateLatency n T` locally stable against `α`. The faithful "raise to
`R = ∞` ⟹ locally stable": pick `n` above the finite rate `r(α)`, then the raised
service rate `≥ n > r(α)`. -/
theorem exists_isLocallyStableServer_sup_rateLatency {β α : ℝ≥0 → ℝ≥0} (T : ℝ≥0)
    (hα : longTermArrivalRate α ≠ ⊤) :
    ∃ n : ℝ≥0, IsLocallyStableServer α (fun t => β t ⊔ rateLatency n T t) := by
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hα
  refine ⟨(n : ℝ≥0), ?_⟩
  refine lt_of_lt_of_le ?_ (le_longTermServiceRate_sup_rateLatency β (n : ℝ≥0) T)
  rwa [ENNReal.coe_natCast]

/-- **Lemma 12.2 in the `R = ∞` form**: a globally stable strict server (common
backlogged bound `T`, strict service curve `β`) is locally stable against *every*
flow of finite arrival rate, after raising `β` by the behaviour-preserving
surrogate `rateLatency n T` for a large enough `n`. Combines the
behaviour-preserving raise (`isStrictMinimalServiceCurve_sup_of_backloggedLength_le`)
with the `n → ∞` service-rate blow-up: the raise stays a strict service curve and
its rate eventually exceeds any finite arrival rate. -/
theorem exists_isLocallyStableServer_sup_rateLatency_of_globallyStable
    {S : Curve → Curve → Prop} {β α : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve β S)
    (hmax : ∀ A D : Curve, S A D → maxBackloggedLength (⇑A) (⇑D) ≤ (T : ℝ≥0∞))
    (hα : longTermArrivalRate α ≠ ⊤) :
    ∃ n : ℝ≥0,
      IsStrictMinimalServiceCurve (fun u => β u ⊔ rateLatency n T u) S ∧
        IsLocallyStableServer α (fun u => β u ⊔ rateLatency n T u) := by
  obtain ⟨n, hstab⟩ := exists_isLocallyStableServer_sup_rateLatency (β := β) T hα
  exact ⟨n, isStrictMinimalServiceCurve_sup_of_backloggedLength_le hβ
      (fun _ h => rateLatency_eq_zero_of_le h)
      (backloggedLength_le_of_forall_maxBackloggedLength_le hmax), hstab⟩

/-! ## Faithfulness checks (Lemma 12.2, `n → ∞`) -/

/-- Faithfulness (`R = ∞` in the limit): the raised service rate of
`β ⊔ rateLatency n T` tends to `⊤` as the surrogate rate `n → ∞`. -/
example (β : ℝ≥0 → ℝ≥0) (T : ℝ≥0) :
    Tendsto (fun n : ℝ≥0 =>
        longTermServiceRate (fun t => β t ⊔ rateLatency n T t)) atTop (𝓝 ⊤) :=
  tendsto_longTermServiceRate_sup_rateLatency_atTop β T

/-- Faithfulness (raise to `R = ∞` ⟹ locally stable): a globally stable strict
server is locally stable against any finite-rate flow after a large enough
surrogate raise. -/
example {S : Curve → Curve → Prop} {β α : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve β S)
    (hmax : ∀ A D : Curve, S A D → maxBackloggedLength (⇑A) (⇑D) ≤ (T : ℝ≥0∞))
    (hα : longTermArrivalRate α ≠ ⊤) :
    ∃ n : ℝ≥0, IsLocallyStableServer α (fun u => β u ⊔ rateLatency n T u) :=
  ⟨_, (exists_isLocallyStableServer_sup_rateLatency_of_globallyStable
    hβ hmax hα).choose_spec.2⟩

/-! ## (2) The `htraj` discharge for a same-flows linear model (Lemma 12.3) -/

variable {κ ι : Type*} [Fintype ι] [DecidableEq κ]

/-- A linear model is built on the **same flows** as `net` when it shares the
routing `paths` and the per-flow arrival processes `arrival` (only the
arrival/service *curves* are replaced by linear bounds). Then the aggregate
source process at every server is unchanged. -/
def Network.SameFlows (net netLin : Network κ ι) : Prop :=
  netLin.paths = net.paths ∧ netLin.arrival = net.arrival

/-- A same-flows linear model has the **same flows-through** at every server: the
crossing-flow sets `Fl(h)` depend only on the shared routing `paths`. -/
theorem Network.SameFlows.flowsThrough {net netLin : Network κ ι}
    (h : net.SameFlows netLin) (k : κ) :
    netLin.flowsThrough k = net.flowsThrough k := by
  simp only [Network.flowsThrough, h.1]

/-- A same-flows linear model has the **same aggregate arrival** at every server:
the aggregate source process `∑_{i∈Fl(h)} Aᵢ` depends only on the shared
`paths`/`arrival`, so it is unchanged when only the curves are replaced. -/
theorem Network.SameFlows.aggregateArrival {net netLin : Network κ ι}
    (h : net.SameFlows netLin) (k : κ) :
    netLin.aggregateArrival k = net.aggregateArrival k := by
  simp only [Network.aggregateArrival, h.flowsThrough k, h.2]

/-- A same-flows linear model satisfies the trajectory-admissibility hypothesis
`htraj` of the reduction *by construction*: the aggregate source processes
coincide, so their coercions are equal. -/
theorem Network.SameFlows.htraj {net netLin : Network κ ι}
    (h : net.SameFlows netLin) :
    ∀ k, ⇑(net.aggregateArrival k) = ⇑(netLin.aggregateArrival k) :=
  fun k => congrArg _ (h.aggregateArrival k).symm

/-- **Lemma 12.3, the reduction with `htraj` discharged for a same-flows linear
model**: if `netLin` is the linear model of `net` on the *same* flows (shared
routing and arrival processes, only the curves replaced), and `netLin` is
globally stable for the original departures, then `net` is globally stable for
those same departures. The trajectory admissibility is `rfl`-discharged via
`Network.SameFlows.htraj` — the aggregate arrivals coincide definitionally. -/
theorem Network.isGloballyStable_of_sameArrivalLinearModel
    (net netLin : Network κ ι) (departure : κ → Curve)
    (hsame : net.SameFlows netLin)
    (hlinStable : netLin.IsGloballyStable departure) :
    net.IsGloballyStable departure :=
  net.isGloballyStable_of_linearModel netLin departure hlinStable hsame.htraj

/-- **The canonical same-flows linear model** of a network: replace each arrival
curve and each service curve by a chosen linear bound, keeping the routing
`paths` and the per-flow arrival processes `arrival`. The resulting network is a
`SameFlows` linear model of `net` by construction. -/
def Network.linearize (net : Network κ ι)
    (arrivalCurveLin : ι → (ℝ≥0 → ℝ≥0)) (serviceLin : κ → (ℝ≥0 → ℝ≥0)) :
    Network κ ι :=
  { net with arrivalCurve := arrivalCurveLin, service := serviceLin }

omit [Fintype ι] [DecidableEq κ] in
/-- A `linearize` is a same-flows model of the original network: it shares the
routing and arrival processes by construction. -/
theorem Network.sameFlows_linearize (net : Network κ ι)
    (arrivalCurveLin : ι → (ℝ≥0 → ℝ≥0)) (serviceLin : κ → (ℝ≥0 → ℝ≥0)) :
    net.SameFlows (net.linearize arrivalCurveLin serviceLin) :=
  ⟨rfl, rfl⟩

/-- **Lemma 12.3 for the canonical linearization**: if the linear model obtained
from `net` by replacing curves with `arrivalCurveLin`/`serviceLin` (same flows)
is globally stable for the original departures, then `net` is globally stable for
those departures. The `htraj` step is fully discharged — the canonical
linearization keeps the same aggregate trajectories. -/
theorem Network.isGloballyStable_of_linearize
    (net : Network κ ι) (departure : κ → Curve)
    (arrivalCurveLin : ι → (ℝ≥0 → ℝ≥0)) (serviceLin : κ → (ℝ≥0 → ℝ≥0))
    (hlinStable : (net.linearize arrivalCurveLin serviceLin).IsGloballyStable departure) :
    net.IsGloballyStable departure :=
  net.isGloballyStable_of_sameArrivalLinearModel _ departure
    (net.sameFlows_linearize arrivalCurveLin serviceLin) hlinStable

/-! ## Faithfulness checks (Lemma 12.3, same-flows reduction) -/

/-- Faithfulness (`htraj` is `rfl` for a same-flows model): the aggregate
arrivals of a same-flows linear model coincide with the original's. -/
example (net netLin : Network κ ι) (hsame : net.SameFlows netLin) (k : κ) :
    netLin.aggregateArrival k = net.aggregateArrival k :=
  hsame.aggregateArrival k

/-- Faithfulness (the reduction, `htraj`-free): global stability of the canonical
linear model transfers to the original network on the same departures. -/
example (net : Network κ ι) (departure : κ → Curve)
    (arrivalCurveLin : ι → (ℝ≥0 → ℝ≥0)) (serviceLin : κ → (ℝ≥0 → ℝ≥0))
    (hlinStable : (net.linearize arrivalCurveLin serviceLin).IsGloballyStable departure) :
    net.IsGloballyStable departure :=
  net.isGloballyStable_of_linearize departure arrivalCurveLin serviceLin hlinStable

/-! ## Scoping: the genuine curve-replacement Lemma 12.3 step

This file discharges `htraj` for the **same-flows** linear model: the routing and
the per-flow cumulative arrival processes `arrival` are shared, only the
arrival/service *curves* are replaced by linear bounds, so the aggregate
trajectories coincide *definitionally* (`Network.SameFlows.htraj` is `rfl` up to
`congrArg`). This is exactly the construction Lemma 12.3 invokes: a token-bucket
bound above on each arrival curve and a rate-latency bound below on each service
curve, leaving the flows themselves untouched.

The one model-level piece still scoped (and untouched here, as it lives in the
core `Network`/served-pair model) is the *genuine* trajectory enlargement the
book also asserts: that bounding an arrival curve from above (or a service curve
from below) makes the linear model admit a **superset** of cumulative-function
trajectories — i.e. the original departures are *among* `netLin`'s, even when the
arrival processes are not literally shared. The faithful same-flows case
(departures literally shared, `htraj = rfl`) is what the reduction needs whenever
the linearization keeps the flows; the strictly-larger-trajectory-set version
needs a served-pair-level "admits more trajectories" operation over the `Servers`
model, a core-model addition rather than a chapter lemma. -/

end DeepWiki
