import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.StabilityNetworkGps
import DeepWiki.NetworkCalculus.StabilityNetworkTrajectory
import DeepWiki.NetworkCalculus.RealCurvesDeconv
import DeepWiki.NetworkCalculus.RealCurvesRates

/-! # GPS networks with constant rates: the peelable critical flow (Lemma 12.5)
In a network of GPS servers where each flow `j` keeps one weight `φⱼ > 0` along its
path and is offered the share `φⱼ / ∑_{k∈Fl(h)} φₖ` of each crossed server `h`'s rate
`R^(h)`, aggregate local stability `∑_{j∈Fl(h)} rⱼ < R^(h)` at every server forces the
existence of a *single* flow `i` — the one minimizing `rⱼ/φⱼ` — whose rate stays
below its GPS share `φᵢ R^(h)/∑_{k∈Fl(h)} φₖ` at *every* server it crosses. This is
the flow that can be peeled off in the induction proving local ⟹ global stability
(Theorem 12.5). The statement is purely arithmetic over the flow/server incidence. -/

namespace DeepWiki

open scoped BigOperators NNReal ENNReal

/-- **Lemma 12.5** (GPS with constant rates): with flows `ι`, servers `σ`, positive
weights `φ`, per-server rates `R`, and flow sets `Fl h` (`i ∈ Fl h ⇔ flow `i` crosses
server `h`), aggregate local stability `∑_{j∈Fl h} r j < R h` at every server yields a
flow `i` below its GPS share `φ i · R h / ∑_{j∈Fl h} φ j` at every server it crosses.
The witness is the flow minimizing `r j / φ j`. -/
theorem exists_flow_below_gps_share {ι σ : Type*} [Fintype ι] [Nonempty ι]
    (r φ : ι → ℝ) (hφ : ∀ j, 0 < φ j) (R : σ → ℝ) (Fl : σ → Finset ι)
    (hstab : ∀ h, ∑ j ∈ Fl h, r j < R h) :
    ∃ i, ∀ h, i ∈ Fl h → r i < φ i * R h / (∑ j ∈ Fl h, φ j) := by
  obtain ⟨i, -, himin⟩ :=
    Finset.exists_min_image Finset.univ (fun j => r j / φ j) Finset.univ_nonempty
  refine ⟨i, fun h hi => ?_⟩
  have hsumφ : 0 < ∑ j ∈ Fl h, φ j := Finset.sum_pos (fun j _ => hφ j) ⟨i, hi⟩
  -- the minimality `r i / φ i ≤ r j / φ j` cross-multiplies to `r i · φ j ≤ r j · φ i`
  have hcross : ∀ j, r i * φ j ≤ r j * φ i := fun j =>
    (div_le_div_iff₀ (hφ i) (hφ j)).mp (himin j (Finset.mem_univ j))
  rw [lt_div_iff₀ hsumφ]
  calc r i * ∑ j ∈ Fl h, φ j
      = ∑ j ∈ Fl h, r i * φ j := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Fl h, φ i * r j :=
        Finset.sum_le_sum fun j _ => (hcross j).trans_eq (mul_comm _ _)
    _ = φ i * ∑ j ∈ Fl h, r j := by rw [← Finset.mul_sum]
    _ < φ i * R h := mul_lt_mul_of_pos_left (hstab h) (hφ i)

/-- **Lemma 12.5 in the network model**: for a GPS-constant network with positive
weights `φ`, per-flow long-term rates `r` and finite per-server service rates `R`
(`longTermArrivalRate αⱼ = rⱼ`, `R^(h) = R h`), aggregate local stability
`∑_{j∈Fl(h)} rⱼ < R^(h)` yields a flow `i` whose rate stays below its GPS share
`(φᵢ/∑_{j∈Fl(h)} φⱼ)·R^(h)` at every server it crosses — the per-server
GPS local-stability condition of `isGloballyStableServer_gps_of_rate_lt`, ready
for the peeling step of Theorem 12.5. -/
theorem Network.exists_flow_below_gpsShare {κ ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq κ] (net : Network κ ι) (φ : ι → ℝ≥0) (hφ : ∀ j, 0 < φ j)
    (r : ι → ℝ≥0) (R : κ → ℝ≥0)
    (hr : ∀ j, longTermArrivalRate (net.arrivalCurve j) = (r j : ℝ≥0∞))
    (hR : ∀ h, net.serviceRate h = (R h : ℝ≥0∞))
    (hstab : ∀ h, ∑ j ∈ net.flowsThrough h, r j < R h) :
    ∃ i, ∀ h, i ∈ net.flowsThrough h →
      longTermArrivalRate (net.arrivalCurve i)
        < (↑(φ i / ∑ j ∈ net.flowsThrough h, φ j) : ℝ≥0∞) * net.serviceRate h := by
  obtain ⟨i, hi⟩ := exists_flow_below_gps_share (fun j => (r j : ℝ)) (fun j => (φ j : ℝ))
    (fun j => by exact_mod_cast hφ j) (fun h => (R h : ℝ)) net.flowsThrough
    (fun h => by
      show ∑ j ∈ net.flowsThrough h, (r j : ℝ) < (R h : ℝ)
      rw [← NNReal.coe_sum]; exact_mod_cast hstab h)
  refine ⟨i, fun h hih => ?_⟩
  rw [hr i, hR h, ← ENNReal.coe_mul, ENNReal.coe_lt_coe, div_mul_eq_mul_div]
  exact_mod_cast hi h hih

/-- **Per-server GPS stability of the critical flow** (Theorem 12.5, step B at one
server): at a server `h` whose flows `Fl(h)` are served by a GPS relation `S`
(strict aggregate service `β^(h) = net.service h`, weights `φ`), a flow `i ∈ Fl(h)`
whose ingress rate stays below its GPS share `(φᵢ/∑_{j∈Fl(h)} φⱼ)·R^(h)` — the
conclusion of `Network.exists_flow_below_gpsShare` — is globally stable at `h`. The
per-server GPS is indexed by the subtype `{j // j ∈ Fl(h)}`, so its share
denominator `∑ⱼ φⱼ` is exactly `∑_{j∈Fl(h)} φⱼ` (`Finset.sum_coe_sort`). -/
theorem Network.isGloballyStableServer_gps_critical {κ ι : Type*} [Fintype ι]
    [DecidableEq κ] (net : Network κ ι) (φ : ι → ℝ≥0) (h : κ)
    {S : ({j // j ∈ net.flowsThrough h} → Curve) →
      ({j // j ∈ net.flowsThrough h} → Curve) → Prop}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve (net.service h) (aggregateServer S))
    (hgps : IsGpsServerN (fun j => φ j.val) S)
    {As Ds : {j // j ∈ net.flowsThrough h} → Curve} (hp : S As Ds)
    {i : {j // j ∈ net.flowsThrough h}}
    (harr : IsMaximalArrivalBound (⇑(As i)) (net.arrivalCurve i.val))
    (hrate : longTermArrivalRate (net.arrivalCurve i.val)
      < (↑(φ i.val / ∑ j ∈ net.flowsThrough h, φ j) : ℝ≥0∞) * net.serviceRate h) :
    IsGloballyStableServer (⇑(As i)) (⇑(Ds i)) := by
  refine isGloballyStableServer_gps_of_rate_lt hcaus hβ hgps hp harr ?_
  rwa [Finset.sum_coe_sort (net.flowsThrough h) φ]

/-- **GPS per-flow path stability** (Theorem 12.5, step B along a path) — the GPS
analogue of `isGloballyStable_residualPath` for a fixed flow population `ι`. Flow
`i` crosses a sequence of GPS servers `Sf 0, Sf 1, …` (each with strict aggregate
service `βf k` and shared weights `φ`); it sees the residual share
`(φᵢ/∑ⱼ φⱼ)·βf k` at hop `k`. If its propagated arrival curve stays locally stable
against that share at every hop (and the per-hop output bound propagates), flow `i`
has a bounded backlogged period at *every* server on its path. -/
theorem isGloballyStable_gpsPath {ι : Type*} [Fintype ι] {n : ℕ}
    {Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop} {βf : ℕ → ℝ≥0 → ℝ≥0} {φ : ι → ℝ≥0} {i : ι}
    (hcaus : ∀ k, IsCausalN (Sf k))
    (hβf : ∀ k, IsStrictMinimalServiceCurve (βf k) (aggregateServer (Sf k)))
    (hgps : ∀ k, IsGpsServerN φ (Sf k))
    (proc : ℕ → Curve) (αs : ℕ → ℝ≥0 → ℝ≥0)
    (hchain : ∀ k, k < n → residualServer (Sf k) i (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (αs 0))
    (hprop : ∀ k, k < n → minDeconv (Deviation.liftENN (αs k))
      (Deviation.liftENN (fun v => (φ i / ∑ j, φ j) * βf k v)) ≤ Deviation.liftENN (αs (k + 1)))
    (hstab : ∀ k, k < n → IsLocallyStableServer (αs k) (fun v => (φ i / ∑ j, φ j) * βf k v)) :
    ∀ k, k < n → IsGloballyStableServer (⇑(proc k)) (⇑(proc (k + 1))) :=
  isGloballyStable_path (S := fun k => residualServer (Sf k) i)
    (β := fun k => fun v => (φ i / ∑ j, φ j) * βf k v)
    (fun k => isCausal_residualServer (hcaus k) i)
    (fun k => isStrictMinimalServiceCurve_residualServer_of_isGps (hcaus k) (hβf k) (hgps k))
    id proc αs hchain harr0 hprop hstab

/-- **Critical-flow path stability, book setting** (Theorem 12.5, step B made
unconditional): a token-bucket flow `γ_{r,b}` crossing a path of GPS servers whose
aggregate offers the rate-latency service `β_{Rₖ,Tₖ}` (shared weights `φ`) is
globally stable at *every* server on its path, provided only its rate stays below
its GPS share, `r < (φᵢ/∑ⱼφⱼ)·Rₖ`. The per-hop propagation is closed-form (the
ingress affine bound `r·t + b` deconvolves to `r·t + (b + r·∑Tⱼ)` at hop `k`,
`minDeconv_affine_rateLatencyNN`), so the `αs`/`hprop`/`hstab` of `isGloballyStable_gpsPath`
are discharged from local stability alone. -/
theorem isGloballyStable_gpsPath_tokenBucket {ι : Type*} [Fintype ι] {n : ℕ}
    {Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop} {φ : ι → ℝ≥0} {i : ι} {r b : ℝ≥0}
    {R T : ℕ → ℝ≥0} (hcaus : ∀ k, IsCausalN (Sf k))
    (hβf : ∀ k, IsStrictMinimalServiceCurve (rateLatency (R k) (T k)) (aggregateServer (Sf k)))
    (hgps : ∀ k, IsGpsServerN φ (Sf k)) (proc : ℕ → Curve)
    (hchain : ∀ k, k < n → residualServer (Sf k) i (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (fun t => r * t + b))
    (hr : ∀ k, k < n → r ≤ (φ i / ∑ j, φ j) * R k)
    (hstab : ∀ k, k < n → r < (φ i / ∑ j, φ j) * R k) :
    ∀ k, k < n → IsGloballyStableServer (⇑(proc k)) (⇑(proc (k + 1))) := by
  set sh : ℝ≥0 := φ i / ∑ j, φ j with hsh
  refine isGloballyStable_gpsPath hcaus hβf hgps proc
    (fun k t => r * t + (b + r * ∑ j ∈ Finset.range k, T j)) hchain ?_ ?_ ?_
  · simpa using harr0
  · intro k hk
    have hres : Deviation.liftENN (fun v => sh * rateLatency (R k) (T k) v)
        = rateLatencyNN (sh * R k) (T k) := by
      funext v
      rw [rateLatencyNN_coe]
      show ((sh * (R k * (v - T k)) : ℝ≥0) : ℝ≥0∞) = (((sh * R k) * (v - T k) : ℝ≥0) : ℝ≥0∞)
      rw [mul_assoc]
    have hαk : Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, T j))
        = affine r (b + r * ∑ j ∈ Finset.range k, T j) := by
      funext t; rw [affine_coe]
    rw [hres, hαk, minDeconv_affine_rateLatencyNN r _ (sh * R k) (T k) (hr k hk)]
    have hαk1 : Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range (k + 1), T j))
        = affine r (b + r * ∑ j ∈ Finset.range k, T j + r * T k) := by
      funext t; rw [affine_coe, Finset.sum_range_succ]; push_cast; ring_nf
    rw [hαk1]
  · intro k hk
    show longTermArrivalRate (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, T j))
        < longTermServiceRate (fun v => sh * rateLatency (R k) (T k) v)
    rw [longTermArrivalRate_affine, longTermServiceRate_const_mul, longTermServiceRate_rateLatency,
      ← ENNReal.coe_mul]
    exact_mod_cast hstab k hk

end DeepWiki
