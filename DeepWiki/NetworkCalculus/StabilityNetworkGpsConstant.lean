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

/-- **Lemma 12.5, active-set form**: the same statement with the argmin taken over an
arbitrary nonempty set `K` of candidate flows containing every server's population
(`Fl h ⊆ K`). The witness is the `K`-minimizer of `r j / φ j`; it lies below its GPS
share at every server it crosses. Generalizes `exists_flow_below_gps_share` (the
`K = univ` case) and is the form the peeling recursion uses on the shrinking active set
— needs neither `Fintype ι` nor `Nonempty ι`, only `K.Nonempty`. -/
theorem exists_flow_below_gps_share_on {ι σ : Type*} (K : Finset ι) (hK : K.Nonempty)
    (r φ : ι → ℝ) (hφ : ∀ j, 0 < φ j) (R : σ → ℝ) (Fl : σ → Finset ι)
    (hsub : ∀ h, Fl h ⊆ K) (hstab : ∀ h, ∑ j ∈ Fl h, r j < R h) :
    ∃ i ∈ K, ∀ h, i ∈ Fl h → r i < φ i * R h / (∑ j ∈ Fl h, φ j) := by
  obtain ⟨i, hiK, himin⟩ := K.exists_min_image (fun j => r j / φ j) hK
  refine ⟨i, hiK, fun h hi => ?_⟩
  have hsumφ : 0 < ∑ j ∈ Fl h, φ j := Finset.sum_pos (fun j _ => hφ j) ⟨i, hi⟩
  -- the minimality `r i / φ i ≤ r j / φ j` cross-multiplies to `r i · φ j ≤ r j · φ i`
  have hcross : ∀ j ∈ Fl h, r i * φ j ≤ r j * φ i := fun j hj =>
    (div_le_div_iff₀ (hφ i) (hφ j)).mp (himin j (hsub h hj))
  rw [lt_div_iff₀ hsumφ]
  calc r i * ∑ j ∈ Fl h, φ j
      = ∑ j ∈ Fl h, r i * φ j := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Fl h, φ i * r j :=
        Finset.sum_le_sum fun j hj => (hcross j hj).trans_eq (mul_comm _ _)
    _ = φ i * ∑ j ∈ Fl h, r j := by rw [← Finset.mul_sum]
    _ < φ i * R h := mul_lt_mul_of_pos_left (hstab h) (hφ i)

/-- **Lemma 12.5** (GPS with constant rates): with flows `ι`, servers `σ`, positive
weights `φ`, per-server rates `R`, and flow sets `Fl h` (`i ∈ Fl h ⇔ flow `i` crosses
server `h`), aggregate local stability `∑_{j∈Fl h} r j < R h` at every server yields a
flow `i` below its GPS share `φ i · R h / ∑_{j∈Fl h} φ j` at every server it crosses.
The witness is the flow minimizing `r j / φ j` (the `K = univ` case of
`exists_flow_below_gps_share_on`). -/
theorem exists_flow_below_gps_share {ι σ : Type*} [Fintype ι] [Nonempty ι]
    (r φ : ι → ℝ) (hφ : ∀ j, 0 < φ j) (R : σ → ℝ) (Fl : σ → Finset ι)
    (hstab : ∀ h, ∑ j ∈ Fl h, r j < R h) :
    ∃ i, ∀ h, i ∈ Fl h → r i < φ i * R h / (∑ j ∈ Fl h, φ j) := by
  obtain ⟨i, -, hi⟩ := exists_flow_below_gps_share_on Finset.univ Finset.univ_nonempty
    r φ hφ R Fl (fun _ => Finset.subset_univ _) hstab
  exact ⟨i, hi⟩

/-- **Lemma 12.5, residual-capacity (peeling) form**: on the active flow set `J`,
local stability `∑_{j∈Fl h} r j < R h` yields a flow `i ∈ J` whose rate stays below its
GPS share of the *residual* capacity left after the already-peeled flows `Fl h \ J` are
removed — `φᵢ·(R h − ∑_{j∈Fl h\J} rⱼ) / ∑_{j∈Fl h∩J} φⱼ` — at every server it crosses.
This is the induction step of Theorem 12.5: peeling the lighter flows shrinks the share
denominator and raises the residual capacity (their rates `∑_{Fl h\J} r` are subtracted
from `R h`, the rate of the blind residual service `β − ∑ peeled α`), so the
next-critical flow is again below its now-larger residual share. The threshold inequality
`∑_{Fl h∩J} r < R h − ∑_{Fl h\J} r` is just `∑_{Fl h} r < R h` resplit
(`Finset.sum_inter_add_sum_diff`). -/
theorem exists_flow_below_residual_share {ι σ : Type*} [DecidableEq ι]
    (J : Finset ι) (hJ : J.Nonempty) (r φ : ι → ℝ) (hφ : ∀ j, 0 < φ j)
    (R : σ → ℝ) (Fl : σ → Finset ι) (hstab : ∀ h, ∑ j ∈ Fl h, r j < R h) :
    ∃ i ∈ J, ∀ h, i ∈ Fl h ∩ J →
      r i < φ i * (R h - ∑ j ∈ Fl h \ J, r j) / (∑ j ∈ Fl h ∩ J, φ j) :=
  exists_flow_below_gps_share_on J hJ r φ hφ (fun h => R h - ∑ j ∈ Fl h \ J, r j)
    (fun h => Fl h ∩ J) (fun _ => Finset.inter_subset_right)
    (fun h => by
      have hsplit := Finset.sum_inter_add_sum_diff (Fl h) J r
      linarith [hstab h])

/-- **Closed-form residual of a rate-latency by a token bucket**: removing a flow whose
arrival is the token bucket `ρ·v + b` from a rate-latency server `β_{R,T}` (`ρ < R`) leaves
the blind residual `residualCurve β_{R,T} (ρ·v+b) = β_{R−ρ, (R·T+b)/(R−ρ)}` — again a
rate-latency, with the rate reduced by the removed flow's rate. The clamped difference is
already non-decreasing (it *is* that reduced rate-latency), so the non-decreasing closure
is the identity. This keeps the Theorem 12.5 peeling inside the rate-latency world: the
not-yet-peeled aggregate sees a rate-latency curve whose rate is `R` minus the summed
rates of the already-peeled flows. -/
theorem residualCurve_rateLatency_affine (R T ρ b : ℝ≥0) (hρR : ρ < R) :
    residualCurve (rateLatency R T) (fun v => ρ * v + b)
      = rateLatency (R - ρ) ((R * T + b) / (R - ρ)) := by
  have hD : (0 : ℝ≥0) < R - ρ := tsub_pos_of_lt hρR
  have hDne : R - ρ ≠ 0 := ne_of_gt hD
  have hDvs : (R - ρ) * ((R * T + b) / (R - ρ)) = R * T + b := mul_div_cancel₀ _ hDne
  set vs : ℝ≥0 := (R * T + b) / (R - ρ) with hvs
  have hTvs : T ≤ vs := by
    rw [hvs, le_div_iff₀ hD]
    calc T * (R - ρ) ≤ T * R := mul_le_mul_right tsub_le_self T
      _ = R * T := mul_comm T R
      _ ≤ R * T + b := le_self_add
  have key : residualCurve (rateLatency R T) (fun v => ρ * v + b)
      = ndClosure (rateLatency (R - ρ) vs) := by
    unfold residualCurve
    congr 1
    funext v
    show R * (v - T) - (ρ * v + b) = (R - ρ) * (v - vs)
    rcases le_total vs v with hvsv | hvvs
    · rw [mul_tsub, mul_tsub, hDvs, tsub_mul, tsub_tsub, tsub_tsub]
      congr 1
      ring
    · rw [tsub_eq_zero_of_le hvvs, mul_zero, tsub_eq_zero_iff_le, mul_tsub, tsub_le_iff_right]
      have hle : (R - ρ) * v ≤ R * T + b := by
        rw [← hDvs]; exact mul_le_mul_right hvvs (R - ρ)
      rw [tsub_mul, tsub_le_iff_right] at hle
      exact hle.trans_eq (by ring)
  rw [key, ndClosure_eq_self (rateLatency_mono _ _)]

/-- **One peeling step at a server** (the Theorem 12.5 induction step, relation form):
at a GPS server with full strict rate-latency aggregate `β_{R,T}` and weights `φ`, restrict
to families whose already-peeled flows `∑_{j∉J} Dⱼ` are token-bucket `ρ·v+b`-constrained
(`ρ` their summed rate, `ρ < R`). Then the not-yet-peeled critical flow `i ∈ J` is served
by the rate-latency strict service curve `β_{(φᵢ/∑_{j∈J}φ)(R−ρ), (R·T+b)/(R−ρ)}`: the
blind residual leaves the `J`-aggregate the reduced-rate rate-latency `β_{R−ρ,·}`
(`isStrictMinimalServiceCurve_aggregateServerOn_residual` + `residualCurve_rateLatency_affine`),
and the GPS share carves flow `i`'s slice of it
(`isStrictMinimalServiceCurve_residualServer_of_isGps_on` + `const_mul_rateLatency`). The
rate `(φᵢ/∑_{j∈J}φ)(R−ρ)` exceeds `rᵢ` exactly by `exists_flow_below_residual_share`. -/
theorem isStrictMinimalServiceCurve_residualServer_gpsPeel {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : (ι → Curve) → (ι → Curve) → Prop} {φ : ι → ℝ≥0}
    {R T ρ b : ℝ≥0} {J : Finset ι} {i : ι} (hi : i ∈ J) (hρR : ρ < R)
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve (rateLatency R T) (aggregateServer S))
    (hgps : IsGpsServerN φ S) :
    IsStrictMinimalServiceCurve
      (rateLatency ((φ i / ∑ j ∈ J, φ j) * (R - ρ)) ((R * T + b) / (R - ρ)))
      (residualServer (fun A D => S A D ∧ IsMaximalArrivalBound
        (fun x => ∑ j ∈ Jᶜ, (D j) x) (fun v => ρ * v + b)) i) := by
  have hcaus' : IsCausalN (fun A D => S A D ∧ IsMaximalArrivalBound
      (fun x => ∑ j ∈ Jᶜ, (D j) x) (fun v => ρ * v + b)) :=
    fun A D hAD => hcaus A D hAD.1
  have hgps' : IsGpsServerN φ (fun A D => S A D ∧ IsMaximalArrivalBound
      (fun x => ∑ j ∈ Jᶜ, (D j) x) (fun v => ρ * v + b)) :=
    fun As Ds hAD => hgps As Ds hAD.1
  have hres := isStrictMinimalServiceCurve_aggregateServerOn_residual (S := S)
    (α := fun v => ρ * v + b) (J := J) hcaus hβ
  rw [residualCurve_rateLatency_affine R T ρ b hρR] at hres
  have hshare := isStrictMinimalServiceCurve_residualServer_of_isGps_on hi hcaus' hres hgps'
  rwa [const_mul_rateLatency] at hshare

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

/-- **GPS per-flow path stability, per-server `Fl(h)`-shares** — the `J`-restricted
analogue of `isGloballyStable_gpsPath`. At hop `k` the GPS aggregate over the flow
set `J k` (the flows present, with `i ∈ J k`) offers strict `βf k`, so flow `i` sees
the share `(φᵢ/∑_{j∈J k} φⱼ)·βf k` (denominator over the present flows). If its
propagated arrival curve is locally stable against that share at every hop, flow `i`
is globally stable at every server on its path. No `Fintype ι` needed. -/
theorem isGloballyStable_gpsPathOn {ι : Type*} {n : ℕ}
    {Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop} {βf : ℕ → ℝ≥0 → ℝ≥0} {φ : ι → ℝ≥0}
    {i : ι} {J : ℕ → Finset ι} (hi : ∀ k, i ∈ J k) (hcaus : ∀ k, IsCausalN (Sf k))
    (hβf : ∀ k, IsStrictMinimalServiceCurve (βf k) (aggregateServerOn (Sf k) (J k)))
    (hgps : ∀ k, IsGpsServerN φ (Sf k))
    (proc : ℕ → Curve) (αs : ℕ → ℝ≥0 → ℝ≥0)
    (hchain : ∀ k, k < n → residualServer (Sf k) i (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (αs 0))
    (hprop : ∀ k, k < n → minDeconv (Deviation.liftENN (αs k))
      (Deviation.liftENN (fun v => (φ i / ∑ j ∈ J k, φ j) * βf k v)) ≤ Deviation.liftENN (αs (k + 1)))
    (hstab : ∀ k, k < n → IsLocallyStableServer (αs k) (fun v => (φ i / ∑ j ∈ J k, φ j) * βf k v)) :
    ∀ k, k < n → IsGloballyStableServer (⇑(proc k)) (⇑(proc (k + 1))) :=
  isGloballyStable_path (S := fun k => residualServer (Sf k) i)
    (β := fun k => fun v => (φ i / ∑ j ∈ J k, φ j) * βf k v)
    (fun k => isCausal_residualServer (hcaus k) i)
    (fun k => isStrictMinimalServiceCurve_residualServer_of_isGps_on (hi k) (hcaus k) (hβf k) (hgps k))
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

/-- **Critical-flow path stability with `Fl(h)`-shares** — the per-server-population
analogue of `isGloballyStable_gpsPath_tokenBucket`. A token-bucket flow `γ_{r,b}`
through a path of GPS servers whose aggregate over the present flows `J k` offers
rate-latency `β_{Rₖ,Tₖ}` is globally stable at every server, given only
`r < (φᵢ/∑_{j∈J k} φⱼ)·Rₖ` (the share denominator over the flows at that server).
The closed-form propagation discharges everything from local stability. -/
theorem isGloballyStable_gpsPathOn_tokenBucket {ι : Type*} {n : ℕ}
    {Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop} {φ : ι → ℝ≥0} {i : ι} {r b : ℝ≥0}
    {R T : ℕ → ℝ≥0} {J : ℕ → Finset ι} (hi : ∀ k, i ∈ J k) (hcaus : ∀ k, IsCausalN (Sf k))
    (hβf : ∀ k, IsStrictMinimalServiceCurve (rateLatency (R k) (T k)) (aggregateServerOn (Sf k) (J k)))
    (hgps : ∀ k, IsGpsServerN φ (Sf k)) (proc : ℕ → Curve)
    (hchain : ∀ k, k < n → residualServer (Sf k) i (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (fun t => r * t + b))
    (hr : ∀ k, k < n → r ≤ (φ i / ∑ j ∈ J k, φ j) * R k)
    (hstab : ∀ k, k < n → r < (φ i / ∑ j ∈ J k, φ j) * R k) :
    ∀ k, k < n → IsGloballyStableServer (⇑(proc k)) (⇑(proc (k + 1))) := by
  refine isGloballyStable_gpsPathOn hi hcaus hβf hgps proc
    (fun k t => r * t + (b + r * ∑ j ∈ Finset.range k, T j)) hchain ?_ ?_ ?_
  · simpa using harr0
  · intro k hk
    have hres : Deviation.liftENN (fun v => (φ i / ∑ j ∈ J k, φ j) * rateLatency (R k) (T k) v)
        = rateLatencyNN ((φ i / ∑ j ∈ J k, φ j) * R k) (T k) := by
      funext v
      rw [rateLatencyNN_coe]
      show (((φ i / ∑ j ∈ J k, φ j) * (R k * (v - T k)) : ℝ≥0) : ℝ≥0∞)
        = ((((φ i / ∑ j ∈ J k, φ j) * R k) * (v - T k) : ℝ≥0) : ℝ≥0∞)
      rw [mul_assoc]
    have hαk : Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, T j))
        = affine r (b + r * ∑ j ∈ Finset.range k, T j) := by funext t; rw [affine_coe]
    rw [hres, hαk, minDeconv_affine_rateLatencyNN r _ ((φ i / ∑ j ∈ J k, φ j) * R k) (T k) (hr k hk)]
    have hαk1 : Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range (k + 1), T j))
        = affine r (b + r * ∑ j ∈ Finset.range k, T j + r * T k) := by
      funext t; rw [affine_coe, Finset.sum_range_succ]; push_cast; ring_nf
    rw [hαk1]
  · intro k hk
    show longTermArrivalRate (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, T j))
        < longTermServiceRate (fun v => (φ i / ∑ j ∈ J k, φ j) * rateLatency (R k) (T k) v)
    rw [longTermArrivalRate_affine, longTermServiceRate_const_mul, longTermServiceRate_rateLatency,
      ← ENNReal.coe_mul]
    exact_mod_cast hstab k hk

/-- **The critical flow's per-server arrival bound** (the `σ` the network harr
aggregation consumes): along a path of GPS servers with rate-latency aggregate
service and `Fl(h)`-shares, a token-bucket flow `γ_{r,b}` (with `r ≤` its share at
each hop) has arrival curve `r·t + (b + r·∑_{j<k} Tⱼ)` at every server `k` on its
path — the ingress burst grown by the accumulated `r·∑T`. Pure propagation
(`isMaximalArrivalBound_path`), no local-stability hypothesis. -/
theorem isMaximalArrivalBound_gpsPathOn_tokenBucket {ι : Type*} {n : ℕ}
    {Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop} {φ : ι → ℝ≥0} {i : ι} {r b : ℝ≥0}
    {R T : ℕ → ℝ≥0} {J : ℕ → Finset ι} (hi : ∀ k, i ∈ J k) (hcaus : ∀ k, IsCausalN (Sf k))
    (hβf : ∀ k, IsStrictMinimalServiceCurve (rateLatency (R k) (T k)) (aggregateServerOn (Sf k) (J k)))
    (hgps : ∀ k, IsGpsServerN φ (Sf k)) (proc : ℕ → Curve)
    (hchain : ∀ k, k < n → residualServer (Sf k) i (proc k) (proc (k + 1)))
    (harr0 : IsMaximalArrivalBound (⇑(proc 0)) (fun t => r * t + b))
    (hr : ∀ k, k < n → r ≤ (φ i / ∑ j ∈ J k, φ j) * R k) :
    ∀ k, k ≤ n → IsMaximalArrivalBound (⇑(proc k))
      (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, T j)) := by
  refine isMaximalArrivalBound_path (S := fun k => residualServer (Sf k) i)
    (β := fun k => fun v => (φ i / ∑ j ∈ J k, φ j) * rateLatency (R k) (T k) v)
    (fun k => isCausal_residualServer (hcaus k) i)
    (fun k => isStrictMinimalServiceCurve_residualServer_of_isGps_on (hi k) (hcaus k) (hβf k) (hgps k))
    id proc (fun k t => r * t + (b + r * ∑ j ∈ Finset.range k, T j)) hchain (by simpa using harr0) ?_
  intro k hk
  show minDeconv (Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, T j)))
      (Deviation.liftENN (fun v => (φ i / ∑ j ∈ J k, φ j) * rateLatency (R k) (T k) v))
    ≤ Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range (k + 1), T j))
  have hres : Deviation.liftENN (fun v => (φ i / ∑ j ∈ J k, φ j) * rateLatency (R k) (T k) v)
      = rateLatencyNN ((φ i / ∑ j ∈ J k, φ j) * R k) (T k) := by
    funext v
    rw [rateLatencyNN_coe]
    show (((φ i / ∑ j ∈ J k, φ j) * (R k * (v - T k)) : ℝ≥0) : ℝ≥0∞)
      = ((((φ i / ∑ j ∈ J k, φ j) * R k) * (v - T k) : ℝ≥0) : ℝ≥0∞)
    rw [mul_assoc]
  have hαk : Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range k, T j))
      = affine r (b + r * ∑ j ∈ Finset.range k, T j) := by funext t; rw [affine_coe]
  rw [hres, hαk, minDeconv_affine_rateLatencyNN r _ ((φ i / ∑ j ∈ J k, φ j) * R k) (T k) (hr k hk)]
  have hαk1 : Deviation.liftENN (fun t => r * t + (b + r * ∑ j ∈ Finset.range (k + 1), T j))
      = affine r (b + r * ∑ j ∈ Finset.range k, T j + r * T k) := by
    funext t; rw [affine_coe, Finset.sum_range_succ]; push_cast; ring_nf
  rw [hαk1]

end DeepWiki
