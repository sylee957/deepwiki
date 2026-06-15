import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstant
import DeepWiki.NetworkCalculus.StabilityNetworkTrajectory
import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.ServersResidualGps
import DeepWiki.NetworkCalculus.ServersMimo
import DeepWiki.NetworkCalculus.ServersResidual
import DeepWiki.NetworkCalculus.ArrivalCurvesAggregate

/-! # Theorem 12.5 (GPS constant rates: local ⟹ global stability), shared-path tandem
The cyclic-peeling assembly of the GPS-constant per-flow engine
(`StabilityNetworkGpsConstant`) into the network-level global-stability theorem, for the
**shared-path tandem**: all flows `ι` traverse the *same* line of `m` GPS rate-latency
servers. `traj k` is the per-flow input vector at hop `k`; the GPS server `Sf k` carries
`traj k` to `traj (k+1)`, its aggregate offering a strict rate-latency `β_{R k, T k}` with
shared weights `φ`; each flow `i` is token-bucket `γ_{r i, b i}` at ingress. Aggregate local
stability `∑ⱼ rⱼ < R^(k)` at every hop forces global stability at every hop, by peeling
flows in increasing `rⱼ/φⱼ` order: the active-set critical flow is below its GPS share of the
residual capacity (`exists_flow_below_residual_share`), hence globally stable and
token-bucket bounded along the line (the per-flow induction body
`isMaximalArrivalBound_gpsPeelPath_tokenBucket`); remove it and recurse on the rest, then
aggregate the per-flow bounds (`Network.isGloballyStable_of_perFlow_bounds`). The
shared-path/`Fl(h)=univ` restriction collapses the list-path↔hop-index bridge to the
identity ℕ-indexing; the variable-per-server-population general network is the
remaining generalization. Helpers live in the `GpsTandem` sub-namespace (their short
names — `HopBound`, `peelStep` — would clash in `DeepWiki`). -/

namespace DeepWiki.GpsTandem

open scoped Classical NNReal ENNReal
open DeepWiki

/-- The peeling invariant carrier: the data of a shared-path GPS tandem — all flows `ι`
traverse the same `m` hops, hop `k`'s GPS server `Sf k` carrying `traj k` to `traj (k+1)`,
each hop offering a strict rate-latency `β_{R k, T k}` to the shared GPS weights `φ`, each
flow a token bucket `γ_{r i, b i}` at ingress, with aggregate local stability `∑ᵢ rᵢ < R k`. -/
structure Tandem (ι : Type*) [Fintype ι] (m : ℕ) where
  /-- The per-hop GPS server relations (over the full flow set). -/
  Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop
  /-- The GPS weights, positive. -/
  φ : ι → ℝ≥0
  /-- The GPS weights are positive. -/
  hφ : ∀ j, 0 < φ j
  /-- Per-hop rate of the aggregate service. -/
  R : ℕ → ℝ≥0
  /-- Per-hop latency of the aggregate service. -/
  T : ℕ → ℝ≥0
  /-- Per-flow rate at hop 0. -/
  r : ι → ℝ≥0
  /-- Per-flow burst at hop 0. -/
  b : ι → ℝ≥0
  /-- The trajectory: `traj k` is the per-flow input vector at hop `k`. -/
  traj : ℕ → (ι → Curve)
  /-- Each hop's server is per-flow causal. -/
  hcaus : ∀ k, IsCausalN (Sf k)
  /-- Each hop's aggregate offers strict rate-latency service `β_{R k, T k}`. -/
  hβf : ∀ k, IsStrictMinimalServiceCurve (rateLatency (R k) (T k)) (aggregateServer (Sf k))
  /-- Each hop's server respects the GPS proportional shares. -/
  hgps : ∀ k, IsGpsServerN φ (Sf k)
  /-- The shared-path chaining: hop `k`'s output is hop `(k+1)`'s input. -/
  hchain : ∀ k, k < m → Sf k (traj k) (traj (k + 1))
  /-- Each flow is token-bucket constrained at hop 0. -/
  harr0 : ∀ i, IsMaximalArrivalBound (⇑(traj 0 i)) (fun t => r i * t + b i)
  /-- Aggregate local stability at every hop. -/
  hstab : ∀ k, ∑ i, r i < R k

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- Flow `i` has a per-hop token-bucket arrival bound of rate `r i` at every hop. -/
def HopBound (t : Tandem ι m) (i : ι) : Prop :=
  ∀ k, k ≤ m → ∃ B : ℝ≥0, IsMaximalArrivalBound (⇑(t.traj k i)) (fun s => t.r i * s + B)

/-- A family of flows, all `HopBound`, gives at each hop a single token-bucket bound
on their aggregate departure of rate `∑_{j∈s} r j` — packaged with the burst. -/
theorem aggregateHopBound (t : Tandem ι m) (s : Finset ι)
    (hs : ∀ j ∈ s, HopBound t j) (k : ℕ) (hk : k ≤ m) :
    ∃ bb : ℝ≥0, IsMaximalArrivalBound (fun x => ∑ j ∈ s, (t.traj k j) x)
      (fun v => (∑ j ∈ s, t.r j) * v + bb) := by
  classical
  -- choose per-flow bursts (total function, junk off `s`)
  have hch : ∀ j : ι, ∃ B : ℝ≥0, j ∈ s →
      IsMaximalArrivalBound (⇑(t.traj k j)) (fun s' => t.r j * s' + B) := by
    intro j
    by_cases hj : j ∈ s
    · obtain ⟨B, hB⟩ := hs j hj k hk; exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose B hB using hch
  refine ⟨∑ j ∈ s, B j, ?_⟩
  have hsum := isMaximalArrivalBound_sum (T := ℝ≥0) s
    (A := fun j => ⇑(t.traj k j)) (α := fun j s' => t.r j * s' + B j)
    (fun j hj => hB j hj)
  -- `∑ⱼ (rⱼ v + Bⱼ) = (∑ⱼ rⱼ) v + ∑ⱼ Bⱼ`
  have hreshape : (fun v => ∑ j ∈ s, (t.r j * v + B j))
      = (fun v => (∑ j ∈ s, t.r j) * v + ∑ j ∈ s, B j) := by
    funext v
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hreshape] at hsum
  exact hsum

/-- Choose a burst function `bb : ℕ → ℝ≥0` for the peeled aggregate `s`: at every
hop `k ≤ m`, `∑_{j∈s} traj k j` is `((∑_{j∈s} rⱼ)·v + bb k)`-bounded. -/
theorem exists_aggregate_bb (t : Tandem ι m) (s : Finset ι)
    (hs : ∀ j ∈ s, HopBound t j) :
    ∃ bb : ℕ → ℝ≥0, ∀ k, k ≤ m →
      IsMaximalArrivalBound (fun x => ∑ j ∈ s, (t.traj k j) x)
        (fun v => (∑ j ∈ s, t.r j) * v + bb k) := by
  classical
  have hch : ∀ k : ℕ, ∃ bb : ℝ≥0, k ≤ m →
      IsMaximalArrivalBound (fun x => ∑ j ∈ s, (t.traj k j) x)
        (fun v => (∑ j ∈ s, t.r j) * v + bb) := by
    intro k
    by_cases hk : k ≤ m
    · obtain ⟨bb, hbb⟩ := aggregateHopBound t s hs k hk; exact ⟨bb, fun _ => hbb⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose bb hbb using hch
  exact ⟨bb, fun k hk => hbb k hk⟩

/-- **The peeling step**: with the already-peeled flows `Jᶜ` all `HopBound`, a critical
flow `i ∈ J` whose rate stays below its GPS share of the residual capacity
`R k − ∑_{j∈Jᶜ} rⱼ` at every hop is itself `HopBound`. Invokes the engine's induction
body `isMaximalArrivalBound_gpsPeelPath_tokenBucket`. -/
theorem peelStep (t : Tandem ι m) (J : Finset ι) {i : ι} (hiJ : i ∈ J)
    (hpeeled : ∀ j ∈ Jᶜ, HopBound t j)
    (hcrit : ∀ k, k < m →
      t.r i < t.φ i * (t.R k - ∑ j ∈ Jᶜ, t.r j) / (∑ j ∈ J, t.φ j)) :
    HopBound t i := by
  classical
  -- residual rate from the peeled flows
  set ρ : ℕ → ℝ≥0 := fun _ => ∑ j ∈ Jᶜ, t.r j with hρdef
  -- `ρ k < R k`: the peeled rates are part of `∑ᵢ rᵢ < R k`
  have hρR : ∀ k, ρ k < t.R k := by
    intro k
    refine lt_of_le_of_lt ?_ (t.hstab k)
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  -- the peeled aggregate's burst bound at each hop
  obtain ⟨bb, hbb⟩ := exists_aggregate_bb t Jᶜ hpeeled
  -- burst supplied to the body uses the OUTPUT-side bound at hop `k+1`
  set bb' : ℕ → ℝ≥0 := fun k => bb (k + 1) with hbb'def
  -- apply the engine body
  have hmab := isMaximalArrivalBound_gpsPeelPath_tokenBucket
    (ι := ι) (n := m) (Sf := t.Sf) (φ := t.φ) (i := i) (r := t.r i) (b := t.b i)
    (R := t.R) (T := t.T) (ρ := ρ) (bb := bb') (J := fun _ => J)
    (fun _ => hiJ) hρR t.hcaus t.hβf t.hgps (fun k => t.traj k i) ?_ (t.harr0 i) ?_
  · -- repackage into HopBound
    intro k hk
    exact ⟨t.b i + t.r i * ∑ j ∈ Finset.range k,
        (t.R j * t.T j + bb' j) / (t.R j - ρ j), hmab k hk⟩
  · -- hchain: the residual-with-peeled-bound carries `traj k i → traj (k+1) i`
    intro k hk
    refine ⟨t.traj k, t.traj (k + 1), ⟨t.hchain k hk, ?_⟩, rfl, rfl⟩
    -- the peeled departures `∑_{j∈Jᶜ} traj (k+1) j` are bounded by `ρ·v + bb' k`
    have h := hbb (k + 1) hk
    exact h
  · -- hr: `r i ≤ (φ i / ∑_{j∈J} φ j) * (R k - ρ k)`
    intro k hk
    have hcr := hcrit k hk
    rw [hρdef]
    rw [div_mul_eq_mul_div]
    exact le_of_lt hcr

/-- **Critical-flow existence** in the tandem: on a nonempty active set `J`, there is a
flow `i ∈ J` below its GPS share of the residual capacity `R k − ∑_{j∈Jᶜ} rⱼ` at every
hop (the `r/φ`-minimizer, via `exists_flow_below_residual_share`, bridged from ℝ). -/
theorem exists_critical (t : Tandem ι m) (J : Finset ι) (hJ : J.Nonempty) :
    ∃ i ∈ J, ∀ k, k < m →
      t.r i < t.φ i * (t.R k - ∑ j ∈ Jᶜ, t.r j) / (∑ j ∈ J, t.φ j) := by
  classical
  obtain ⟨i, hiJ, hi⟩ := exists_flow_below_residual_share (σ := ℕ) J hJ
    (fun j => (t.r j : ℝ)) (fun j => (t.φ j : ℝ))
    (fun j => by exact_mod_cast t.hφ j)
    (fun k => (t.R k : ℝ)) (fun _ => Finset.univ)
    (fun k => by
      rw [← NNReal.coe_sum]
      exact_mod_cast t.hstab k)
  refine ⟨i, hiJ, fun k hk => ?_⟩
  have hmem : i ∈ (Finset.univ : Finset ι) ∩ J := Finset.mem_inter.mpr ⟨Finset.mem_univ i, hiJ⟩
  have hiR := hi k hmem
  -- bridge `univ \ J = Jᶜ`, `univ ∩ J = J`
  rw [Finset.univ_inter] at hiR
  rw [show (Finset.univ : Finset ι) \ J = Jᶜ from rfl] at hiR
  -- the peeled rate sum is below `R k` (so truncated sub agrees with real sub)
  have hle : (∑ j ∈ Jᶜ, t.r j) ≤ t.R k :=
    le_of_lt (lt_of_le_of_lt
      (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) (t.hstab k))
  -- recast `hiR` (over ℝ) to the ℝ≥0 inequality
  rw [show ((t.R k : ℝ) - ∑ j ∈ Jᶜ, (t.r j : ℝ))
      = ((t.R k - ∑ j ∈ Jᶜ, t.r j : ℝ≥0) : ℝ) by
        rw [NNReal.coe_sub hle, NNReal.coe_sum]] at hiR
  rw [show (t.φ i : ℝ) * ((t.R k - ∑ j ∈ Jᶜ, t.r j : ℝ≥0) : ℝ) / (∑ j ∈ J, (t.φ j : ℝ))
      = ((t.φ i * (t.R k - ∑ j ∈ Jᶜ, t.r j) / (∑ j ∈ J, t.φ j) : ℝ≥0) : ℝ) by
        rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sum]] at hiR
  exact_mod_cast hiR

/-- **The outer peeling induction**: for any active set `J` whose peeled complement
`Jᶜ` is already `HopBound`, every flow `i ∈ J` is `HopBound`. Strong induction on
`J.card`: peel the critical flow (`exists_critical`), establish its bound (`peelStep`),
and recurse on `J.erase i` (whose complement `insert i Jᶜ` is now all `HopBound`). -/
theorem peelInduction (t : Tandem ι m) :
    ∀ (J : Finset ι), (∀ j ∈ Jᶜ, HopBound t j) → ∀ i ∈ J, HopBound t i := by
  classical
  intro J
  induction J using Finset.strongInduction with
  | _ J ih =>
    intro hpeeled i hiJ
    -- find the critical flow `c ∈ J`
    obtain ⟨c, hcJ, hcrit⟩ := exists_critical t J ⟨i, hiJ⟩
    -- `c` is HopBound by the peeling step
    have hcHop : HopBound t c := peelStep t J hcJ hpeeled hcrit
    -- the smaller active set `J.erase c` has complement `insert c Jᶜ`, all HopBound
    have hpeeled' : ∀ j ∈ (J.erase c)ᶜ, HopBound t j := by
      intro j hj
      rw [Finset.compl_erase, Finset.mem_insert] at hj
      rcases hj with rfl | hjJc
      · exact hcHop
      · exact hpeeled j hjJc
    -- recurse: every flow in `J.erase c` is HopBound
    have hrest : ∀ j ∈ J.erase c, HopBound t j :=
      ih (J.erase c) (Finset.erase_ssubset hcJ) hpeeled'
    -- now `i`: either `i = c` or `i ∈ J.erase c`
    rcases eq_or_ne i c with rfl | hic
    · exact hcHop
    · exact hrest i (Finset.mem_erase.mpr ⟨hic, hiJ⟩)

/-- Every flow in a shared-path GPS tandem is `HopBound`: instantiate the outer
peeling at `J = univ` (whose complement `∅` is vacuously `HopBound`). -/
theorem allHopBound (t : Tandem ι m) (i : ι) : HopBound t i := by
  refine peelInduction t Finset.univ ?_ i (Finset.mem_univ i)
  intro j hj
  rw [Finset.compl_univ] at hj
  exact absurd hj (Finset.notMem_empty j)

/-! ## Final assembly into the `Network` model
We package the shared-path tandem as a genuine `Network (Fin m) ι`: hop `h : Fin m`
is a server offering rate-latency `β_{R h, T h}`, all flows take the same path
`List.finRange m`, the per-flow input at server `h` is `traj h i` and output
`traj (h+1) i`. The per-flow `HopBound` curves are the `σ` that
`Network.isGloballyStable_of_perFlow_bounds` aggregates. -/

/-- The shared-path tandem as a `Network (Fin m) ι`. -/
noncomputable def toNetwork (t : Tandem ι m) : Network (Fin m) ι where
  paths := fun _ => List.finRange m
  arrival := fun i => t.traj 0 i
  arrivalCurve := fun i => fun s => t.r i * s + t.b i
  service := fun h => rateLatency (t.R h.val) (t.T h.val)

omit [DecidableEq ι] in
/-- In the tandem network every flow crosses every server. -/
theorem toNetwork_flowsThrough (t : Tandem ι m) (h : Fin m) :
    (toNetwork t).flowsThrough h = Finset.univ := by
  ext i
  simp only [Network.mem_flowsThrough, toNetwork, Finset.mem_univ,
    List.mem_finRange]

/-- **Theorem 12.5, shared-path tandem**: a locally stable shared-path GPS-constant tandem
is globally stable at every hop. Each server `h : Fin m` of the network `toNetwork t`
offers strict rate-latency aggregate service to its GPS relation; the aggregate local
stability `∑ᵢ rᵢ < R^(h)` forces every server's aggregate to have a bounded backlogged
period. Assembled by feeding the per-flow `HopBound` curves (from the peeling induction
`allHopBound`) to `Network.isGloballyStable_of_perFlow_bounds`. -/
theorem isGloballyStable_sharedPath_tandem (t : Tandem ι m) :
    ∀ h : Fin m, IsGloballyStableServer
      (⇑(∑ i, t.traj h.val i)) (⇑(∑ i, t.traj (h.val + 1) i)) := by
  classical
  -- the per-flow HopBound bursts, as a total function over `(h, i)`
  have hHop : ∀ (h : Fin m) (i : ι), ∃ B : ℝ≥0,
      IsMaximalArrivalBound (⇑(t.traj h.val i)) (fun s => t.r i * s + B) := fun h i =>
    allHopBound t i h.val (le_of_lt h.isLt)
  choose B hB using hHop
  set σ : Fin m → ι → ℝ≥0 → ℝ≥0 := fun h i => fun s => t.r i * s + B h i with hσdef
  -- assemble via the network aggregation lemma
  have hmain := (toNetwork t).isGloballyStable_of_perFlow_bounds
    (S := fun h => t.Sf h.val)
    (Ain := fun h i => t.traj h.val i)
    (Dout := fun h i => t.traj (h.val + 1) i)
    (σ := σ)
    (fun h => t.hcaus h.val)
    (fun h => t.hβf h.val)
    (fun h => t.hchain h.val h.isLt)
    (fun h i => hB h i)
    ?_
  · exact hmain
  · -- local stability of `∑ᵢ σ h i` against `net.service h = β_{R h, T h}`
    intro h
    show IsLocallyStableServer (fun s => ∑ i, σ h i s)
      (rateLatency (t.R h.val) (t.T h.val))
    -- `∑ᵢ σ h i s = (∑ᵢ rᵢ)·s + ∑ᵢ Bₕᵢ` — affine with rate `∑ᵢ rᵢ`
    have hcurve : (fun s => ∑ i, σ h i s)
        = fun s => (∑ i, t.r i) * s + ∑ i, B h i := by
      funext s
      simp only [hσdef]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hcurve]
    show longTermArrivalRate (fun s => (∑ i, t.r i) * s + ∑ i, B h i)
      < longTermServiceRate (rateLatency (t.R h.val) (t.T h.val))
    rw [longTermArrivalRate_affine, longTermServiceRate_rateLatency]
    exact_mod_cast t.hstab h.val

/-! ## Book restatement (Theorem 12.5, shared-path tandem)
A locally stable GPS-constant tandem in which every flow follows the same `m`-hop
line, each hop offering a strict rate-latency aggregate service to its GPS relation
and each flow a token bucket at ingress, is globally stable at every hop: the
aggregate input/output at hop `h` has a bounded backlogged period. The only
hypothesis consumed beyond the structure is aggregate local stability
`∑ᵢ rᵢ < R^(h)` at every hop. -/
example (t : Tandem ι m) (h : Fin m) :
    IsGloballyStableServer
      (⇑(∑ i, t.traj h.val i)) (⇑(∑ i, t.traj (h.val + 1) i)) :=
  isGloballyStable_sharedPath_tandem t h

end DeepWiki.GpsTandem
