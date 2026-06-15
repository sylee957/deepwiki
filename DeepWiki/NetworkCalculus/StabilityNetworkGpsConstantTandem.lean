import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstant
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstantGeneral
import DeepWiki.NetworkCalculus.StabilityNetworkTrajectory
import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.ServersResidualGps
import DeepWiki.NetworkCalculus.ServersMimo

/-! # Theorem 12.5 (GPS constant rates: local ⟹ global stability), shared-path tandem
The **shared-path tandem** special case: all flows `ι` traverse the *same* line of `m` GPS
rate-latency servers (`traj k` is the per-flow input vector at hop `k`, the GPS server `Sf k`
carrying `traj k` to `traj (k+1)`, each hop offering a strict rate-latency `β_{R k, T k}` to
the shared weights `φ`, each flow a token bucket at ingress). Aggregate local stability
`∑ⱼ rⱼ < R^(k)` at every hop forces global stability at every hop.

This now reads as a **corollary of the fully general network theorem**
(`GpsNetwork.Traj.isGloballyStable`, `StabilityNetworkGpsConstantGeneral`): the tandem is the
general trajectory model with routing `net.paths = List.finRange m` (so `Fl(h) = univ` at every
hop), packaged by `toTraj`. The dedicated `Tandem` structure remains a convenient line-topology
API. Helpers live in the `GpsTandem` sub-namespace. -/

namespace DeepWiki.GpsTandem

open scoped Classical NNReal ENNReal
open DeepWiki

/-- The data of a shared-path GPS tandem — all flows `ι` traverse the same `m` hops, hop `k`'s
GPS server `Sf k` carrying `traj k` to `traj (k+1)`, each hop offering a strict rate-latency
`β_{R k, T k}` to the shared GPS weights `φ`, each flow a token bucket `γ_{r i, b i}` at ingress,
with aggregate local stability `∑ᵢ rᵢ < R k`. -/
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

/-- The shared-path tandem as a `Network (Fin m) ι`: every flow takes the same path
`List.finRange m`, hop `h` offers rate-latency `β_{R h, T h}`, ingress is the hop-0 process. -/
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

/-- A positive-length shared-path tandem as a general `GpsNetwork.Traj` over `Fin m`: the routing
is `List.finRange m` (so `Fl(h) = univ`), the per-flow input/output at hop `h` are `traj h`,
`traj (h+1)`, and the default server is the first hop `⟨0, hm⟩`. -/
noncomputable def toTraj (t : Tandem ι m) (hm : 0 < m) : GpsNetwork.Traj (Fin m) ι where
  net := toNetwork t
  h0 := ⟨0, hm⟩
  S := fun h => t.Sf h.val
  φ := t.φ
  hφ := t.hφ
  R := fun h => t.R h.val
  T := fun h => t.T h.val
  r := t.r
  b := t.b
  Ain := fun h i => t.traj h.val i
  Dout := fun h i => t.traj (h.val + 1) i
  hcaus := fun h => t.hcaus h.val
  hβ := fun h => t.hβf h.val
  hgps := fun h => t.hgps h.val
  hp := fun h => t.hchain h.val h.isLt
  hservice := fun h => rfl
  hingress := fun i hP => by
    rw [show ((toNetwork t).paths i).get ⟨0, hP⟩ = (⟨0, hm⟩ : Fin m) by
      simp [toNetwork, List.getElem_finRange]]
    rfl
  hwire := fun i k hk => by
    have hpath : (toNetwork t).paths i = List.finRange m := rfl
    have hk' : k + 1 < m := by simpa [hpath] using hk
    have hk0 : k < m := Nat.lt_of_succ_lt hk'
    rw [show ((toNetwork t).paths i).get ⟨k + 1, hk⟩ = (⟨k + 1, hk'⟩ : Fin m) by
        simp [hpath, List.getElem_finRange],
      show ((toNetwork t).paths i).get ⟨k, Nat.lt_of_succ_lt hk⟩ = (⟨k, hk0⟩ : Fin m) by
        simp [hpath, List.getElem_finRange]]
  hoff := fun h i hi => absurd (by rw [toNetwork_flowsThrough]; exact Finset.mem_univ i) hi
  harr0 := t.harr0
  hstab := fun h => by rw [toNetwork_flowsThrough]; exact t.hstab h.val

/-- **Theorem 12.5, shared-path tandem**: a locally stable shared-path GPS-constant tandem is
globally stable at every hop — the aggregate input/output at each server has a bounded backlogged
period. A corollary of the general network theorem `GpsNetwork.Traj.isGloballyStable` via the
`toTraj` packaging (the empty tandem `m = 0` is vacuous). -/
theorem isGloballyStable_sharedPath_tandem (t : Tandem ι m) :
    ∀ h : Fin m, IsGloballyStableServer
      (⇑(∑ i, t.traj h.val i)) (⇑(∑ i, t.traj (h.val + 1) i)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact fun h => h.elim0
  · exact (toTraj t hm).isGloballyStable

/-! ## Book restatement (Theorem 12.5, shared-path tandem)
A locally stable GPS-constant tandem in which every flow follows the same `m`-hop line, each hop
offering a strict rate-latency aggregate service to its GPS relation and each flow a token bucket
at ingress, is globally stable at every hop. The only hypothesis consumed beyond the structure is
aggregate local stability `∑ᵢ rᵢ < R^(h)` at every hop. -/
example (t : Tandem ι m) (h : Fin m) :
    IsGloballyStableServer
      (⇑(∑ i, t.traj h.val i)) (⇑(∑ i, t.traj (h.val + 1) i)) :=
  isGloballyStable_sharedPath_tandem t h

end DeepWiki.GpsTandem
