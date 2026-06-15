import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstantTandem
import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstantEndToEnd

/-! # End-to-end delay / backlog for the shared-path GPS tandem
The network-wide capstone (`GpsNetwork.Traj.isFlowEndToEndDelayBounded` /
`…BacklogBounded`) read on the canonical shared-path tandem (the book's §11.1 worked setting): a flow
crossing the `m`-hop line of a locally stable GPS tandem has finite end-to-end delay and backlog from
ingress `traj 0` to egress `traj m`. Obtained by applying the capstone through `GpsTandem.toTraj`
and reading its `proc` endpoints back as `traj 0` / `traj m`. -/

namespace DeepWiki.GpsTandem

open DeepWiki
open scoped Classical NNReal ENNReal BigOperators

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- The `toTraj` packaging's `proc` endpoints are the tandem's ingress `traj 0` and egress `traj m`
(and its path is nonempty). -/
theorem toTraj_procEndpoints (t : Tandem ι m) (hm : 0 < m) (i : ι) :
    (toTraj t hm).net.paths i ≠ [] ∧
      (toTraj t hm).proc i 0 = t.traj 0 i ∧
      (toTraj t hm).proc i ((toTraj t hm).net.paths i).length = t.traj m i := by
  have hlen : ((toTraj t hm).net.paths i).length = m := by rw [toTraj]; simp [toNetwork]
  refine ⟨by rw [← List.length_pos_iff_ne_nil, hlen]; exact hm, ?_, ?_⟩
  · rw [GpsNetwork.Traj.proc_zero (toTraj t hm) i (by rw [hlen]; exact hm)]; rfl
  · have hm1 : m - 1 < m := Nat.sub_lt hm one_pos
    rw [hlen, GpsNetwork.Traj.proc, if_neg (by rw [hlen]; exact lt_irrefl m), hlen,
      GpsNetwork.Traj.hopServer_eq_get (toTraj t hm) i (by rw [hlen]; exact hm1)]
    simp only [toTraj, toNetwork, List.get_eq_getElem, List.getElem_finRange, Fin.val_cast]
    congr 1
    omega

/-- **End-to-end delay, shared-path GPS tandem**: a flow crossing the `m`-hop line of a locally stable
GPS tandem has finite end-to-end delay `traj 0 → traj m`. -/
theorem isFlowEndToEndDelayBounded (t : Tandem ι m) (hm : 0 < m) (i : ι) :
    ∃ d : ℝ≥0, Deviation.delay (⇑(t.traj 0 i)) (⇑(t.traj m i)) ≤ (d : ℝ≥0∞) := by
  obtain ⟨hne, h0, hL⟩ := toTraj_procEndpoints t hm i
  obtain ⟨d, hd⟩ := (toTraj t hm).isFlowEndToEndDelayBounded i hne
  rw [h0, hL] at hd
  exact ⟨d, hd⟩

/-- **End-to-end backlog, shared-path GPS tandem**: the same flow has finite end-to-end backlog. -/
theorem isFlowEndToEndBacklogBounded (t : Tandem ι m) (hm : 0 < m) (i : ι) :
    ∃ c : ℝ≥0, Deviation.backlog (⇑(t.traj 0 i)) (⇑(t.traj m i)) ≤ (c : ℝ≥0∞) := by
  obtain ⟨hne, h0, hL⟩ := toTraj_procEndpoints t hm i
  obtain ⟨c, hc⟩ := (toTraj t hm).isFlowEndToEndBacklogBounded i hne
  rw [h0, hL] at hc
  exact ⟨c, hc⟩

end DeepWiki.GpsTandem
