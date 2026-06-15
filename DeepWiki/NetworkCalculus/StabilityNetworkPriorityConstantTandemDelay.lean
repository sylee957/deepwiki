import DeepWiki.NetworkCalculus.StabilityNetworkPriorityConstantTandem
import DeepWiki.NetworkCalculus.StabilityNetworkPriorityConstantEndToEnd

/-! # End-to-end delay / backlog for the shared-path static-priority tandem
The SP analogue of `GpsTandem`'s end-to-end results: `SpTandem.toTraj` packages a shared-path SP
tandem as a `SpNetwork.Traj`, and the network-wide capstone then gives every flow a finite end-to-end
delay and backlog (ingress `traj 0` → egress `traj m`) on the book's §11.1 canonical tandem. -/

namespace DeepWiki.SpTandem

open DeepWiki
open scoped Classical NNReal ENNReal BigOperators

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- The shared-path SP tandem as a `SpNetwork.Traj` (every flow follows the same `m`-hop line). -/
noncomputable def toTraj (t : Tandem ι m) (hm : 0 < m) : SpNetwork.Traj (Fin m) ι where
  net := toNetwork t
  h0 := ⟨0, hm⟩
  S := fun h => t.Sf h.val
  R := fun h => t.R h.val
  T := fun h => t.T h.val
  r := t.r
  b := t.b
  Ain := fun h i => t.traj h.val i
  Dout := fun h i => t.traj (h.val + 1) i
  hcaus := fun h => t.hcaus h.val
  hβ := fun h => t.hβf h.val
  hSP := fun h => t.hSP h.val
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

/-- The `toTraj` packaging's `proc` endpoints are the tandem's ingress `traj 0` and egress `traj m`. -/
theorem toTraj_procEndpoints (t : Tandem ι m) (hm : 0 < m) (i : ι) :
    (toTraj t hm).net.paths i ≠ [] ∧
      (toTraj t hm).proc i 0 = t.traj 0 i ∧
      (toTraj t hm).proc i ((toTraj t hm).net.paths i).length = t.traj m i := by
  have hlen : ((toTraj t hm).net.paths i).length = m := by rw [toTraj]; simp [toNetwork]
  refine ⟨by rw [← List.length_pos_iff_ne_nil, hlen]; exact hm, ?_, ?_⟩
  · rw [SpNetwork.Traj.proc_zero (toTraj t hm) i (by rw [hlen]; exact hm)]; rfl
  · have hm1 : m - 1 < m := Nat.sub_lt hm one_pos
    rw [hlen, SpNetwork.Traj.proc, if_neg (by rw [hlen]; exact lt_irrefl m), hlen,
      SpNetwork.Traj.hopServer_eq_get (toTraj t hm) i (by rw [hlen]; exact hm1)]
    simp only [toTraj, toNetwork, List.get_eq_getElem, List.getElem_finRange, Fin.val_cast]
    congr 1
    omega

/-- **End-to-end delay, shared-path SP tandem**: a flow crossing the `m`-hop line of a locally stable
static-priority tandem has finite end-to-end delay `traj 0 → traj m`. -/
theorem isFlowEndToEndDelayBounded (t : Tandem ι m) (hm : 0 < m) (i : ι) :
    ∃ d : ℝ≥0, Deviation.delay (⇑(t.traj 0 i)) (⇑(t.traj m i)) ≤ (d : ℝ≥0∞) := by
  obtain ⟨hne, h0, hL⟩ := toTraj_procEndpoints t hm i
  obtain ⟨d, hd⟩ := (toTraj t hm).isFlowEndToEndDelayBounded i hne
  rw [h0, hL] at hd
  exact ⟨d, hd⟩

/-- **End-to-end backlog, shared-path SP tandem**: the same flow has finite end-to-end backlog. -/
theorem isFlowEndToEndBacklogBounded (t : Tandem ι m) (hm : 0 < m) (i : ι) :
    ∃ c : ℝ≥0, Deviation.backlog (⇑(t.traj 0 i)) (⇑(t.traj m i)) ≤ (c : ℝ≥0∞) := by
  obtain ⟨hne, h0, hL⟩ := toTraj_procEndpoints t hm i
  obtain ⟨c, hc⟩ := (toTraj t hm).isFlowEndToEndBacklogBounded i hne
  rw [h0, hL] at hc
  exact ⟨c, hc⟩

end DeepWiki.SpTandem
