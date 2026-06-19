import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstantGeneral
import DeepWiki.NetworkCalculus.ServersResidualSfaDelay

/-! # Per-flow end-to-end delay / backlog in a stable GPS network (capstone)
The GPS analogue of the static-priority capstone: a locally stable GPS-constant network `Traj` yields
*finite end-to-end delay and backlog* for every flow, via the SFA blind-multiplexing end-to-end bound
(which needs only the strict rate-latency aggregate, so it applies to GPS). The bridge is
`concatComp_of_chain` over flow `i`'s per-hop trajectory `proc`; cross-traffic from `allBound`;
stability from `∑_{Fl h} r < R^(h)`. The shared assembly is `sfaEndToEndSetup`. -/

open DeepWiki
open scoped Classical NNReal ENNReal BigOperators

namespace DeepWiki.GpsNetwork.Traj

variable {κ ι : Type*} [Fintype ι] [DecidableEq κ]

/-- **The SFA blind-multiplexing end-to-end setup for a stable GPS network**: flow `i`'s per-hop
trajectory realizes the SFA `concatComp` chain along its path, with affine cross-traffic, per-server
stability, and a token-bucket ingress — everything `delay_le_sfa_rateLatency` /
`backlog_le_sfa_rateLatency` need (`ρ^(h) = ∑_{j≠i, j∈Fl h} rⱼ`). -/
theorem sfaEndToEndSetup (t : Traj κ ι) (i : ι) (hne : t.net.paths i ≠ []) :
    ∃ (α : κ → ι → ℝ≥0 → ℝ≥0) (ρ bc : κ → ℝ≥0) (head : κ) (tail : List κ),
      t.net.paths i = head :: tail ∧
      (∀ h, (fun v => ∑ j ∈ Finset.univ.erase i, α h j v) = fun v => ρ h * v + bc h) ∧
      (∀ h, ρ h < t.R h) ∧
      concatComp (fun h => residualServer (fun A D => t.S h A D ∧
        ∀ j, j ≠ i → IsMaximalArrivalBound (⇑(A j)) (α h j)) i) (head :: tail)
        (t.proc i 0) (t.proc i (head :: tail).length) ∧
      IsMaximalArrivalBound (⇑(t.proc i 0)) (fun s => t.r i * s + t.b i) ∧
      0 < pathMinRate (fun h => t.R h - ρ h) head tail ∧
      t.r i ≤ pathMinRate (fun h => t.R h - ρ h) head tail := by
  classical
  obtain ⟨head, tail, hpath⟩ := List.exists_cons_of_ne_nil hne
  have hlen : 0 < (t.net.paths i).length := by rw [hpath]; simp
  have hch : ∀ j : ι, ∃ B : κ → ℝ≥0, ∀ h, j ∈ t.net.flowsThrough h →
      IsMaximalArrivalBound (⇑(t.Ain h j)) (fun s => t.r j * s + B h) := by
    intro j; obtain ⟨B, hin, _⟩ := t.allBound j; exact ⟨B, hin⟩
  choose B hB using hch
  set α : κ → ι → ℝ≥0 → ℝ≥0 :=
    fun h j => if j ∈ t.net.flowsThrough h then (fun v => t.r j * v + B j h) else 0 with hαdef
  set ρ : κ → ℝ≥0 :=
    fun h => ∑ j ∈ (Finset.univ.erase i).filter (fun j => j ∈ t.net.flowsThrough h), t.r j with hρdef
  set bc : κ → ℝ≥0 :=
    fun h => ∑ j ∈ (Finset.univ.erase i).filter (fun j => j ∈ t.net.flowsThrough h), B j h with hbcdef
  have hcross : ∀ h, (fun v => ∑ j ∈ Finset.univ.erase i, α h j v) = fun v => ρ h * v + bc h := by
    intro h; funext v
    rw [hρdef, hbcdef, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hαdef]
    by_cases hjc : j ∈ t.net.flowsThrough h <;> simp [hjc]
  have hsubF : ∀ h, (Finset.univ.erase i).filter (fun j => j ∈ t.net.flowsThrough h)
      ⊆ t.net.flowsThrough h := fun h j hj => (Finset.mem_filter.mp hj).2
  have hkey : ∀ h ∈ t.net.paths i, t.r i < t.R h - ρ h := by
    intro h hh
    have hiFl : i ∈ t.net.flowsThrough h := Network.mem_flowsThrough.mpr hh
    have hset : insert i ((Finset.univ.erase i).filter (fun j => j ∈ t.net.flowsThrough h))
        = t.net.flowsThrough h := by
      ext j
      rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨_, hj⟩)
        · exact hiFl
        · exact hj
      · intro hj
        by_cases hji : j = i
        · exact Or.inl hji
        · exact Or.inr ⟨⟨hji, Finset.mem_univ j⟩, hj⟩
    rw [hρdef, lt_tsub_iff_right]
    calc t.r i + ∑ j ∈ (Finset.univ.erase i).filter (fun j => j ∈ t.net.flowsThrough h), t.r j
        = ∑ j ∈ insert i ((Finset.univ.erase i).filter
            (fun j => j ∈ t.net.flowsThrough h)), t.r j := (Finset.sum_insert (by simp)).symm
      _ = ∑ j ∈ t.net.flowsThrough h, t.r j := by rw [hset]
      _ < t.R h := t.hstab h
  have hRpos : 0 < pathMinRate (fun h => t.R h - ρ h) head tail := by
    apply pathMinRate_pos
    rw [← hpath]; exact fun h hh => lt_of_le_of_lt (zero_le (a := t.r i)) (hkey h hh)
  have hr : t.r i ≤ pathMinRate (fun h => t.R h - ρ h) head tail := by
    apply le_pathMinRate
    rw [← hpath]; exact fun h hh => (hkey h hh).le
  have hp : concatComp (fun h => residualServer (fun A D => t.S h A D ∧
      ∀ j, j ≠ i → IsMaximalArrivalBound (⇑(A j)) (α h j)) i) (head :: tail)
      (t.proc i 0) (t.proc i (head :: tail).length) := by
    rw [← hpath]
    refine concatComp_of_chain _ (t.net.paths i) (t.proc i) (fun k hk => ?_)
    rw [← hopServer_eq_get t i hk]
    refine ⟨t.Ain (t.hopServer i k), t.Dout (t.hopServer i k),
      ⟨t.hp (t.hopServer i k), ?_⟩, (proc_of_lt t i hk).symm, Dout_hopServer_eq_proc_succ t i hk⟩
    intro j _
    simp only [hαdef]
    by_cases hjc : j ∈ t.net.flowsThrough (t.hopServer i k)
    · simp only [if_pos hjc]; exact hB j (t.hopServer i k) hjc
    · simp only [if_neg hjc]
      rw [show t.Ain (t.hopServer i k) j = 0 from t.hoff _ j hjc, isMaximalArrivalBound_iff_increment]
      intro s d; simp only [Curve.zero_apply, zero_add]; positivity
  have harr : IsMaximalArrivalBound (⇑(t.proc i 0)) (fun s => t.r i * s + t.b i) := by
    rw [proc_zero t i hlen]; exact t.harr0 i
  have hstabρ : ∀ h, ρ h < t.R h := fun h => by
    rw [hρdef]; exact lt_of_le_of_lt (Finset.sum_le_sum_of_subset (hsubF h)) (t.hstab h)
  exact ⟨α, ρ, bc, head, tail, hpath, hcross, hstabρ, hp, harr, hRpos, hr⟩

/-- **Per-flow end-to-end delay in a stable GPS network**: every flow with a nonempty path has a
*finite end-to-end delay* (ingress to egress), via `sfaEndToEndSetup` + `delay_le_sfa_rateLatency`. -/
theorem isFlowEndToEndDelayBounded (t : Traj κ ι) (i : ι) (hne : t.net.paths i ≠ []) :
    ∃ d : ℝ≥0, Deviation.delay (⇑(t.proc i 0)) (⇑(t.proc i (t.net.paths i).length)) ≤ (d : ℝ≥0∞) := by
  obtain ⟨α, ρ, bc, head, tail, hpath, hcross, hstabρ, hp, harr, hRpos, hr⟩ := t.sfaEndToEndSetup i hne
  rw [hpath]
  exact ⟨_, delay_le_sfa_rateLatency (S := t.S) (R := t.R) (T := t.T) (α := α) (i := i)
    (ρ := ρ) (bc := bc) (r := t.r i) (b := t.b i) t.hcaus t.hβ hcross hstabρ hp harr hRpos hr⟩

/-- **Per-flow end-to-end backlog in a stable GPS network**: every flow with a nonempty path has a
*finite end-to-end backlog*, via `sfaEndToEndSetup` + `backlog_le_sfa_rateLatency`. -/
theorem isFlowEndToEndBacklogBounded (t : Traj κ ι) (i : ι) (hne : t.net.paths i ≠ []) :
    ∃ c : ℝ≥0, Deviation.backlog (⇑(t.proc i 0)) (⇑(t.proc i (t.net.paths i).length)) ≤ (c : ℝ≥0∞) := by
  obtain ⟨α, ρ, bc, head, tail, hpath, hcross, hstabρ, hp, harr, _hRpos, hr⟩ := t.sfaEndToEndSetup i hne
  rw [hpath]
  exact ⟨_, backlog_le_sfa_rateLatency (S := t.S) (R := t.R) (T := t.T) (α := α) (i := i)
    (ρ := ρ) (bc := bc) (r := t.r i) (b := t.b i) t.hcaus t.hβ hcross hstabρ hp harr hr⟩

/-- **Per-flow end-to-end output burstiness**: a flow's egress (last-server departure) from a stable
GPS network is again token-bucket `(rᵢ·s + B)`-bounded — the network preserves token-bucket
burstiness (compositionality). Immediate from the departure half of `allBound` at the last hop. -/
theorem isFlowEndToEndOutputBounded (t : Traj κ ι) (i : ι) (hne : t.net.paths i ≠ []) :
    ∃ B : ℝ≥0, IsMaximalArrivalBound (⇑(t.proc i (t.net.paths i).length)) (fun s => t.r i * s + B) := by
  obtain ⟨B, _, hBout⟩ := t.allBound i
  have hlast : (t.net.paths i).length - 1 < (t.net.paths i).length :=
    Nat.sub_lt (List.length_pos_of_ne_nil hne) one_pos
  refine ⟨B (t.hopServer i ((t.net.paths i).length - 1)), ?_⟩
  rw [show t.proc i (t.net.paths i).length
        = t.Dout (t.hopServer i ((t.net.paths i).length - 1)) i by
      simp only [proc, lt_self_iff_false, if_false]]
  exact hBout (t.hopServer i ((t.net.paths i).length - 1)) (mem_flowsThrough_hopServer t i hlast)

end DeepWiki.GpsNetwork.Traj
