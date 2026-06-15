import DeepWiki.NetworkCalculus.StabilityNetworkPriorityConstantGeneral
import DeepWiki.NetworkCalculus.ServersResidualSpPmooDelay

/-! # Per-flow end-to-end delay in a stable static-priority network (capstone)
Connecting the two halves of the theory: a locally stable static-priority network `Traj` (the
stability side — every flow's per-hop bursts are bounded by `allBound`) yields a *finite end-to-end
delay* for every flow (the performance side — the SP-PMOO end-to-end rate-latency bound). The bridge
is `concatComp_of_chain`: flow `i`'s per-hop trajectory `proc` realizes the SP-PMOO `concatComp`
chain, whose cross-traffic affine bounds come from `allBound` and whose stability `rᵢ < R^(h) − ρ^(h)`
comes from the network's local stability. -/

open DeepWiki
open scoped Classical NNReal ENNReal BigOperators

namespace DeepWiki.SpNetwork.Traj

variable {κ ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq κ]

/-- **Per-flow end-to-end delay in a stable static-priority network**: in a locally stable SP
network trajectory, every flow `i` with a nonempty path has a *finite end-to-end delay* (ingress to
egress), bounded by the SP-PMOO end-to-end rate-latency residual along its path. The cross-traffic
bounds are supplied by `allBound`; the per-hop trajectory realizes the `concatComp` chain
(`concatComp_of_chain`); and the SP-PMOO end-to-end delay (`delay_le_spPmoo_rateLatency`) closes it. -/
theorem isFlowEndToEndDelayBounded (t : Traj κ ι) (i : ι) (hne : t.net.paths i ≠ []) :
    ∃ d : ℝ≥0, Deviation.delay (⇑(t.proc i 0)) (⇑(t.proc i (t.net.paths i).length)) ≤ (d : ℝ≥0∞) := by
  classical
  obtain ⟨head, tail, hpath⟩ := List.exists_cons_of_ne_nil hne
  have hlen : 0 < (t.net.paths i).length := by rw [hpath]; simp
  -- cross-traffic bursts from allBound
  have hch : ∀ j : ι, ∃ B : κ → ℝ≥0, ∀ h, j ∈ t.net.flowsThrough h →
      IsMaximalArrivalBound (⇑(t.Ain h j)) (fun s => t.r j * s + B h) := by
    intro j; obtain ⟨B, hin, _⟩ := t.allBound j; exact ⟨B, hin⟩
  choose B hB using hch
  set α : κ → ι → ℝ≥0 → ℝ≥0 :=
    fun h j => if j ∈ t.net.flowsThrough h then (fun v => t.r j * v + B j h) else 0 with hαdef
  set ρ : κ → ℝ≥0 :=
    fun h => ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ j ∈ t.net.flowsThrough h), t.r j with hρdef
  set bc : κ → ℝ≥0 :=
    fun h => ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ j ∈ t.net.flowsThrough h), B j h with hbcdef
  -- cross-traffic aggregates to the affine `ρ h · v + bc h`
  have hcross : ∀ h, (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α h j v)
      = fun v => ρ h * v + bc h := by
    intro h; funext v
    rw [hρdef, hbcdef, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hαdef]
    by_cases hj : j < i <;> by_cases hjc : j ∈ t.net.flowsThrough h <;> simp [hj, hjc]
  have hsubF : ∀ h, Finset.univ.filter (fun j => j < i ∧ j ∈ t.net.flowsThrough h)
      ⊆ t.net.flowsThrough h := fun h j hj => (Finset.mem_filter.mp hj).2.2
  -- per-server stability: `rᵢ < R h − ρ h` for every server on flow `i`'s path
  have hkey : ∀ h ∈ t.net.paths i, t.r i < t.R h - ρ h := by
    intro h hh
    have hiFl : i ∈ t.net.flowsThrough h := Network.mem_flowsThrough.mpr hh
    rw [hρdef, lt_tsub_iff_right]
    calc t.r i + ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ j ∈ t.net.flowsThrough h), t.r j
        = ∑ j ∈ insert i (Finset.univ.filter
            (fun j => j < i ∧ j ∈ t.net.flowsThrough h)), t.r j := by rw [Finset.sum_insert (by simp)]
      _ ≤ ∑ j ∈ t.net.flowsThrough h, t.r j :=
          Finset.sum_le_sum_of_subset (Finset.insert_subset hiFl (hsubF h))
      _ < t.R h := t.hstab h
  have hRpos : 0 < pathMinRate (fun h => t.R h - ρ h) head tail := by
    apply pathMinRate_pos
    rw [← hpath]; exact fun h hh => lt_of_le_of_lt (zero_le' (a := t.r i)) (hkey h hh)
  have hr : t.r i ≤ pathMinRate (fun h => t.R h - ρ h) head tail := by
    apply le_pathMinRate
    rw [← hpath]; exact fun h hh => (hkey h hh).le
  -- the per-hop trajectory realizes the SP-PMOO `concatComp` chain
  have hp : concatComp (fun h => residualServer (fun As Ds => t.S h As Ds ∧
      ∀ j, j < i → IsMaximalArrivalBound (⇑(As j)) (α h j)) i) (head :: tail)
      (t.proc i 0) (t.proc i (head :: tail).length) := by
    rw [← hpath]
    refine concatComp_of_chain _ (t.net.paths i) (t.proc i) (fun k hk => ?_)
    rw [← hopServer_eq_get t i hk]
    refine ⟨t.Ain (t.hopServer i k), t.Dout (t.hopServer i k),
      ⟨t.hp (t.hopServer i k), ?_⟩, (proc_of_lt t i hk).symm, Dout_hopServer_eq_proc_succ t i hk⟩
    intro j hj
    simp only [hαdef]
    by_cases hjc : j ∈ t.net.flowsThrough (t.hopServer i k)
    · simp only [if_pos hjc]; exact hB j (t.hopServer i k) hjc
    · simp only [if_neg hjc]
      rw [show t.Ain (t.hopServer i k) j = 0 from t.hoff _ j hjc, isMaximalArrivalBound_iff_increment]
      intro s d; simp only [Curve.zero_apply, zero_add]; positivity
  -- flow `i`'s ingress token bucket
  have harr : IsMaximalArrivalBound (⇑(t.proc i 0)) (fun s => t.r i * s + t.b i) := by
    rw [proc_zero t i hlen]; exact t.harr0 i
  have hstabρ : ∀ h, ρ h < t.R h := fun h => by
    rw [hρdef]; exact lt_of_le_of_lt (Finset.sum_le_sum_of_subset (hsubF h)) (t.hstab h)
  rw [hpath]
  exact ⟨_, delay_le_spPmoo_rateLatency (S := t.S) (R := t.R) (T := t.T) (α := α) (i := i)
    (ρ := ρ) (bc := bc) (r := t.r i) (b := t.b i)
    t.hcaus
    (fun h => isLeftContinuous_of_continuous _ (rateLatency_continuous (t.R h) (t.T h)))
    t.hβ t.hSP hcross hstabρ hp harr hRpos hr⟩

end DeepWiki.SpNetwork.Traj
