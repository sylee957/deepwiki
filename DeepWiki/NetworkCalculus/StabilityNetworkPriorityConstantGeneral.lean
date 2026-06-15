import DeepWiki.NetworkCalculus.StabilityNetworkPriorityConstant
import DeepWiki.NetworkCalculus.StabilityNetworkTrajectory
import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.RealCurvesRates

/-! # Theorem 12.3 (static priority / FDF), general network
The fully general static-priority network stability theorem — arbitrary per-flow routing
`net.paths i : List κ`, variable per-server populations `net.flowsThrough h`, flows priority-ordered
by `<`. A locally stable static-priority network trajectory is globally stable at every server.
This is the static-priority analogue of the GPS general theorem
(`GpsNetwork.Traj.isGloballyStable`), and generalizes the shared-path tandem
(`SpTandem.isGloballyStable_sharedPath_tandem`) to arbitrary routing.

The structure mirrors the GPS general assembly but is *simpler*: instead of GPS's argmin
*peeling*, the outer induction is a plain **well-founded induction on the priority order `<`**
(`allBound`) — the strictly-higher-priority flows `j < i` are bounded first, so their per-server
bursts feed flow `i`'s per-hop SP residual along its `List` path
(`isMaximalArrivalBound_spPathOn_tokenBucket`, with the higher-priority *crossing* population
`{j<i} ∩ Fl(h)` differing per server), and flow `i` stays below its residual rate because
`∑_{j≤i, j∈Fl(h)} r ≤ ∑_{Fl(h)} r < R^(h)`. The per-flow token-bucket bounds aggregate to local
stability against each server (`Network.isGloballyStable_of_perFlow_bounds`). The list-path↔ℕ-hop
bridge (`bridge`) reuses a `Traj` path-indexing (`hopServer`/`proc`) — the static-priority analogue
of `GpsNetwork.Traj`. -/

open DeepWiki
open scoped Classical NNReal ENNReal BigOperators

namespace DeepWiki.SpNetwork

variable {κ ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq κ]

/-- A **static-priority network trajectory**: a network `net` with per-server per-flow processes
`Ain`/`Dout`, per-hop SP server relations `S h` (causal, strict rate-latency aggregate `β_{R h,T h}`,
preemptive priority), served pairs, the path wiring, token-bucket ingress, and local stability
`∑_{Fl h} rⱼ < R^(h)`. Flows are priority-ordered by `<` (`LinearOrder ι`). -/
structure Traj (κ ι : Type*) [Fintype ι] [LinearOrder ι] [DecidableEq κ] where
  /-- The underlying network. -/
  net : Network κ ι
  /-- A default server (for total ℕ-extension of finite paths). -/
  h0 : κ
  /-- Per-hop static-priority server relation. -/
  S : κ → (ι → Curve) → (ι → Curve) → Prop
  /-- Per-server rate of the strict aggregate service. -/
  R : κ → ℝ≥0
  /-- Per-server latency of the strict aggregate service. -/
  T : κ → ℝ≥0
  /-- Per-flow rate at ingress. -/
  r : ι → ℝ≥0
  /-- Per-flow burst at ingress. -/
  b : ι → ℝ≥0
  /-- Per-server per-flow input process. -/
  Ain : κ → ι → Curve
  /-- Per-server per-flow output process. -/
  Dout : κ → ι → Curve
  /-- Each server is per-flow causal. -/
  hcaus : ∀ h, IsCausalN (S h)
  /-- The network's service curve at `h` is the strict rate-latency `β_{R h, T h}`. -/
  hβ : ∀ h, IsStrictMinimalServiceCurve (rateLatency (R h) (T h)) (aggregateServer (S h))
  /-- Each server obeys the preemptive static-priority freeze. -/
  hSP : ∀ h, IsStaticPriorityServerN (S h)
  /-- Each server carries its per-flow input vector to its output vector. -/
  hp : ∀ h, S h (Ain h) (Dout h)
  /-- The network's service curve at `h` is the rate-latency `β_{R h, T h}`. -/
  hservice : ∀ h, net.service h = rateLatency (R h) (T h)
  /-- Each flow's ingress at its first server is its network arrival. -/
  hingress : ∀ i (hP : 0 < (net.paths i).length),
    Ain ((net.paths i).get ⟨0, hP⟩) i = net.arrival i
  /-- Path wiring: hop `k`'s output feeds hop `(k+1)`'s input along each flow's path. -/
  hwire : ∀ i (k : ℕ) (hk : k + 1 < (net.paths i).length),
    Ain ((net.paths i).get ⟨k + 1, hk⟩) i = Dout ((net.paths i).get ⟨k, Nat.lt_of_succ_lt hk⟩) i
  /-- A flow not crossing server `h` contributes no input there. -/
  hoff : ∀ h i, i ∉ net.flowsThrough h → Ain h i = 0
  /-- Each flow is token-bucket `γ_{r i, b i}` at ingress. -/
  harr0 : ∀ i, IsMaximalArrivalBound (⇑(net.arrival i)) (fun t => r i * t + b i)
  /-- Local stability at every server: the crossing flows' rate sum is below the service rate. -/
  hstab : ∀ h, ∑ j ∈ net.flowsThrough h, r j < R h

namespace Traj

variable (t : Traj κ ι)

/-- A flow not crossing `h` has zero departure there (off-path input is `0`, causal output ≤ it). -/
theorem Dout_off (h : κ) (i : ι) (hi : i ∉ t.net.flowsThrough h) : t.Dout h i = 0 := by
  have hle : t.Dout h i ≤ t.Ain h i := t.hcaus h _ _ (t.hp h) i
  rw [t.hoff h i hi] at hle
  ext s
  have : (t.Dout h i) s ≤ (0 : Curve) s := hle s
  rw [Curve.zero_apply] at this
  simpa using le_antisymm this (zero_le' (a := (t.Dout h i) s))

/-- The server at hop `k` of flow `i`'s path (junk default `h0` past the path's end). -/
def hopServer (i : ι) (k : ℕ) : κ := (t.net.paths i).getD k t.h0

/-- For `k` within the path, the hop server is the indexed path element. -/
theorem hopServer_eq_get (i : ι) {k : ℕ} (hk : k < (t.net.paths i).length) :
    t.hopServer i k = (t.net.paths i).get ⟨k, hk⟩ := by
  rw [hopServer, List.get_eq_getElem, List.getElem_eq_getD]

/-- For `k` within the path, flow `i` crosses its hop server. -/
theorem mem_flowsThrough_hopServer (i : ι) {k : ℕ} (hk : k < (t.net.paths i).length) :
    i ∈ t.net.flowsThrough (t.hopServer i k) := by
  rw [Network.mem_flowsThrough, hopServer_eq_get t i hk, List.get_eq_getElem]
  exact List.getElem_mem hk

/-- Flow `i`'s process entering hop `k`: its input at the `k`-th server while within the path,
the egress (last server's output) once `k` reaches the path length. -/
noncomputable def proc (i : ι) (k : ℕ) : Curve :=
  if k < (t.net.paths i).length then t.Ain (t.hopServer i k) i
  else t.Dout (t.hopServer i ((t.net.paths i).length - 1)) i

/-- Within the path, `proc i k` is flow `i`'s input at the `k`-th server. -/
theorem proc_of_lt (i : ι) {k : ℕ} (hk : k < (t.net.paths i).length) :
    t.proc i k = t.Ain (t.hopServer i k) i := by rw [proc, if_pos hk]

/-- The proc at hop `0` is flow `i`'s network arrival (for a nonempty path). -/
theorem proc_zero (i : ι) (hP : 0 < (t.net.paths i).length) :
    t.proc i 0 = t.net.arrival i := by
  rw [proc_of_lt t i hP, hopServer_eq_get t i hP]; exact t.hingress i hP

/-- Wiring at the proc level: hop `k`'s output equals hop `(k+1)`'s proc, for `k < length`. -/
theorem Dout_hopServer_eq_proc_succ (i : ι) {k : ℕ} (hk : k < (t.net.paths i).length) :
    t.Dout (t.hopServer i k) i = t.proc i (k + 1) := by
  rcases Nat.lt_or_ge (k + 1) (t.net.paths i).length with hk1 | hk1
  · rw [proc_of_lt t i hk1, hopServer_eq_get t i hk1, hopServer_eq_get t i hk]
    exact (t.hwire i k hk1).symm
  · have hkeq : k + 1 = (t.net.paths i).length := Nat.le_antisymm hk hk1
    rw [proc, if_neg (by omega)]; congr 2; omega

/-- **Per-flow stability bound**: flow `j` has a per-server token-bucket arrival bound of its own
rate `r j` on both its input and its departure at every server it crosses. -/
def PerFlowBound (t : Traj κ ι) (j : ι) : Prop :=
  ∃ B : κ → ℝ≥0,
    (∀ h, j ∈ t.net.flowsThrough h →
      IsMaximalArrivalBound (⇑(t.Ain h j)) (fun s => t.r j * s + B h)) ∧
    (∀ h, j ∈ t.net.flowsThrough h →
      IsMaximalArrivalBound (⇑(t.Dout h j)) (fun s => t.r j * s + B h))

/-- **The per-flow bridge** (priority order): if all strictly-higher-priority flows `j < i` are
`PerFlowBound`, so is flow `i`. Their per-server bursts feed flow `i`'s per-hop SP residual
(`isMaximalArrivalBound_spPathOn_tokenBucket`); flow `i` stays below its residual rate because at
every crossed server `∑_{j≤i, j∈Fl h} r ≤ ∑ⱼ r < R^(h)`. -/
theorem bridge (t : Traj κ ι) (i : ι) (hHP : ∀ j, j < i → PerFlowBound t j) :
    PerFlowBound t i := by
  classical
  set P := t.net.paths i with hPdef
  set n := P.length with hndef
  -- choose each higher-priority flow's per-server input-burst function
  have hch : ∀ j : ι, ∃ Bj : κ → ℝ≥0, j < i → ∀ h, j ∈ t.net.flowsThrough h →
      IsMaximalArrivalBound (⇑(t.Ain h j)) (fun s => t.r j * s + Bj h) := by
    intro j
    by_cases hj : j < i
    · obtain ⟨Bj, hBin, _⟩ := hHP j hj; exact ⟨Bj, fun _ => hBin⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose Bhp hBhp using hch
  -- per-hop higher-priority rates / bursts (0 for a higher-priority flow not crossing the hop)
  set rHP : ℕ → ι → ℝ≥0 := fun k j =>
    if j ∈ t.net.flowsThrough (t.hopServer i k) then t.r j else 0 with hrHP
  set bHP : ℕ → ι → ℝ≥0 := fun k j =>
    if j ∈ t.net.flowsThrough (t.hopServer i k) then Bhp j (t.hopServer i k) else 0 with hbHP
  -- the per-hop higher-priority rate sum is the crossing-higher-priority rate, `< R`
  have hsumrHP : ∀ k, (∑ j ∈ Finset.univ.filter (fun j => j < i), rHP k j)
      = ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ j ∈ t.net.flowsThrough (t.hopServer i k)),
          t.r j := by
    intro k
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hrHP]
    by_cases hj : j < i <;> by_cases hjc : j ∈ t.net.flowsThrough (t.hopServer i k) <;>
      simp [hj, hjc]
  have hsub : ∀ k, Finset.univ.filter (fun j => j < i ∧ j ∈ t.net.flowsThrough (t.hopServer i k))
      ⊆ t.net.flowsThrough (t.hopServer i k) := fun k j hj => (Finset.mem_filter.mp hj).2.2
  have hρ : ∀ k, (∑ j ∈ Finset.univ.filter (fun j => j < i), rHP k j) < t.R (t.hopServer i k) := by
    intro k
    rw [hsumrHP k]
    exact lt_of_le_of_lt (Finset.sum_le_sum_of_subset (hsub k)) (t.hstab (t.hopServer i k))
  -- flow `i`'s rate is below the per-hop residual rate `R − ∑_{j<i} rHP`
  have hr : ∀ k, k < n → t.r i
      ≤ t.R (t.hopServer i k) - ∑ j ∈ Finset.univ.filter (fun j => j < i), rHP k j := by
    intro k hk
    have hiFl : i ∈ t.net.flowsThrough (t.hopServer i k) := t.mem_flowsThrough_hopServer i hk
    rw [hsumrHP k, le_tsub_iff_right (le_of_lt (lt_of_le_of_lt
      (Finset.sum_le_sum_of_subset (hsub k)) (t.hstab _)))]
    calc t.r i + ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ j ∈ t.net.flowsThrough (t.hopServer i k)), t.r j
        = ∑ j ∈ insert i (Finset.univ.filter
            (fun j => j < i ∧ j ∈ t.net.flowsThrough (t.hopServer i k))), t.r j := by
          rw [Finset.sum_insert (by simp)]
      _ ≤ ∑ j ∈ t.net.flowsThrough (t.hopServer i k), t.r j :=
          Finset.sum_le_sum_of_subset (Finset.insert_subset hiFl (hsub k))
      _ ≤ t.R (t.hopServer i k) := le_of_lt (t.hstab _)
  -- the per-flow arrival bound along the path
  have hmab := isMaximalArrivalBound_spPathOn_tokenBucket
    (ι := ι) (n := n) (Sf := fun k => t.S (t.hopServer i k)) (i := i) (r := t.r i) (b := t.b i)
    (R := fun k => t.R (t.hopServer i k)) (T := fun k => t.T (t.hopServer i k))
    (rHP := rHP) (bHP := bHP)
    (fun k => t.hcaus _) (fun k => t.hβ _) (fun k => t.hSP _) hρ (t.proc i) ?_ ?_ hr
  · -- assemble PerFlowBound from the per-hop bound
    set Bk : ℕ → ℝ≥0 := fun k => t.b i + t.r i * ∑ j ∈ Finset.range k,
      (t.R (t.hopServer i j) * t.T (t.hopServer i j)
        + ∑ l ∈ Finset.univ.filter (fun l => l < i), bHP j l)
        / (t.R (t.hopServer i j) - ∑ l ∈ Finset.univ.filter (fun l => l < i), rHP j l) with hBkdef
    have hBkmono : Monotone Bk := by
      intro a c hac
      simp only [hBkdef]
      exact add_le_add le_rfl (mul_le_mul_right
        (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hac)) _)
    have hmab' : ∀ k, k ≤ n → IsMaximalArrivalBound (⇑(t.proc i k)) (fun s => t.r i * s + Bk k) := by
      intro k hk; have := hmab k hk; simpa only [hBkdef] using this
    have hcross : ∀ h, i ∈ t.net.flowsThrough h → ∃ k, k < n ∧ t.hopServer i k = h := by
      intro h hh
      have hmem : h ∈ P := by rw [hPdef]; rwa [Network.mem_flowsThrough] at hh
      refine ⟨P.idxOf h, ?_, ?_⟩
      · rw [hndef]; exact List.idxOf_lt_length_of_mem hmem
      · rw [t.hopServer_eq_get i (k := P.idxOf h)
            (by rw [← hPdef]; exact List.idxOf_lt_length_of_mem hmem), List.get_eq_getElem]
        exact List.getElem_idxOf (by rw [← hPdef]; exact List.idxOf_lt_length_of_mem hmem)
    refine ⟨fun h => if hh : i ∈ t.net.flowsThrough h then Bk ((hcross h hh).choose + 1) else 0,
      ?_, ?_⟩
    · intro h hh
      simp only [dif_pos hh]
      set k := (hcross h hh).choose with hkdef
      have hk : k < n := (hcross h hh).choose_spec.1
      have hkeq : t.hopServer i k = h := (hcross h hh).choose_spec.2
      have hAinEq : t.Ain h i = t.proc i k := by rw [t.proc_of_lt i (by rw [← hndef]; exact hk), hkeq]
      rw [hAinEq]
      exact (hmab' k (le_of_lt hk)).mono (fun s => add_le_add le_rfl (hBkmono (Nat.le_succ k)))
    · intro h hh
      simp only [dif_pos hh]
      set k := (hcross h hh).choose with hkdef
      have hk : k < n := (hcross h hh).choose_spec.1
      have hkeq : t.hopServer i k = h := (hcross h hh).choose_spec.2
      have hDoutEq : t.Dout h i = t.proc i (k + 1) := by
        rw [← hkeq]; exact t.Dout_hopServer_eq_proc_succ i (by rw [← hndef]; exact hk)
      rw [hDoutEq]; exact hmab' (k + 1) (by omega)
  · -- hchain: the SP-restricted served pair at hop k
    intro k hk
    refine ⟨t.Ain (t.hopServer i k), t.Dout (t.hopServer i k), ⟨t.hp (t.hopServer i k), ?_⟩, ?_, ?_⟩
    · -- the higher-priority flows are bounded at this hop
      intro j hj
      simp only [hrHP, hbHP]
      by_cases hjc : j ∈ t.net.flowsThrough (t.hopServer i k)
      · simp only [if_pos hjc]; exact hBhp j hj (t.hopServer i k) hjc
      · simp only [if_neg hjc]
        rw [show t.Ain (t.hopServer i k) j = 0 from t.hoff _ j hjc, isMaximalArrivalBound_iff_increment]
        intro s d; simp only [Curve.zero_apply, zero_add]; positivity
    · rw [t.proc_of_lt i hk]
    · exact t.Dout_hopServer_eq_proc_succ i hk
  · -- harr0 : the proc at hop 0 is token-bucket bounded
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · have hnotmem : i ∉ t.net.flowsThrough (t.hopServer i 0) := by
        intro hmem
        rw [Network.mem_flowsThrough] at hmem
        have : 0 < P.length := List.length_pos_of_mem hmem
        omega
      have hp0 : t.proc i 0 = 0 := by
        rw [Traj.proc, if_neg (by rw [← hPdef, ← hndef]; omega)]
        rw [show (t.net.paths i).length - 1 = 0 from by rw [← hPdef, ← hndef, hn0]]
        exact t.Dout_off _ i hnotmem
      rw [hp0, isMaximalArrivalBound_iff_increment]
      intro s d; simp only [Curve.zero_apply, zero_add]; positivity
    · rw [t.proc_zero i hnpos]; exact t.harr0 i

/-- Every flow is `PerFlowBound`: well-founded induction on the priority order `<`. -/
theorem allBound (t : Traj κ ι) (i : ι) : PerFlowBound t i :=
  WellFoundedLT.induction i (fun i ih => t.bridge i ih)

/-- **Theorem 12.3, fully general** (arbitrary per-flow routing, variable per-server populations):
a locally stable static-priority network trajectory is globally stable at every server. -/
theorem isGloballyStable (t : Traj κ ι) :
    ∀ h : κ, IsGloballyStableServer ⇑(∑ i, t.Ain h i) ⇑(∑ i, t.Dout h i) := by
  classical
  have hAll : ∀ i, PerFlowBound t i := t.allBound
  choose Bfun hBin _ using hAll
  set σ : κ → ι → ℝ≥0 → ℝ≥0 :=
    fun h i => if i ∈ t.net.flowsThrough h then (fun s => t.r i * s + Bfun i h) else 0 with hσdef
  have hbound : ∀ h i, IsMaximalArrivalBound (⇑(t.Ain h i)) (σ h i) := by
    intro h i
    by_cases hih : i ∈ t.net.flowsThrough h
    · simp only [hσdef, if_pos hih]; exact hBin i h hih
    · simp only [hσdef, if_neg hih]
      rw [show t.Ain h i = 0 from t.hoff h i hih, isMaximalArrivalBound_iff_increment]
      intro s d; simp only [Curve.zero_apply, Pi.zero_apply, add_zero, le_refl]
  have hrate : ∀ h i, longTermArrivalRate (σ h i)
      = (if i ∈ t.net.flowsThrough h then (t.r i : ℝ≥0∞) else 0) := by
    intro h i
    by_cases hih : i ∈ t.net.flowsThrough h
    · simp only [hσdef, if_pos hih, longTermArrivalRate_affine]
    · simp only [hσdef, if_neg hih, longTermArrivalRate_zero]
  have hagg : ∀ h, IsLocallyStableServer (fun s => ∑ i, σ h i s) (t.net.service h) := by
    intro h
    show longTermArrivalRate (fun s => ∑ i, σ h i s) < longTermServiceRate (t.net.service h)
    calc longTermArrivalRate (fun s => ∑ i, σ h i s)
        ≤ ∑ i, longTermArrivalRate (σ h i) := longTermArrivalRate_sum_le Finset.univ _
      _ = ∑ i, (if i ∈ t.net.flowsThrough h then (t.r i : ℝ≥0∞) else 0) :=
          Finset.sum_congr rfl fun i _ => hrate h i
      _ = ∑ i ∈ t.net.flowsThrough h, (t.r i : ℝ≥0∞) := by rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ((∑ i ∈ t.net.flowsThrough h, t.r i : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
      _ < (t.R h : ℝ≥0∞) := by exact_mod_cast t.hstab h
      _ = longTermServiceRate (t.net.service h) := by
          rw [t.hservice h, longTermServiceRate_rateLatency]
  exact t.net.isGloballyStable_of_perFlow_bounds t.S t.Ain t.Dout σ
    t.hcaus (fun h => by rw [t.hservice h]; exact t.hβ h) t.hp hbound hagg

end Traj

end DeepWiki.SpNetwork
