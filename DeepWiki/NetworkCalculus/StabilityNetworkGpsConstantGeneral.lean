import DeepWiki.NetworkCalculus.StabilityNetworkGpsConstant
import DeepWiki.NetworkCalculus.StabilityNetworkTrajectory
import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.DeviationsBoundsServerRateLatency

/-! # Theorem 12.5 (GPS constant rates: local ⟹ global stability), general network
The fully general cyclic-peeling assembly: an arbitrary GPS-constant network with per-flow
routing `net.paths i : List κ` and variable per-server populations `net.flowsThrough h`,
locally stable (`∑_{Fl h} rⱼ < R^(h)`), is globally stable at every server. This generalizes
the shared-path tandem (`GpsTandem.isGloballyStable_sharedPath_tandem`) to arbitrary routing.

The crux over the per-flow engine (`StabilityNetworkGpsConstant`) is the **list-path ↔ ℕ-hop
bridge**: for a flow `i` with path `P = net.paths i`, index the path with `List.getD` to feed
the ℕ-hop engine body `isMaximalArrivalBound_gpsPeelPath_tokenBucket`. This file
- adds a trajectory model (`Traj`) on top of `Network`: per-server per-flow processes
  `Ain`/`Dout`, GPS served pairs, path wiring along `net.paths`;
- proves the per-flow bridge lemma (`Traj.bridge`): a flow below its residual GPS share
  along its path, whose already-peeled crossing flows are token-bucket bounded at each
  crossed server, has a per-server token-bucket arrival bound of its own rate;
- runs the outer peeling induction (`Traj.peelInduction`, peeling the `rⱼ/φⱼ`-minimizer) and
  assembles the general theorem (`Traj.isGloballyStable`) via
  `Network.isGloballyStable_of_perFlow_bounds`.
Helpers live in the `GpsNetwork` sub-namespace (their short names — `bridge`, `peelStep`,
`hopServer` — would clash in `DeepWiki`). -/

open scoped Classical NNReal ENNReal BigOperators

namespace DeepWiki.GpsNetwork

variable {κ ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- A **GPS-constant network trajectory**: a network `net` together with per-server
per-flow input/output processes `Ain Dout`, a per-hop GPS server relation `S h`
(per-flow causal, aggregate offering the strict rate-latency `β_{R h, T h}` with
shared weights `φ`), the served pairs `S h (Ain h) (Dout h)`, the path wiring
(ingress = `net.arrival`, hop-to-hop chaining along each `net.paths i`, off-path
flows contribute `0`), and a default server `h0` (junk for the ℕ-extension past a
path's end).  The network's service curve at `h` is the strict rate-latency
`β_{R h, T h}` (so its service rate is `R h`). -/
structure Traj (κ ι : Type*) [Fintype ι] [DecidableEq κ] where
  /-- The underlying network. -/
  net : Network κ ι
  /-- A default server (for total ℕ-extension of finite paths). -/
  h0 : κ
  /-- Per-hop GPS server relation. -/
  S : κ → (ι → Curve) → (ι → Curve) → Prop
  /-- GPS weights, positive. -/
  φ : ι → ℝ≥0
  /-- Positivity of the weights. -/
  hφ : ∀ j, 0 < φ j
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
  /-- Each server respects the GPS proportional shares. -/
  hgps : ∀ h, IsGpsServerN φ (S h)
  /-- Each server carries its per-flow input vector to its output vector. -/
  hp : ∀ h, S h (Ain h) (Dout h)
  /-- The network's service curve at `h` is the rate-latency `β_{R h, T h}`. -/
  hservice : ∀ h, net.service h = rateLatency (R h) (T h)
  /-- Each flow's ingress at its first server is its network arrival. -/
  hingress : ∀ i (hP : 0 < (net.paths i).length),
    Ain ((net.paths i).get ⟨0, hP⟩) i = net.arrival i
  /-- Path wiring: hop `k`'s output feeds hop `(k+1)`'s input along each flow's path. -/
  hwire : ∀ i (k : ℕ) (hk : k + 1 < (net.paths i).length),
    Ain ((net.paths i).get ⟨k + 1, hk⟩) i
      = Dout ((net.paths i).get ⟨k, Nat.lt_of_succ_lt hk⟩) i
  /-- A flow not crossing server `h` contributes no input there. -/
  hoff : ∀ h i, i ∉ net.flowsThrough h → Ain h i = 0
  /-- Each flow is token-bucket `γ_{r i, b i}` at ingress. -/
  harr0 : ∀ i, IsMaximalArrivalBound (⇑(net.arrival i)) (fun t => r i * t + b i)
  /-- Aggregate local stability at every server. -/
  hstab : ∀ h, ∑ j ∈ net.flowsThrough h, r j < R h

namespace Traj

variable (t : Traj κ ι)

omit [DecidableEq ι] in
/-- Every server has positive rate: `0 ≤ ∑_{Fl h} r < R h`. -/
theorem R_pos (h : κ) : 0 < t.R h :=
  lt_of_le_of_lt zero_le' (t.hstab h)

omit [DecidableEq ι] in
/-- A flow not crossing `h` has zero departure there (off-path input is `0`, causal
output `Dout ≤ Ain = 0`). -/
theorem Dout_off (h : κ) (i : ι) (hi : i ∉ t.net.flowsThrough h) : t.Dout h i = 0 := by
  have hle : t.Dout h i ≤ t.Ain h i := t.hcaus h _ _ (t.hp h) i
  rw [t.hoff h i hi] at hle
  ext s
  have : (t.Dout h i) s ≤ (0 : Curve) s := hle s
  rw [Curve.zero_apply] at this
  simpa using le_antisymm this (zero_le' (a := (t.Dout h i) s))

/-- The server at hop `k` of flow `i`'s path (junk default `h0` past the path's end). -/
def hopServer (i : ι) (k : ℕ) : κ := (t.net.paths i).getD k t.h0

omit [DecidableEq ι] in
/-- For `k` within the path, the hop server is the indexed path element. -/
theorem hopServer_eq_get (i : ι) {k : ℕ} (hk : k < (t.net.paths i).length) :
    t.hopServer i k = (t.net.paths i).get ⟨k, hk⟩ := by
  rw [hopServer, List.get_eq_getElem, List.getElem_eq_getD]

omit [DecidableEq ι] in
/-- For `k` within the path, flow `i` crosses its hop server. -/
theorem mem_flowsThrough_hopServer (i : ι) {k : ℕ} (hk : k < (t.net.paths i).length) :
    i ∈ t.net.flowsThrough (t.hopServer i k) := by
  rw [Network.mem_flowsThrough, hopServer_eq_get t i hk, List.get_eq_getElem]
  exact List.getElem_mem hk

/-- Flow `i`'s process entering hop `k`: its input at the `k`-th server on its path
while `k` is within the path, and the egress (last server's output) once `k` reaches
the path length — so the engine's `proc (k+1)` at the last hop is the actual departure. -/
noncomputable def proc (i : ι) (k : ℕ) : Curve :=
  if k < (t.net.paths i).length then t.Ain (t.hopServer i k) i
  else t.Dout (t.hopServer i ((t.net.paths i).length - 1)) i

omit [DecidableEq ι] in
/-- Within the path, `proc i k` is flow `i`'s input at the `k`-th server. -/
theorem proc_of_lt (i : ι) {k : ℕ} (hk : k < (t.net.paths i).length) :
    t.proc i k = t.Ain (t.hopServer i k) i := by
  rw [proc, if_pos hk]

omit [DecidableEq ι] in
/-- The proc at hop `0` is flow `i`'s network arrival (for a nonempty path). -/
theorem proc_zero (i : ι) (hP : 0 < (t.net.paths i).length) :
    t.proc i 0 = t.net.arrival i := by
  rw [proc_of_lt t i hP, hopServer_eq_get t i hP]
  exact t.hingress i hP

omit [DecidableEq ι] in
/-- Wiring at the proc level: hop `k`'s output equals hop `(k+1)`'s proc, for `k < length`
(both the interior wiring `k+1 < length` and the last hop `k+1 = length`, where the next
proc is the egress). -/
theorem Dout_hopServer_eq_proc_succ (i : ι) {k : ℕ} (hk : k < (t.net.paths i).length) :
    t.Dout (t.hopServer i k) i = t.proc i (k + 1) := by
  rcases Nat.lt_or_ge (k + 1) (t.net.paths i).length with hk1 | hk1
  · -- interior: proc (k+1) = Ain (hopServer i (k+1)) i = Dout (hopServer i k) i (wire)
    rw [proc_of_lt t i hk1, hopServer_eq_get t i hk1, hopServer_eq_get t i hk]
    exact (t.hwire i k hk1).symm
  · -- last hop: k+1 = length, proc (k+1) = Dout (hopServer i (length-1)) i
    have hkeq : k + 1 = (t.net.paths i).length := Nat.le_antisymm hk hk1
    rw [proc, if_neg (by omega)]
    congr 2
    omega

/-! ## The per-flow LIST-PATH ↔ ℕ-HOP bridge -/

/-- The active population at flow `i`'s hop `k`: the active flows crossing that hop,
with `i` forced in (so `i ∈ J` holds at every ℕ-index, including past the path). -/
def hopActive (i : ι) (act : Finset ι) (k : ℕ) : Finset ι :=
  insert i (act ∩ t.net.flowsThrough (t.hopServer i k))

/-- The peeled rate at flow `i`'s hop `k`: the summed rate of the flows crossing that
hop but not in its active population — i.e. the already-peeled crossing flows. -/
noncomputable def hopPeeledRate (i : ι) (act : Finset ι) (k : ℕ) : ℝ≥0 :=
  ∑ j ∈ (t.hopActive i act k)ᶜ ∩ t.net.flowsThrough (t.hopServer i k), t.r j

/-- **The per-flow bridge lemma** (the crux). For a flow `i` in the active set `act`,
below its residual GPS share `r i < φᵢ·(Rₕ − ∑_{Fl h \ act} r)/∑_{Fl h ∩ act} φ` at every
server it crosses, and whose already-peeled crossing flows `Fl h ∩ actᶜ` have a
token-bucket aggregate departure bound at every crossed server, flow `i` has a per-server
token-bucket arrival bound `σᵢ h` of its own rate `r i` at every server it crosses. The
ℕ-hop engine body `isMaximalArrivalBound_gpsPeelPath_tokenBucket` is applied by indexing
`i`'s path with `hopServer`/`getD`. -/
theorem bridge (t : Traj κ ι) (i : ι) (act : Finset ι) (hiact : i ∈ act)
    (hshare : ∀ h, i ∈ t.net.flowsThrough h ∩ act →
      t.r i < t.φ i * (t.R h - ∑ j ∈ t.net.flowsThrough h \ act, t.r j)
        / (∑ j ∈ t.net.flowsThrough h ∩ act, t.φ j))
    (hpeeled : ∀ h, i ∈ t.net.flowsThrough h → ∃ bb : ℝ≥0,
      IsMaximalArrivalBound
        (fun x => ∑ j ∈ (t.net.flowsThrough h ∩ actᶜ), (t.Dout h j) x)
        (fun v => (∑ j ∈ t.net.flowsThrough h ∩ actᶜ, t.r j) * v + bb)) :
    ∃ B : κ → ℝ≥0,
      (∀ h, i ∈ t.net.flowsThrough h →
        IsMaximalArrivalBound (⇑(t.Ain h i)) (fun s => t.r i * s + B h)) ∧
      (∀ h, i ∈ t.net.flowsThrough h →
        IsMaximalArrivalBound (⇑(t.Dout h i)) (fun s => t.r i * s + B h)) := by
  classical
  set P := t.net.paths i with hPdef
  set n := P.length with hndef
  -- the ℕ-indexed engine data
  set Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop := fun k => t.S (t.hopServer i k) with hSfdef
  set Rk : ℕ → ℝ≥0 := fun k => t.R (t.hopServer i k) with hRkdef
  set Tk : ℕ → ℝ≥0 := fun k => t.T (t.hopServer i k) with hTkdef
  set J : ℕ → Finset ι := fun k => t.hopActive i act k with hJdef
  set ρ : ℕ → ℝ≥0 := fun k => t.hopPeeledRate i act k with hρdef
  -- `i ∈ J k` for all k
  have hiJ : ∀ k, i ∈ J k := fun k => by
    rw [hJdef]; exact Finset.mem_insert_self _ _
  -- `ρ k < Rk k` for all k
  have hρR : ∀ k, ρ k < Rk k := by
    intro k
    simp only [hρdef, hRkdef, hopPeeledRate]
    refine lt_of_le_of_lt ?_ (t.hstab (t.hopServer i k))
    exact Finset.sum_le_sum_of_subset Finset.inter_subset_right
  -- choose per-hop bursts for the peeled aggregate departures
  have hbbch : ∀ k, ∃ bb : ℝ≥0, k < n →
      IsMaximalArrivalBound
        (fun x => ∑ j ∈ (J k)ᶜ, (t.Dout (t.hopServer i k) j) x)
        (fun v => ρ k * v + bb) := by
    intro k
    by_cases hk : k < n
    · -- i crosses hopServer i k, so the server-wise peeled bound applies
      set h := t.hopServer i k with hhdef
      have hmemFl : i ∈ t.net.flowsThrough h := t.mem_flowsThrough_hopServer i hk
      have hJk : J k = act ∩ t.net.flowsThrough h := by
        rw [hJdef]
        simp only [Traj.hopActive, ← hhdef]
        exact Finset.insert_eq_self.mpr (Finset.mem_inter.mpr ⟨hiact, hmemFl⟩)
      -- the peeled-on-this-server set: Fl h ∩ actᶜ
      have hset : (J k)ᶜ ∩ t.net.flowsThrough h = t.net.flowsThrough h ∩ actᶜ := by
        rw [hJk]
        ext x
        simp only [Finset.mem_inter, Finset.mem_compl, not_and]
        constructor
        · rintro ⟨hc, hF⟩; exact ⟨hF, fun ha => hc ha hF⟩
        · rintro ⟨hF, hna⟩; exact ⟨fun ha _ => hna ha, hF⟩
      -- ρ k = ∑_{Fl h ∩ actᶜ} r
      have hρk : ρ k = ∑ j ∈ t.net.flowsThrough h ∩ actᶜ, t.r j := by
        have : ρ k = ∑ j ∈ (J k)ᶜ ∩ t.net.flowsThrough h, t.r j := by
          simp only [hρdef, Traj.hopPeeledRate, ← hhdef, hJdef]
        rw [this, hset]
      obtain ⟨bb, hbb⟩ := hpeeled h hmemFl
      refine ⟨bb, fun _ => ?_⟩
      -- drop off-path (zero-departure) flows, reduce to the Fl h ∩ actᶜ sum
      have hsumeq : (fun x => ∑ j ∈ (J k)ᶜ, (t.Dout h j) x)
          = (fun x => ∑ j ∈ t.net.flowsThrough h ∩ actᶜ, (t.Dout h j) x) := by
        funext x
        rw [← hset]
        refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
        intro j hjc hjni
        -- j ∈ (J k)ᶜ but j ∉ (J k)ᶜ ∩ Fl h ⟹ j ∉ Fl h ⟹ Dout = 0
        have hjnotF : j ∉ t.net.flowsThrough h := by
          intro hjF; exact hjni (Finset.mem_inter.mpr ⟨hjc, hjF⟩)
        rw [t.Dout_off h j hjnotF]; rfl
      rw [hsumeq, hρk]
      exact hbb
    · exact ⟨0, fun hk' => absurd hk' hk⟩
  choose bb hbb using hbbch
  -- the engine body, in arrival-bound form
  have hmab := isMaximalArrivalBound_gpsPeelPath_tokenBucket
    (ι := ι) (n := n) (Sf := Sf) (φ := t.φ) (i := i) (r := t.r i) (b := t.b i)
    (R := Rk) (T := Tk) (ρ := ρ) (bb := bb) (J := J)
    hiJ hρR (fun k => t.hcaus _) (fun k => t.hβ _) (fun k => t.hgps _)
    (t.proc i) ?_ ?_ ?_
  · -- assemble σi
    -- the engine's per-hop burst at hop `k`
    set Bk : ℕ → ℝ≥0 :=
      fun k => t.b i + t.r i * ∑ j ∈ Finset.range k, (Rk j * Tk j + bb j) / (Rk j - ρ j)
      with hBkdef
    -- Bk is nondecreasing (the sum grows with the prefix length)
    have hBkmono : Monotone Bk := by
      intro a c hac
      simp only [hBkdef]
      refine add_le_add le_rfl (mul_le_mul_right ?_ _)
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hac)
    -- the engine bound at hop k (k ≤ n): proc i k bounded by token bucket of burst Bk k
    have hmab' : ∀ k, k ≤ n →
        IsMaximalArrivalBound (⇑(t.proc i k)) (fun s => t.r i * s + Bk k) := by
      intro k hk
      have := hmab k hk
      simpa only [hBkdef] using this
    -- for a crossed server h, the path index k := idxOf h has hopServer i k = h
    have hcross : ∀ h, i ∈ t.net.flowsThrough h →
        ∃ k, k < n ∧ t.hopServer i k = h := by
      intro h hh
      have hmem : h ∈ P := by rw [hPdef]; rwa [Network.mem_flowsThrough] at hh
      refine ⟨P.idxOf h, ?_, ?_⟩
      · rw [hndef]; exact List.idxOf_lt_length_of_mem hmem
      · rw [t.hopServer_eq_get i (k := P.idxOf h)
            (by rw [← hPdef]; exact List.idxOf_lt_length_of_mem hmem), List.get_eq_getElem]
        exact List.getElem_idxOf (by rw [← hPdef]; exact List.idxOf_lt_length_of_mem hmem)
    -- B h: burst `Bk (k+1)` at h's path index (else 0),
    -- which dominates both the input (`Bk k`) and the departure (`Bk (k+1)`) bursts
    refine ⟨fun h => if hh : i ∈ t.net.flowsThrough h then Bk ((hcross h hh).choose + 1) else 0,
      ?_, ?_⟩
    · -- input bound
      intro h hh
      simp only [dif_pos hh]
      set k := (hcross h hh).choose with hkdef
      have hk : k < n := (hcross h hh).choose_spec.1
      have hkeq : t.hopServer i k = h := (hcross h hh).choose_spec.2
      have hAinEq : t.Ain h i = t.proc i k := by
        rw [t.proc_of_lt i (by rw [← hndef]; exact hk), hkeq]
      rw [hAinEq]
      exact (hmab' k (le_of_lt hk)).mono (fun s => add_le_add le_rfl (hBkmono (Nat.le_succ k)))
    · -- departure bound: Dout h i = proc i (k+1), bounded by Bk (k+1)
      intro h hh
      simp only [dif_pos hh]
      set k := (hcross h hh).choose with hkdef
      have hk : k < n := (hcross h hh).choose_spec.1
      have hkeq : t.hopServer i k = h := (hcross h hh).choose_spec.2
      have hDoutEq : t.Dout h i = t.proc i (k + 1) := by
        rw [← hkeq]
        exact t.Dout_hopServer_eq_proc_succ i (by rw [← hndef]; exact hk)
      rw [hDoutEq]
      exact hmab' (k + 1) (by omega)
  · -- hchain : ∀ k < n, residualServer (Sf k ∧ peeled-bound) i (proc i k) (proc i (k+1))
    intro k hk
    -- exhibit the full per-server vectors at hop k
    refine ⟨t.Ain (t.hopServer i k), t.Dout (t.hopServer i k),
      ⟨t.hp (t.hopServer i k), ?_⟩, ?_, ?_⟩
    · -- peeled-departure bound is exactly `hbb k hk`
      exact hbb k hk
    · -- As i = proc i k
      rw [t.proc_of_lt i hk]
    · -- Ds i = proc i (k+1)
      exact t.Dout_hopServer_eq_proc_succ i hk
  · -- harr0 : IsMaximalArrivalBound (proc i 0) (fun s => r i * s + b i)
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- empty path: proc i 0 = Dout (hopServer i 0) i = 0 (i crosses no server)
      have hnotmem : i ∉ t.net.flowsThrough (t.hopServer i 0) := by
        intro hmem
        rw [Network.mem_flowsThrough] at hmem
        have : 0 < P.length := List.length_pos_of_mem hmem
        omega
      have hlen0 : (t.net.paths i).length = 0 := by rw [← hPdef, ← hndef]; exact hn0
      have hp0 : t.proc i 0 = 0 := by
        rw [Traj.proc, if_neg (by rw [hlen0]; omega)]
        rw [show (t.net.paths i).length - 1 = 0 from by rw [hlen0]]
        exact t.Dout_off _ i hnotmem
      rw [hp0, isMaximalArrivalBound_iff_increment]
      intro s d; simp only [Curve.zero_apply, zero_add]; positivity
    · rw [t.proc_zero i hnpos]
      exact t.harr0 i
  · -- hr : ∀ k < n, r i ≤ (φ i / ∑ j ∈ J k, φ j) * (Rk k - ρ k)
    intro k hk
    -- at hop `k < n`, server `h := hopServer i k`, and `i ∈ Fl h`
    set h := t.hopServer i k with hhdef
    have hmemFl : i ∈ t.net.flowsThrough h := t.mem_flowsThrough_hopServer i hk
    -- J k = act ∩ Fl  (since i ∈ act ∩ Fl)
    have hJk : J k = act ∩ t.net.flowsThrough h := by
      rw [hJdef]
      simp only [Traj.hopActive, ← hhdef]
      exact Finset.insert_eq_self.mpr (Finset.mem_inter.mpr ⟨hiact, hmemFl⟩)
    -- ρ k = ∑_{Fl \ act} r
    have hρk : ρ k = ∑ j ∈ t.net.flowsThrough h \ act, t.r j := by
      have : ρ k = ∑ j ∈ (J k)ᶜ ∩ t.net.flowsThrough h, t.r j := by
        simp only [hρdef, Traj.hopPeeledRate, ← hhdef, hJdef]
      rw [this, hJk]
      congr 1
      ext x
      simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff, not_and]
      constructor
      · rintro ⟨hc, hF⟩; exact ⟨hF, fun ha => (hc ha hF)⟩
      · rintro ⟨hF, hna⟩; exact ⟨fun ha _ => hna ha, hF⟩
    -- the share inequality at h
    have hsh := hshare h (Finset.mem_inter.mpr ⟨hmemFl, hiact⟩)
    rw [hJk, hρk, div_mul_eq_mul_div, Finset.inter_comm act (t.net.flowsThrough h)]
    exact le_of_lt hsh

/-! ## Outer peeling induction and the general theorem -/

/-- **Per-flow stability bound**: flow `j` has a per-server token-bucket arrival bound
of its own rate `r j` on both its input and its departure at every server it crosses.
This is the bridge's conclusion and the peeling-induction carrier. -/
def PerFlowBound (t : Traj κ ι) (j : ι) : Prop :=
  ∃ B : κ → ℝ≥0,
    (∀ h, j ∈ t.net.flowsThrough h →
      IsMaximalArrivalBound (⇑(t.Ain h j)) (fun s => t.r j * s + B h)) ∧
    (∀ h, j ∈ t.net.flowsThrough h →
      IsMaximalArrivalBound (⇑(t.Dout h j)) (fun s => t.r j * s + B h))

/-- The peeled flows' aggregate departure at a server `h` (over `Fl h ∩ actᶜ`) is
token-bucket bounded with rate `∑_{Fl h ∩ actᶜ} r` — the `hpeeled` hypothesis of the
bridge, derived from the per-flow departure bounds of the already-peeled flows. -/
theorem peeledAggregate (t : Traj κ ι) (act : Finset ι)
    (hpeeled : ∀ j ∈ actᶜ, t.PerFlowBound j) (h : κ) :
    ∃ bb : ℝ≥0, IsMaximalArrivalBound
      (fun x => ∑ j ∈ (t.net.flowsThrough h ∩ actᶜ), (t.Dout h j) x)
      (fun v => (∑ j ∈ t.net.flowsThrough h ∩ actᶜ, t.r j) * v + bb) := by
  classical
  -- choose each peeled flow's departure burst at h (junk off the set)
  have hch : ∀ j : ι, ∃ B : ℝ≥0, j ∈ t.net.flowsThrough h ∩ actᶜ →
      IsMaximalArrivalBound (⇑(t.Dout h j)) (fun s => t.r j * s + B) := by
    intro j
    by_cases hj : j ∈ t.net.flowsThrough h ∩ actᶜ
    · obtain ⟨hjF, hjc⟩ := Finset.mem_inter.mp hj
      obtain ⟨B, _, hBd⟩ := hpeeled j hjc
      exact ⟨B h, fun _ => hBd h hjF⟩
    · exact ⟨0, fun hcon => absurd hcon hj⟩
  choose B hB using hch
  refine ⟨∑ j ∈ t.net.flowsThrough h ∩ actᶜ, B j, ?_⟩
  have hsum := isMaximalArrivalBound_sum (T := ℝ≥0) (t.net.flowsThrough h ∩ actᶜ)
    (A := fun j => ⇑(t.Dout h j)) (α := fun j s => t.r j * s + B j)
    (fun j hj => hB j hj)
  -- reshape `∑ⱼ (rⱼ v + Bⱼ) = (∑ⱼ rⱼ) v + ∑ⱼ Bⱼ`
  have hreshape : (fun v => ∑ j ∈ t.net.flowsThrough h ∩ actᶜ, (t.r j * v + B j))
      = (fun v => (∑ j ∈ t.net.flowsThrough h ∩ actᶜ, t.r j) * v
          + ∑ j ∈ t.net.flowsThrough h ∩ actᶜ, B j) := by
    funext v; rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hreshape] at hsum
  exact hsum

/-- **The peeling step**: with the already-peeled flows `actᶜ` all `PerFlowBound`, an
active flow `i ∈ act` below its residual GPS share at every crossed server is itself
`PerFlowBound`.  Wraps the bridge lemma, discharging its `hpeeled` hypothesis with
`peeledAggregate`. -/
theorem peelStep (t : Traj κ ι) (i : ι) (act : Finset ι) (hiact : i ∈ act)
    (hpeeled : ∀ j ∈ actᶜ, t.PerFlowBound j)
    (hshare : ∀ h, i ∈ t.net.flowsThrough h ∩ act →
      t.r i < t.φ i * (t.R h - ∑ j ∈ t.net.flowsThrough h \ act, t.r j)
        / (∑ j ∈ t.net.flowsThrough h ∩ act, t.φ j)) :
    t.PerFlowBound i := by
  obtain ⟨B, hAin, hDout⟩ := t.bridge i act hiact hshare
    (fun h _ => t.peeledAggregate act hpeeled h)
  exact ⟨B, hAin, hDout⟩

/-- **Critical-flow existence**: on a nonempty active set `act`, there is a flow `i ∈ act`
below its GPS share of the residual capacity `R h − ∑_{Fl h \ act} r` at every server it
crosses (the `r/φ`-minimizer, via `exists_flow_below_residual_share`, bridged from ℝ). -/
theorem exists_critical (t : Traj κ ι) (act : Finset ι) (hact : act.Nonempty) :
    ∃ i ∈ act, ∀ h, i ∈ t.net.flowsThrough h ∩ act →
      t.r i < t.φ i * (t.R h - ∑ j ∈ t.net.flowsThrough h \ act, t.r j)
        / (∑ j ∈ t.net.flowsThrough h ∩ act, t.φ j) := by
  classical
  obtain ⟨i, hiact, hi⟩ := exists_flow_below_residual_share (σ := κ) act hact
    (fun j => (t.r j : ℝ)) (fun j => (t.φ j : ℝ))
    (fun j => by exact_mod_cast t.hφ j)
    (fun h => (t.R h : ℝ)) t.net.flowsThrough
    (fun h => by rw [← NNReal.coe_sum]; exact_mod_cast t.hstab h)
  refine ⟨i, hiact, fun h hmem => ?_⟩
  have hiR := hi h hmem
  -- the peeled rate sum is below `R h`, so truncated sub agrees with real sub
  have hle : (∑ j ∈ t.net.flowsThrough h \ act, t.r j) ≤ t.R h :=
    le_of_lt (lt_of_le_of_lt
      (Finset.sum_le_sum_of_subset (Finset.sdiff_subset)) (t.hstab h))
  rw [show ((t.R h : ℝ) - ∑ j ∈ t.net.flowsThrough h \ act, (t.r j : ℝ))
      = ((t.R h - ∑ j ∈ t.net.flowsThrough h \ act, t.r j : ℝ≥0) : ℝ) by
        rw [NNReal.coe_sub hle, NNReal.coe_sum]] at hiR
  rw [show (t.φ i : ℝ) * ((t.R h - ∑ j ∈ t.net.flowsThrough h \ act, t.r j : ℝ≥0) : ℝ)
        / (∑ j ∈ t.net.flowsThrough h ∩ act, (t.φ j : ℝ))
      = ((t.φ i * (t.R h - ∑ j ∈ t.net.flowsThrough h \ act, t.r j)
          / (∑ j ∈ t.net.flowsThrough h ∩ act, t.φ j) : ℝ≥0) : ℝ) by
        rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sum]] at hiR
  exact_mod_cast hiR

/-- **The outer peeling induction**: for any active set `act` whose peeled complement
`actᶜ` is already `PerFlowBound`, every flow `i ∈ act` is `PerFlowBound`.  Strong
induction on `act`: peel the critical flow (`exists_critical`), bound it (`peelStep`),
recurse on `act.erase c` (whose complement `insert c actᶜ` is now all `PerFlowBound`). -/
theorem peelInduction (t : Traj κ ι) :
    ∀ (act : Finset ι), (∀ j ∈ actᶜ, t.PerFlowBound j) → ∀ i ∈ act, t.PerFlowBound i := by
  classical
  intro act
  induction act using Finset.strongInduction with
  | _ act ih =>
    intro hpeeled i hiact
    -- find the critical flow `c ∈ act`
    obtain ⟨c, hcact, hcrit⟩ := t.exists_critical act ⟨i, hiact⟩
    -- `c` is PerFlowBound by the peeling step
    have hcB : t.PerFlowBound c := t.peelStep c act hcact hpeeled hcrit
    -- `act.erase c` has complement `insert c actᶜ`, all PerFlowBound
    have hpeeled' : ∀ j ∈ (act.erase c)ᶜ, t.PerFlowBound j := by
      intro j hj
      rw [Finset.compl_erase, Finset.mem_insert] at hj
      rcases hj with rfl | hjc
      · exact hcB
      · exact hpeeled j hjc
    have hrest : ∀ j ∈ act.erase c, t.PerFlowBound j :=
      ih (act.erase c) (Finset.erase_ssubset hcact) hpeeled'
    rcases eq_or_ne i c with rfl | hic
    · exact hcB
    · exact hrest i (Finset.mem_erase.mpr ⟨hic, hiact⟩)

/-- Every flow is `PerFlowBound`: instantiate the outer peeling at `act = univ` (whose
complement `∅` is vacuously `PerFlowBound`). -/
theorem allBound (t : Traj κ ι) (i : ι) : t.PerFlowBound i := by
  refine t.peelInduction Finset.univ ?_ i (Finset.mem_univ i)
  intro j hj
  rw [Finset.compl_univ] at hj
  exact absurd hj (Finset.notMem_empty j)

/-- **Theorem 12.5, fully general** (arbitrary per-flow routing `net.paths i : List κ`,
variable per-server populations `net.flowsThrough h`): a locally stable GPS-constant
network trajectory is globally stable at every server — the aggregate input/output at
each server has a bounded backlogged period. Every flow is `PerFlowBound` by the outer
peeling induction (`allBound`), built on the list-path↔ℕ-hop `bridge`; the per-flow
token-bucket bounds aggregate to local stability `∑_{Fl h} r < R h = serviceRate h`,
discharging global stability through `Network.isGloballyStable_of_perFlow_bounds`. -/
theorem isGloballyStable (t : Traj κ ι) :
    ∀ h : κ, IsGloballyStableServer ⇑(∑ i, t.Ain h i) ⇑(∑ i, t.Dout h i) := by
  classical
  -- every flow's per-server token-bucket bound
  have hAll : ∀ i, t.PerFlowBound i := t.allBound
  choose Bfun hBin hBout using hAll
  -- patch off-path: σ h i is the token bucket on `Fl h`, 0 off it
  set σ : κ → ι → ℝ≥0 → ℝ≥0 :=
    fun h i => if i ∈ t.net.flowsThrough h then (fun s => t.r i * s + Bfun i h) else 0
    with hσdef
  -- per (h,i) input arrival bound
  have hbound : ∀ h i, IsMaximalArrivalBound (⇑(t.Ain h i)) (σ h i) := by
    intro h i
    by_cases hih : i ∈ t.net.flowsThrough h
    · simp only [hσdef, if_pos hih]; exact hBin i h hih
    · simp only [hσdef, if_neg hih]
      rw [show t.Ain h i = 0 from t.hoff h i hih, isMaximalArrivalBound_iff_increment]
      intro s d; simp only [Curve.zero_apply, Pi.zero_apply, add_zero, le_refl]
  -- rate of σ h i is r i on Fl h, 0 off it
  have hrate : ∀ h i, longTermArrivalRate (σ h i)
      = (if i ∈ t.net.flowsThrough h then (t.r i : ℝ≥0∞) else 0) := by
    intro h i
    by_cases hih : i ∈ t.net.flowsThrough h
    · simp only [hσdef, if_pos hih, longTermArrivalRate_affine]
    · simp only [hσdef, if_neg hih, longTermArrivalRate_zero]
  -- aggregate local stability of `∑ᵢ σ h i` against net.service h = β_{R h, T h}
  have hagg : ∀ h, IsLocallyStableServer (fun s => ∑ i, σ h i s) (t.net.service h) := by
    intro h
    show longTermArrivalRate (fun s => ∑ i, σ h i s)
      < longTermServiceRate (t.net.service h)
    calc longTermArrivalRate (fun s => ∑ i, σ h i s)
        ≤ ∑ i, longTermArrivalRate (σ h i) := longTermArrivalRate_sum_le Finset.univ _
      _ = ∑ i, (if i ∈ t.net.flowsThrough h then (t.r i : ℝ≥0∞) else 0) :=
          Finset.sum_congr rfl fun i _ => hrate h i
      _ = ∑ i ∈ t.net.flowsThrough h, (t.r i : ℝ≥0∞) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ((∑ i ∈ t.net.flowsThrough h, t.r i : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
      _ < (t.R h : ℝ≥0∞) := by exact_mod_cast t.hstab h
      _ = longTermServiceRate (t.net.service h) := by
          rw [t.hservice h, longTermServiceRate_rateLatency]
  -- final assembly
  exact t.net.isGloballyStable_of_perFlow_bounds t.S t.Ain t.Dout σ
    t.hcaus
    (fun h => by rw [t.hservice h]; exact t.hβ h)
    t.hp hbound hagg

/-- **Per-flow GPS residual**: at a crossed server `h`, flow `i` is served by a strict rate-latency
residual `β_{R',T'}` with share rate `R' = (φᵢ/∑_{Fl h∩J}φ)(R^(h) − ∑_{Fl h\J}r)`, its input is
token-bucket `(rᵢ·s + B')`-bounded, and `rᵢ < R'`. Flow `i` is `r/φ`-minimal in the active set
`J = {j : rᵢφⱼ ≤ rⱼφᵢ}` (i and the heavier-per-weight flows), so the GPS peel step leaves it that
share (the lighter flows `Fl h\J` already bounded by `allBound`, aggregated by `peeledAggregate`),
and `gps_share_lt_of_cross` places its rate below it. The shared core of the per-flow stability and
delay bounds; unlike the static-priority `SpNetwork.Traj.flowResidualBound`, the active set is
selected per flow by the `r/φ` order rather than a fixed priority. -/
theorem flowResidualBound (t : Traj κ ι) (i : ι) (h : κ) (hh : i ∈ t.net.flowsThrough h) :
    ∃ (R' T' B' : ℝ≥0) (Si : Curve → Curve → Prop),
      IsCausal Si ∧ IsStrictMinimalServiceCurve (rateLatency R' T') Si ∧
        Si (t.Ain h i) (t.Dout h i) ∧
        IsMaximalArrivalBound (⇑(t.Ain h i)) (fun s => t.r i * s + B') ∧ t.r i < R' := by
  classical
  -- the active set: i and the flows at least as heavy per weight (`rᵢφⱼ ≤ rⱼφᵢ`)
  set J : Finset ι := Finset.univ.filter (fun j => t.r i * t.φ j ≤ t.r j * t.φ i) with hJ
  have hiJ : i ∈ J := by rw [hJ]; simp
  have hiJh : i ∈ t.net.flowsThrough h ∩ J := Finset.mem_inter.mpr ⟨hh, hiJ⟩
  -- the lighter (peeled) crossing flows `Fl h ∩ Jᶜ = Fl h \ J` are bounded (allBound)
  obtain ⟨bb, hbb⟩ := t.peeledAggregate J (fun j _ => t.allBound j) h
  set ρ : ℝ≥0 := ∑ j ∈ t.net.flowsThrough h ∩ Jᶜ, t.r j with hρ
  -- `∑_{Fl h∩J} r + ρ = ∑_{Fl h} r`
  have hpart : (∑ j ∈ t.net.flowsThrough h ∩ J, t.r j) + ρ = ∑ j ∈ t.net.flowsThrough h, t.r j := by
    rw [hρ, ← Finset.sum_inter_add_sum_diff (t.net.flowsThrough h) J]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
  have hρR : ρ < t.R h := by
    have : ρ ≤ ∑ j ∈ t.net.flowsThrough h, t.r j := by rw [← hpart]; exact le_add_self
    exact lt_of_le_of_lt this (t.hstab h)
  -- the GPS peel step: flow `i` sees its residual rate-latency share
  have hβ := isStrictMinimalServiceCurve_residualServer_gpsPeel
    (S := t.S h) (φ := t.φ) (R := t.R h) (T := t.T h) (ρ := ρ) (b := bb)
    (J := t.net.flowsThrough h ∩ J) (i := i) hiJh hρR (t.hcaus h) (t.hβ h) (t.hgps h)
  -- the served pair: rewrite the peeled departure sum to `peeledAggregate`'s `Fl h ∩ Jᶜ` form
  have hsetEq : (fun x => ∑ j ∈ (t.net.flowsThrough h ∩ J)ᶜ, (t.Dout h j) x)
      = (fun x => ∑ j ∈ t.net.flowsThrough h ∩ Jᶜ, (t.Dout h j) x) := by
    funext x
    symm
    apply Finset.sum_subset
    · intro j hj
      obtain ⟨hjF, hjc⟩ := Finset.mem_inter.mp hj
      exact Finset.mem_compl.mpr fun hin => (Finset.mem_compl.mp hjc) (Finset.mem_inter.mp hin).2
    · intro j hjc hjnotin
      have hjnotF : j ∉ t.net.flowsThrough h := by
        intro hjF
        have hjnotJ : j ∉ J := fun hjJ =>
          (Finset.mem_compl.mp hjc) (Finset.mem_inter.mpr ⟨hjF, hjJ⟩)
        exact hjnotin (Finset.mem_inter.mpr ⟨hjF, Finset.mem_compl.mpr hjnotJ⟩)
      rw [t.Dout_off h j hjnotF, Curve.zero_apply]
  have hpair : residualServer (fun A D => t.S h A D ∧ IsMaximalArrivalBound
      (fun x => ∑ j ∈ (t.net.flowsThrough h ∩ J)ᶜ, (D j) x) (fun v => ρ * v + bb)) i
      (t.Ain h i) (t.Dout h i) := by
    refine ⟨t.Ain h, t.Dout h, ⟨t.hp h, ?_⟩, rfl, rfl⟩
    rw [hsetEq]; exact hbb
  -- flow `i`'s own arrival bound at `h`
  obtain ⟨Bi, hBin, _⟩ := t.allBound i
  -- local stability: `r i < (φ i / ∑_{Fl h∩J} φ)(R h − ρ)`
  have hshare : t.r i < (t.φ i / ∑ j ∈ t.net.flowsThrough h ∩ J, t.φ j) * (t.R h - ρ) := by
    have hcross : ∀ j ∈ t.net.flowsThrough h ∩ J, (t.r i : ℝ) * (t.φ j : ℝ)
        ≤ (t.r j : ℝ) * (t.φ i : ℝ) := by
      intro j hj
      have := (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2
      exact_mod_cast this
    have hstabℝ : (∑ j ∈ t.net.flowsThrough h ∩ J, (t.r j : ℝ)) < (t.R h : ℝ) - (ρ : ℝ) := by
      have : (∑ j ∈ t.net.flowsThrough h ∩ J, (t.r j : ℝ)) + (ρ : ℝ) < (t.R h : ℝ) := by
        rw [← NNReal.coe_sum, ← NNReal.coe_add, hpart]; exact_mod_cast t.hstab h
      linarith
    rw [← NNReal.coe_lt_coe, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_sub (le_of_lt hρR), NNReal.coe_sum, div_mul_eq_mul_div]
    exact gps_share_lt_of_cross (fun j => (t.r j : ℝ)) (fun j => (t.φ j : ℝ))
      (fun j => by exact_mod_cast t.hφ j) hiJh hcross hstabℝ
  exact ⟨_, _, Bi h, _,
    isCausal_residualServer (fun A D hAD => t.hcaus h A D hAD.1) i, hβ, hpair, hBin h hh, hshare⟩

/-- **Per-flow global stability (GPS)**: in a locally stable GPS-constant network, *each individual
flow* `i` has a bounded backlogged period at every server `h` it crosses (stronger than the
per-server aggregate `isGloballyStable`); flow `i` is locally stable against its GPS residual
(`flowResidualBound`). Unlike the static-priority `SpNetwork.Traj.isFlowGloballyStable`, the active
set is selected per flow by the `r/φ` order rather than a fixed priority. -/
theorem isFlowGloballyStable (t : Traj κ ι) (i : ι) (h : κ) (hh : i ∈ t.net.flowsThrough h) :
    IsGloballyStableServer (⇑(t.Ain h i)) (⇑(t.Dout h i)) := by
  obtain ⟨R', T', B', Si, hc, hβ, hp, harr, hlt⟩ := t.flowResidualBound i h hh
  refine isGloballyStableServer_of_isLocallyStableServer hc hβ hp harr ?_
  show longTermArrivalRate (fun s => t.r i * s + B') < longTermServiceRate (rateLatency R' T')
  rw [longTermArrivalRate_affine, longTermServiceRate_rateLatency]
  exact_mod_cast hlt

/-- **Per-flow delay bound (GPS)**: flow `i`'s virtual delay at a crossed server `h` is finite —
bounded by `T' + B'/R'` of its GPS residual (`flowResidualBound`). The quantitative companion of
`isFlowGloballyStable`. -/
theorem isFlowDelayBounded (t : Traj κ ι) (i : ι) (h : κ) (hh : i ∈ t.net.flowsThrough h) :
    ∃ d : ℝ≥0, Deviation.delay (⇑(t.Ain h i)) (⇑(t.Dout h i)) ≤ (d : ℝ≥0∞) := by
  obtain ⟨R', T', B', Si, hc, hβ, hp, harr, hlt⟩ := t.flowResidualBound i h hh
  exact ⟨T' + B' / R', delay_le_of_strictRateLatency_affine hc hβ hp harr
    (lt_of_le_of_lt (zero_le' (a := t.r i)) hlt) (le_of_lt hlt)⟩

end Traj

/-! ## Faithfulness checks (Theorem 12.5, fully general) -/

/-- The fully general theorem applies to an **arbitrary** network topology: the routing
`net.paths : ι → List κ` is unconstrained and the per-server populations
`net.flowsThrough h` vary freely — there is no shared-path / tandem restriction. -/
example (t : Traj κ ι) :
    ∀ h : κ, IsGloballyStableServer ⇑(∑ i, t.Ain h i) ⇑(∑ i, t.Dout h i) :=
  t.isGloballyStable

/-- The per-flow `bridge` discharges one flow's stability bound from the engine body, the
reusable crux: a flow below its residual GPS share at each crossed server, with its
already-peeled crossing flows token-bucket bounded, gets its own per-server token-bucket
input/departure bound of rate `r i`. -/
example (t : Traj κ ι) (i : ι) (act : Finset ι) (hiact : i ∈ act)
    (hshare : ∀ h, i ∈ t.net.flowsThrough h ∩ act →
      t.r i < t.φ i * (t.R h - ∑ j ∈ t.net.flowsThrough h \ act, t.r j)
        / (∑ j ∈ t.net.flowsThrough h ∩ act, t.φ j))
    (hpeeled : ∀ h, i ∈ t.net.flowsThrough h → ∃ bb : ℝ≥0,
      IsMaximalArrivalBound
        (fun x => ∑ j ∈ (t.net.flowsThrough h ∩ actᶜ), (t.Dout h j) x)
        (fun v => (∑ j ∈ t.net.flowsThrough h ∩ actᶜ, t.r j) * v + bb)) :
    ∃ B : κ → ℝ≥0,
      (∀ h, i ∈ t.net.flowsThrough h →
        IsMaximalArrivalBound (⇑(t.Ain h i)) (fun s => t.r i * s + B h)) ∧
      (∀ h, i ∈ t.net.flowsThrough h →
        IsMaximalArrivalBound (⇑(t.Dout h i)) (fun s => t.r i * s + B h)) :=
  t.bridge i act hiact hshare hpeeled

end DeepWiki.GpsNetwork
