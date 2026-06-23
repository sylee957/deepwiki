import DeepWiki.NetworkCalculus.ScalingFunction
import DeepWiki.NetworkCalculus.ServersBacklog
import DeepWiki.NetworkCalculus.Deviations

/-! # The §12.4.2 adversarial scaling trajectory (geometric backlog growth)

The explicit per-phase backlog sequence of the Fig. 12.5 cyclic scaling network and a
concrete cumulative-function witness exhibiting geometric backlog growth.

Building on `linearIterate_unbounded` (the *gain* divergence) and `scaling_gain_*`
(the gain `c = m₂m₄/((1−m₂)(1−m₄))` grounded in the scaling operations), this chapter
sharpens the divergence to the **explicit geometric closed form** of the per-phase burst
sequence `σₙ₊₁ = c·σₙ + d` — `σₙ = cⁿσ₀ + d·∑_{k<n} cᵏ` — proves it is monotone and
unbounded when `c ≥ 1`, and realizes it as the backlog along a concrete piecewise-linear
**adversarial cumulative trajectory** `A` against a stalled departure `D = 0`: the backlog
`A(τₙ) − D(τₙ)` at the phase-`n` boundaries `τₙ` is exactly `σₙ`, growing geometrically,
so `Deviation.backlog A 0 = ⊤` and `maxBackloggedLength A 0 = ⊤`.

The book (§12.4.2, p. 285) describes this adversarial sample path phase by phase — each
cycle multiplies the server-1 backlog by the gain `m₂m₄/((1−m₂)(1−m₄))`, so when
`m₂ + m₄ > 1` the backlog strictly increases each cycle — and defers the literal path to
[FID 06b]. The witness here is that geometric-growth core; the full Fig. 12.5 served-pair
dynamics that *produce* this path are scoped at the end. -/

namespace DeepWiki

open scoped NNReal ENNReal
open Deviation

/-! ## (1) The per-phase burst sequence — explicit geometric closed form -/

/-- **The per-phase burst sequence** `σₙ` of the §12.4.2 cyclic scaling network: the
fix-point iteration `σ₀, σ₁ = c·σ₀ + d, …, σₙ₊₁ = c·σₙ + d` with gain `c` and per-cycle
injection `d`. This is exactly `(fun σ => c·σ + d)^[n] σ₀` of `linearIterate_unbounded`,
named as the burst trajectory it represents. -/
noncomputable def burstSeq (c d σ₀ : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  (fun σ => c * σ + d)^[n] σ₀

/-- `burstSeq c d σ₀ 0 = σ₀`: the trajectory starts at the initial burst. -/
@[simp] theorem burstSeq_zero (c d σ₀ : ℝ≥0) : burstSeq c d σ₀ 0 = σ₀ := rfl

/-- The recursion `σₙ₊₁ = c·σₙ + d`. -/
theorem burstSeq_succ (c d σ₀ : ℝ≥0) (n : ℕ) :
    burstSeq c d σ₀ (n + 1) = c * burstSeq c d σ₀ n + d := by
  rw [burstSeq, burstSeq, Function.iterate_succ_apply']

/-- **Explicit geometric closed form** (the §12.4.2 burst growth):
`σₙ = cⁿ·σ₀ + d·∑_{k<n} cᵏ`. The homogeneous part `cⁿ·σ₀` carries the initial burst, the
particular part `d·∑_{k<n} cᵏ` accumulates the per-cycle injection `d` geometrically. (Stated
with the finite geometric sum `∑_{k<n} cᵏ` to stay division-free in `ℝ≥0`.) -/
theorem burstSeq_eq (c d σ₀ : ℝ≥0) (n : ℕ) :
    burstSeq c d σ₀ n = c ^ n * σ₀ + d * ∑ k ∈ Finset.range n, c ^ k := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hgeom : ∑ k ∈ Finset.range (m + 1), c ^ k
        = 1 + c * ∑ k ∈ Finset.range m, c ^ k := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ, mul_comm, pow_zero]
      rw [add_comm]
    rw [burstSeq_succ, ih, hgeom, pow_succ]
    ring

/-- The burst sequence is monotone (non-decreasing) when the gain `c ≥ 1`: each cycle adds
`d` after a non-shrinking scaling, `σₙ₊₁ = c·σₙ + d ≥ σₙ`. -/
theorem burstSeq_mono {c d σ₀ : ℝ≥0} (hc : 1 ≤ c) : Monotone (burstSeq c d σ₀) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [burstSeq_succ]
  calc burstSeq c d σ₀ n ≤ c * burstSeq c d σ₀ n :=
        le_mul_of_one_le_left (zero_le) hc
    _ ≤ c * burstSeq c d σ₀ n + d := le_self_add

/-- The burst sequence grows at least linearly, `σₙ ≥ σ₀ + n·d`, when `c ≥ 1`: the
homogeneous part is `≥ σ₀` and the geometric injection sum is `≥ n·d`. -/
theorem le_burstSeq {c d σ₀ : ℝ≥0} (hc : 1 ≤ c) (n : ℕ) :
    σ₀ + n * d ≤ burstSeq c d σ₀ n := by
  rw [burstSeq_eq]
  have hpow : (1 : ℝ≥0) ≤ c ^ n := one_le_pow₀ hc
  have hsum : (n : ℝ≥0) ≤ ∑ k ∈ Finset.range n, c ^ k := by
    calc (n : ℝ≥0) = ∑ _k ∈ Finset.range n, (1 : ℝ≥0) := by simp
      _ ≤ ∑ k ∈ Finset.range n, c ^ k :=
          Finset.sum_le_sum fun k _ => one_le_pow₀ hc
  have h1 : σ₀ ≤ c ^ n * σ₀ := le_mul_of_one_le_left (zero_le) hpow
  have h2 : (n : ℝ≥0) * d ≤ d * ∑ k ∈ Finset.range n, c ^ k := by
    rw [mul_comm]; gcongr
  exact add_le_add h1 h2

/-- **The per-phase burst sequence diverges** when the gain `c ≥ 1` and the injection
`d > 0`: every threshold `M` is exceeded by some `σₙ`. This is the monotone-divergence
sharpening of `scalingIterate_unbounded`, stated directly on the named `burstSeq`. -/
theorem burstSeq_unbounded {c d : ℝ≥0} (hc : 1 ≤ c) (hd : 0 < d) (σ₀ M : ℝ≥0) :
    ∃ n : ℕ, M ≤ burstSeq c d σ₀ n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (M / d)
  refine ⟨n, le_trans ?_ (le_trans le_add_self (le_burstSeq hc n))⟩
  calc M = M / d * d := (div_mul_cancel₀ M (ne_of_gt hd)).symm
    _ ≤ (n : ℝ≥0) * d := by gcongr

/-- **The burst sequence tends to `+∞`** (in `ℝ≥0∞`) when `c ≥ 1`, `d > 0`: the geometric
backlog growth is genuine divergence to infinity, not merely an unbounded subsequence. -/
theorem burstSeq_tendsto_atTop {c d : ℝ≥0} (hc : 1 ≤ c) (hd : 0 < d) (σ₀ : ℝ≥0) :
    Filter.Tendsto (fun n => (burstSeq c d σ₀ n : ℝ≥0∞)) Filter.atTop (nhds ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro M
  obtain ⟨n, hn⟩ := burstSeq_unbounded hc hd σ₀ (M + 1)
  refine Filter.eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
  have : (M : ℝ≥0∞) < ((burstSeq c d σ₀ n : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe]
    exact lt_of_lt_of_le (lt_add_one M) hn
  exact lt_of_lt_of_le this (by exact_mod_cast burstSeq_mono hc hm)

/-! ## The geometric ratio is exactly the §12.4.2 scaling gain -/

/-- **The burst-sequence ratio is the cyclic scaling gain**: the per-phase sequence of the
Fig. 12.5 network is `burstSeq` with `c = m₂m₄/((1−m₂)(1−m₄))` — the gain grounded in the
data-scaling operations (`scaling_gain_eq_perHop_prod`/`scaling_gain_numerator_eq_comp`).
So when `m₂ + m₄ ≥ 1` (gain `≥ 1`) the backlog diverges geometrically. -/
theorem scalingBurstSeq_unbounded {m2 m4 d : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1)
    (hge : 1 ≤ m2 + m4) (hd : 0 < d) (σ₀ M : ℝ≥0) :
    ∃ n : ℕ, M ≤ burstSeq (m2 * m4 / ((1 - m2) * (1 - m4))) d σ₀ n :=
  burstSeq_unbounded
    (not_lt.mp fun h => absurd ((scaling_gain_lt_one_iff h2 h4).mp h) (not_lt.mpr hge))
    hd σ₀ M

/-! ### Faithfulness checks (part 1) -/

/-- The burst sequence is exactly the §12.4.2 fix-point iteration of `linearIterate_unbounded`. -/
example (c d σ₀ : ℝ≥0) (n : ℕ) :
    burstSeq c d σ₀ n = (fun σ => c * σ + d)^[n] σ₀ := rfl

/-- The closed form is the geometric sum: `σₙ = cⁿσ₀ + d·(1 + c + ⋯ + cⁿ⁻¹)`. -/
example (c d σ₀ : ℝ≥0) (n : ℕ) :
    burstSeq c d σ₀ n = c ^ n * σ₀ + d * ∑ k ∈ Finset.range n, c ^ k :=
  burstSeq_eq c d σ₀ n

/-! ## (2) A concrete adversarial cumulative trajectory with geometric backlog

A cumulative arrival `burstTrajectory c d` whose value at the phase-`n` boundary `n` is the
burst `σₙ = burstSeq c d 0 n` — the staircase `t ↦ σ_{⌊t⌋}` (the natural bursty-arrival
convention: data arrives in instantaneous bursts at the phase boundaries). It is monotone,
null at the origin, and against a stalled departure `D = 0` realizes the geometric backlog
sequence as an actual `Deviation.backlog` along a trajectory. -/

/-- **The adversarial cumulative trajectory** of the §12.4.2 scaling network: the bursty
arrival `t ↦ σ_{⌊t⌋}` accumulating the per-phase bursts `σₙ = burstSeq c d 0 n` (initial
backlog `0`, per-cycle injection `d`, gain `c`). A staircase: data arrives in instantaneous
bursts at each phase boundary, modelling the adversary releasing the amplified backlog each
cycle. -/
noncomputable def burstTrajectory (c d : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => burstSeq c d 0 ⌊t⌋₊

/-- `burstTrajectory c d t = σ_{⌊t⌋}`. -/
theorem burstTrajectory_apply (c d : ℝ≥0) (t : ℝ≥0) :
    burstTrajectory c d t = burstSeq c d 0 ⌊t⌋₊ := rfl

/-- At a phase boundary `n` the trajectory equals the burst `σₙ`. -/
@[simp] theorem burstTrajectory_natCast (c d : ℝ≥0) (n : ℕ) :
    burstTrajectory c d (n : ℝ≥0) = burstSeq c d 0 n := by
  rw [burstTrajectory_apply, Nat.floor_natCast]

/-- The trajectory is null at the origin: `burstTrajectory c d 0 = 0` (empty initial
backlog). -/
@[simp] theorem burstTrajectory_zero (c d : ℝ≥0) : burstTrajectory c d 0 = 0 := by
  rw [burstTrajectory_apply, Nat.floor_zero, burstSeq_zero]

/-- The trajectory is monotone when the gain `c ≥ 1` (the staircase of the monotone burst
sequence: `⌊·⌋` and `burstSeq` are both monotone). -/
theorem burstTrajectory_mono {c d : ℝ≥0} (hc : 1 ≤ c) : Monotone (burstTrajectory c d) :=
  fun _ _ h => burstSeq_mono hc (Nat.floor_mono h)

/-- **The backlog at the phase-`n` boundary is the burst `σₙ`** (geometric in `n`): against
a stalled departure `D = 0`, the instantaneous backlog at time `n` is exactly
`burstTrajectory c d n − 0 = σₙ`. So the geometric burst sequence is realized as an actual
per-instant backlog along the trajectory. -/
theorem backlogAt_burstTrajectory_natCast (c d : ℝ≥0) (n : ℕ) :
    backlogAt (burstTrajectory c d) (fun _ => 0) (n : ℝ≥0) = burstSeq c d 0 n := by
  rw [backlogAt_eq, burstTrajectory_natCast, tsub_zero]

/-- **The trajectory's backlog is unbounded** (geometric growth, gain `c ≥ 1`): for every
threshold `M` some phase boundary `n` has backlog `σₙ ≥ M` against the stalled departure.
The constructive witness for the divergence `burstSeq_unbounded`. -/
theorem exists_backlogAt_burstTrajectory_ge {c d : ℝ≥0} (hc : 1 ≤ c) (hd : 0 < d) (M : ℝ≥0) :
    ∃ t : ℝ≥0, M ≤ backlogAt (burstTrajectory c d) (fun _ => 0) t := by
  obtain ⟨n, hn⟩ := burstSeq_unbounded hc hd 0 M
  exact ⟨(n : ℝ≥0), by rw [backlogAt_burstTrajectory_natCast]; exact hn⟩

/-- **The trajectory has infinite backlog**: `Deviation.backlog (burstTrajectory c d) 0 = ⊤`
when the gain `c ≥ 1`, `d > 0` — the geometric backlog growth diverges, witnessed
concretely by an arrival cumulative function against a stalled departure. -/
theorem backlog_burstTrajectory (c d : ℝ≥0) (hc : 1 ≤ c) (hd : 0 < d) :
    backlog (burstTrajectory c d) (fun _ => 0) = ⊤ := by
  rw [backlog_eq_iSup, iSup_eq_top]
  intro M hM
  lift M to ℝ≥0 using hM.ne with M
  obtain ⟨t, ht⟩ := exists_backlogAt_burstTrajectory_ge hc hd (M + 1)
  rw [backlogAt_eq, tsub_zero] at ht
  refine ⟨t, ?_⟩
  calc (M : ℝ≥0∞) < ((M + 1 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast lt_add_one M
    _ ≤ ((burstTrajectory c d t - 0 : ℝ≥0) : ℝ≥0∞) := by
        rw [tsub_zero]; exact_mod_cast ht

/-- `σ₁ = d`: the first phase's burst is exactly the injection `d` (from `σ₀ = 0`). -/
theorem burstSeq_one (c d : ℝ≥0) : burstSeq c d 0 1 = d := by
  rw [burstSeq_succ, burstSeq_zero, mul_zero, zero_add]

/-- **The trajectory stays backlogged from phase `1` on**: `(1, n]` is a backlogged period
against the stalled departure for each `n` (positive backlog `σ_{⌊u⌋} ≥ σ₁ = d > 0` once
`u > 1`). The staircase is `0` on `[0, 1)`, so the backlog opens at `1` and never clears. -/
theorem isBacklogged_burstTrajectory {c d : ℝ≥0} (hc : 1 ≤ c) (hd : 0 < d) (n : ℕ) :
    IsBacklogged (burstTrajectory c d) (fun _ => 0) (Set.Ioc 1 (n : ℝ≥0)) := by
  intro u hu
  show (0 : ℝ≥0) < burstTrajectory c d u
  have hfloor : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by exact_mod_cast hu.1.le)
  calc (0 : ℝ≥0) < d := hd
    _ = burstSeq c d 0 1 := (burstSeq_one c d).symm
    _ ≤ burstSeq c d 0 ⌊u⌋₊ := burstSeq_mono hc hfloor
    _ = burstTrajectory c d u := rfl

/-- **The maximal backlogged-period length is infinite**: as the trajectory's backlog never
clears against the stalled departure, the backlogged periods `(1, 1 + k]` grow without bound,
so `maxBackloggedLength (burstTrajectory c d) 0 = ⊤`. -/
theorem maxBackloggedLength_burstTrajectory {c d : ℝ≥0} (hc : 1 ≤ c) (hd : 0 < d) :
    maxBackloggedLength (burstTrajectory c d) (fun _ => 0) = ⊤ := by
  -- The backlogged period `(1, 1 + k]` has length `k`, so the max length exceeds every `k`.
  refine ENNReal.eq_top_of_forall_nnreal_le fun b => ?_
  obtain ⟨k, hk⟩ := exists_nat_ge b
  have hbl : IsBacklogged (burstTrajectory c d) (fun _ => 0)
      (Set.Ioc (1 : ℝ≥0) (1 + (k : ℝ≥0))) := by
    have := isBacklogged_burstTrajectory hc hd (k + 1)
    refine this.subset fun u hu => ⟨hu.1, hu.2.trans ?_⟩
    push_cast; rw [add_comm]
  have hle : ((k : ℝ≥0) : ℝ≥0∞)
      ≤ maxBackloggedLength (burstTrajectory c d) (fun _ => 0) :=
    le_maxBackloggedLength_of_isBacklogged (t := 1) (d := (k : ℝ≥0)) hbl
  exact le_trans (by exact_mod_cast hk) hle

/-! ### Faithfulness checks (part 2) -/

/-- The trajectory's value at phase boundary `n` is the geometric burst `σₙ`. -/
example (c d : ℝ≥0) (n : ℕ) : burstTrajectory c d (n : ℝ≥0) = burstSeq c d 0 n :=
  burstTrajectory_natCast c d n

/-- The trajectory is a genuine cumulative function: monotone and null at the origin
(for gain `c ≥ 1`). -/
example {c d : ℝ≥0} (hc : 1 ≤ c) :
    Monotone (burstTrajectory c d) ∧ burstTrajectory c d 0 = 0 :=
  ⟨burstTrajectory_mono hc, burstTrajectory_zero c d⟩

/-- The backlog along the trajectory diverges to `⊤` (geometric growth realized as an actual
`Deviation.backlog`) when the gain `c ≥ 1`, `d > 0`. -/
example {c d : ℝ≥0} (hc : 1 ≤ c) (hd : 0 < d) :
    backlog (burstTrajectory c d) (fun _ => 0) = ⊤ :=
  backlog_burstTrajectory c d hc hd

/-! ## (3) Scope: what the full Fig. 12.5 cyclic-network reconstruction needs

The two pieces above are the **achievable, citable core** of the §12.4.2 instability tail:

* **(1)** the per-phase burst sequence `σₙ` in **explicit geometric closed form**
  (`burstSeq_eq`), monotone (`burstSeq_mono`) and divergent (`burstSeq_unbounded`,
  `burstSeq_tendsto_atTop`) with ratio the scaling gain `m₂m₄/((1−m₂)(1−m₄))`
  (`scalingBurstSeq_unbounded`) — sharpening the `linearIterate_unbounded` *gain*
  divergence to the exact growth law of the backlog;
* **(2)** a **concrete adversarial cumulative trajectory** `burstTrajectory c d` (a bursty
  staircase) realizing that sequence as an actual `Deviation.backlog`
  (`backlog_burstTrajectory = ⊤`, `maxBackloggedLength_burstTrajectory = ⊤`,
  `backlogAt_burstTrajectory_natCast`), monotone and null at the origin — a genuine flow
  whose backlog grows geometrically with ratio the gain.

What the **full** Fig. 12.5 (book p. 284–285) reconstruction needs *beyond* this witness —
and is therefore **scoped, not formalized**:

* **The cyclic served-pair dynamics that *produce* this trajectory.** The book's adversarial
  sample path (p. 285, phases 1–5) is generated by the *coupled* two-server network: flow 1
  and flow 2 cross-scale each other (`m₁, m₂, m₃, m₄`), each server offering minimal service
  `λ₁`, with instantaneous transfer between servers, so that after one full cycle the
  server-1 backlog is multiplied by `m₂m₄/((1−m₂)(1−m₄))`. Reconstructing this requires a
  *multi-flow, multi-server served-pair model with feedback coupling* (each server's input
  is the scaled output of the other), instantiated against the figure's topology — a
  network-dynamics layer the library does not yet build. The book itself **defers the literal
  sample path to [FID 06b]** and only states the per-cycle multiplication factor; our
  `burstTrajectory` is exactly that per-cycle geometric factor exhibited as a standalone
  flow. `[deferred]` — the coupled served-pair dynamics, to do with the user against
  Fig. 12.5.
* **The descaling/end-to-end backlog reading** `b(t) = F(t) − S⁻¹(F_S(t))` of [FID 06b]
  Def. 3.3 (backlog as seen from the data source through the inverse scaling). Our witness
  reads the backlog directly on the (already-scaled) cumulative pair; the source-side
  descaled reading needs the scaling-function inverse `S⁻¹` and its backlog convention.
  `[deferred]`.

The geometric-growth law and a flow witnessing it are the faithful core; the coupled-network
sample path that drives them is the cited deferral. -/

end DeepWiki
