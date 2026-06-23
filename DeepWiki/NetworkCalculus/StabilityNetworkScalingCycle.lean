import DeepWiki.NetworkCalculus.StabilityNetworkScalingInstability
import DeepWiki.NetworkCalculus.StabilityNetworkScalingTrajectory

/-! # The Fig. 12.5 coupled per-cycle burst map (cyclic scaling dynamics)

The §12.4.2 cyclic scaling network (book p.284–285, Fig. 12.5) is two rate-`1` servers, each
cross-scaling the other's flow (`m₂` into server 2, `m₄` into server 1). The instability is
*generated* by the feedback loop: a burst of size `σ` on server 1 produces, after one full
trip through both servers, an *amplified* burst of size `c·σ + d` back on server 1, with
gain `c = m₂m₄/((1−m₂)(1−m₄)) ≥ 1` when `m₂ + m₄ ≥ 1`.

This chapter assembles that **per-cycle burst map as the composition of the two servers'
single-hop burst operations** — not as a postulated affine map. The single hop
`hopBurst m σ = 1 + mσ/(1−m)` is the genuine descaled NC output burst of one server
(`descaledOutputBurst_zero`: residual rate-latency `scalingResidual_rateLatency` + Theorem 7.1
output `input ⊘ service`); the cycle map `cycleBurst = hopBurst m₄ ∘ hopBurst m₂` is the
composition of server 1's hop (cross-scale `m₂`) and server 2's hop (cross-scale `m₄`), and is
proved equal to the `burstSeq` affine step `σ ↦ c·σ + d` via `scalingFixpointPair_substitute`.
Iterating the cycle map then *generates* the geometric `burstSeq` (`cycleBurst_iterate_eq_burstSeq`),
so the server-1 backlog after `n` cycles is `burstSeq c d 0 n` — realizing the
`burstTrajectory` / `backlog_burstTrajectory = ⊤` divergence by the coupled dynamics.

A `linearScale`-inverse layer (`linearScaleInv`) formalizes the [FID 06b] Def. 3.3 descaled
backlog `b(t) = F(t) − S⁻¹(F_S(t))` for the linear (constant) scaling regime. The general
served-pair coupled-network model is scoped at the end. -/

namespace DeepWiki

open scoped NNReal ENNReal
open Deviation

/-! ## (1) The single-hop burst map and the per-cycle composition -/

/-- **The single-hop descaled output burst map** `σ ↦ 1 + mσ/(1−m)` of one Fig. 12.5 server:
a cross-flow with burstiness `σ`, scaled by `m`, crossing a rate-`1` server, descaled, leaves
with burstiness `1 + mσ/(1−m)`. This is exactly the genuine NC output burst grounded in
`descaledOutputBurst_zero` (residual rate-latency + Theorem 7.1 deconvolution); see
`hopBurst_eq_descaledOutputBurst`. -/
noncomputable def hopBurst (m : ℝ≥0) : ℝ≥0 → ℝ≥0 := fun σ => 1 + m * σ / (1 - m)

/-- `hopBurst m σ = 1 + mσ/(1−m)`. -/
@[simp] theorem hopBurst_apply (m σ : ℝ≥0) : hopBurst m σ = 1 + m * σ / (1 - m) := rfl

/-- **The single-hop burst map is the genuine descaled NC output burst** (grounding): the
abstract `hopBurst m₄ σ` equals the descaled output of the scaled flow `m₁γ_{1,1}` through its
residual rate-latency `β_{1−m₄, m₄σ/(1−m₄)}`, evaluated at the origin
(`descaledOutputBurst_zero`). So the per-hop step of the coupled dynamics is read off the real
output operation `input ⊘ service`, not postulated — the `m₁` cancels under the `1/m₁`
descaling, which is why only the cross-scaling `m₄` survives. -/
theorem hopBurst_eq_descaledOutputBurst {m1 m4 σ : ℝ≥0}
    (hm1 : 0 < m1) (hm4 : 0 < m4) (h4 : m4 < 1) (hσ : 0 < σ) (hstab : m1 ≤ 1 - m4) :
    ((hopBurst m4 σ : ℝ≥0) : ℝ≥0∞)
      = (↑(1 / m1) : ℝ≥0∞) *
          minDeconv (tokenBucketNN m1 m1) (rateLatencyNN (1 - m4) (m4 * σ / (1 - m4))) 0 := by
  rw [descaledOutputBurst_zero hm1 hm4 h4 hσ hstab, hopBurst_apply]

/-- **The per-cycle burst map of the Fig. 12.5 loop** `cycleBurst m₂ m₄ = hopBurst m₄ ∘ hopBurst m₂`:
one full trip of flow 1's burstiness around the cycle — server 1's hop scales the cross-flow by
`m₂` (producing `hopBurst m₂ σ`), then server 2's hop scales by `m₄` (producing
`hopBurst m₄ (hopBurst m₂ σ)`), returning the amplified burst to server 1. The coupled feedback
*as the composition of the two single-hop output operations*, not an asserted affine map. -/
noncomputable def cycleBurst (m2 m4 : ℝ≥0) : ℝ≥0 → ℝ≥0 := hopBurst m4 ∘ hopBurst m2

/-- `cycleBurst m₂ m₄ σ = 1 + m₄(1 + m₂σ/(1−m₂))/(1−m₄)`: the nested two-hop burst. -/
theorem cycleBurst_apply (m2 m4 σ : ℝ≥0) :
    cycleBurst m2 m4 σ = 1 + m4 * (1 + m2 * σ / (1 - m2)) / (1 - m4) := by
  simp only [cycleBurst, Function.comp_apply, hopBurst_apply]

/-- **The cycle map is the `burstSeq` affine step** `σ ↦ c·σ + d`: composing the two single-hop
burst operations collapses (via `scalingFixpointPair_substitute`) to gain
`c = m₂m₄/((1−m₂)(1−m₄))` and offset `d = 1 + m₄/(1−m₄)` — the per-cycle gain *derived* from the
scale-and-residual composition, exactly the `burstSeq` step. -/
theorem cycleBurst_eq_step {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) (σ : ℝ≥0) :
    cycleBurst m2 m4 σ
      = m2 * m4 / ((1 - m2) * (1 - m4)) * σ + (1 + m4 / (1 - m4)) := by
  rw [cycleBurst_apply, scalingFixpointPair_substitute h2 h4]

/-- The per-cycle gain `c = m₂m₄/((1−m₂)(1−m₄))` of the cycle map, named. -/
noncomputable def cycleGain (m2 m4 : ℝ≥0) : ℝ≥0 := m2 * m4 / ((1 - m2) * (1 - m4))

/-- The per-cycle offset `d = 1 + m₄/(1−m₄)` of the cycle map, named. -/
noncomputable def cycleOffset (m4 : ℝ≥0) : ℝ≥0 := 1 + m4 / (1 - m4)

/-- The offset is positive: `d = 1 + m₄/(1−m₄) > 0` (so the loop injects fresh burst each cycle). -/
theorem cycleOffset_pos (m4 : ℝ≥0) : 0 < cycleOffset m4 := by
  rw [cycleOffset]; positivity

/-- **The cycle map is exactly the named affine `burstSeq` step**: `cycleBurst m₂ m₄ σ
= cycleGain·σ + cycleOffset` — the per-cycle map and the `burstSeq` recursion coincide. -/
theorem cycleBurst_eq {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) (σ : ℝ≥0) :
    cycleBurst m2 m4 σ = cycleGain m2 m4 * σ + cycleOffset m4 := by
  rw [cycleGain, cycleOffset, cycleBurst_eq_step h2 h4]

/-- **The per-cycle gain is below `1` iff `m₂ + m₄ < 1`** (the stability boundary, on the
cycle-map gain): the loop's amplification factor `cycleGain = m₂m₄/((1−m₂)(1−m₄))` is `< 1` iff
`m₂ + m₄ < 1`. So `m₂ + m₄ ≥ 1` makes the cycle map *expand* (`cycleGain ≥ 1`). -/
theorem cycleGain_lt_one_iff {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) :
    cycleGain m2 m4 < 1 ↔ m2 + m4 < 1 := by
  rw [cycleGain]; exact scaling_gain_lt_one_iff h2 h4

/-- **The per-cycle gain factors as the product of the two per-hop gains** `(mᵢ/(1−mᵢ))`: the
loop gain is the product of server 1's per-hop gain `m₂/(1−m₂)` and server 2's per-hop gain
`m₄/(1−m₄)`, each a single-hop scale-over-residual ratio (`scaling_gain_eq_perHop_prod`). -/
theorem cycleGain_eq_perHop_prod (m2 m4 : ℝ≥0) :
    cycleGain m2 m4 = m2 / (1 - m2) * (m4 / (1 - m4)) := by
  rw [cycleGain]; exact scaling_gain_eq_perHop_prod m2 m4

/-! ## (2) Iterating the cycle map generates the geometric `burstSeq` -/

/-- **Iterating the cycle map generates the geometric burst sequence**: applying the coupled
per-cycle map `cycleBurst m₂ m₄` `n` times to the initial burst `σ₀` yields
`burstSeq (cycleGain) (cycleOffset) σ₀ n` — the explicit geometric trajectory
`cⁿσ₀ + d·∑cᵏ` (`burstSeq_eq`). So the Fig. 12.5 loop's server-1 burstiness after `n`
cycles is exactly the geometric `burstSeq`, *generated* by the composed scale/residual
dynamics rather than posited. -/
theorem cycleBurst_iterate_eq_burstSeq {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1)
    (σ₀ : ℝ≥0) (n : ℕ) :
    (cycleBurst m2 m4)^[n] σ₀ = burstSeq (cycleGain m2 m4) (cycleOffset m4) σ₀ n := by
  induction n with
  | zero => simp [burstSeq_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, burstSeq_succ, cycleBurst_eq h2 h4]

/-- **The server-1 burstiness after `n` cycles, in geometric closed form**: iterating the
coupled cycle map gives `cⁿσ₀ + d·∑_{k<n} cᵏ` with `c = cycleGain`, `d = cycleOffset` —
the explicit growth law of the feedback loop. -/
theorem cycleBurst_iterate_eq {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) (σ₀ : ℝ≥0) (n : ℕ) :
    (cycleBurst m2 m4)^[n] σ₀
      = cycleGain m2 m4 ^ n * σ₀
          + cycleOffset m4 * ∑ k ∈ Finset.range n, cycleGain m2 m4 ^ k := by
  rw [cycleBurst_iterate_eq_burstSeq h2 h4, burstSeq_eq]

/-- **The coupled cycle dynamics diverge when `m₂ + m₄ ≥ 1`**: iterating the Fig. 12.5 per-cycle
burst map (built from the two single-hop scale/residual operations) exceeds every threshold `M`.
Combines `cycleBurst_iterate_eq_burstSeq` with the `burstSeq` divergence: the loop gain `≥ 1`
(`cycleGain_lt_one_iff`) and the positive injection `cycleOffset > 0` force unbounded growth. -/
theorem cycleBurst_iterate_unbounded {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1)
    (hge : 1 ≤ m2 + m4) (σ₀ M : ℝ≥0) :
    ∃ n : ℕ, M ≤ (cycleBurst m2 m4)^[n] σ₀ := by
  have hc : 1 ≤ cycleGain m2 m4 :=
    not_lt.mp fun h => absurd ((cycleGain_lt_one_iff h2 h4).mp h) (not_lt.mpr hge)
  obtain ⟨n, hn⟩ := burstSeq_unbounded hc (cycleOffset_pos m4) σ₀ M
  exact ⟨n, by rw [cycleBurst_iterate_eq_burstSeq h2 h4]; exact hn⟩

/-! ## The coupled dynamics realize the geometric backlog trajectory -/

/-- **The Fig. 12.5 loop's server-1 backlog after `n` cycles is the geometric burst `σₙ`**: the
coupled cycle map iterated from empty initial burst (`σ₀ = 0`) is `burstSeq c d 0 n`, which is the
backlog at the phase-`n` boundary of the adversarial `burstTrajectory` against a stalled departure
(`backlogAt_burstTrajectory_natCast`). So the existing `burstTrajectory`/`burstSeq` divergence is
realized *by* the coupled served-pair dynamics, not merely posited alongside them. -/
theorem cycleBurst_iterate_eq_backlogAt {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) (n : ℕ) :
    (cycleBurst m2 m4)^[n] 0
      = backlogAt (burstTrajectory (cycleGain m2 m4) (cycleOffset m4)) (fun _ => 0) (n : ℝ≥0) := by
  rw [cycleBurst_iterate_eq_burstSeq h2 h4, backlogAt_burstTrajectory_natCast]

/-- **The coupled cyclic dynamics drive the backlog to `⊤`** (`m₂ + m₄ ≥ 1`): the
`burstTrajectory` with the *cycle map's* gain and offset has infinite `Deviation.backlog`
against a stalled departure — the geometric backlog growth of `backlog_burstTrajectory`,
realized by the genuine Fig. 12.5 feedback loop. The loop gain `≥ 1` (`cycleGain_lt_one_iff`)
plus the positive per-cycle injection `cycleOffset > 0` is exactly the divergence hypothesis. -/
theorem backlog_burstTrajectory_cycle {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1)
    (hge : 1 ≤ m2 + m4) :
    backlog (burstTrajectory (cycleGain m2 m4) (cycleOffset m4)) (fun _ => 0) = ⊤ := by
  have hc : 1 ≤ cycleGain m2 m4 :=
    not_lt.mp fun h => absurd ((cycleGain_lt_one_iff h2 h4).mp h) (not_lt.mpr hge)
  exact backlog_burstTrajectory _ _ hc (cycleOffset_pos m4)

/-! ## (3) The descaled backlog of the linear scaling regime ([FID 06b] Def. 3.3) -/

/-- **The inverse linear scaling** `S⁻¹ = linearScale (1/m)` (the descaling `a ↦ a/m` that
returns scaled data to its original scale, the `1/mᵢ` of Fig. 12.5). For `m ≠ 0` it is a genuine
left inverse of `linearScale m` (`linearScale_leftInverse`). -/
noncomputable def linearScaleInv (m : ℝ≥0) : ℝ≥0 → ℝ≥0 := linearScale (1 / m)

/-- `linearScaleInv m a = a / m`. -/
@[simp] theorem linearScaleInv_apply (m a : ℝ≥0) : linearScaleInv m a = a / m := by
  simp only [linearScaleInv, linearScale_apply, one_div]; rw [inv_mul_eq_div]

/-- **The descaling is a left inverse of the linear scaling** (`m ≠ 0`):
`linearScaleInv m (linearScale m a) = a`, i.e. `(1/m)·(m·a) = a` — descaling exactly undoes the
`mᵢ` scaling on the relevant range, as in Fig. 12.5's `mᵢ` / `1/mᵢ` pairs. -/
theorem linearScale_leftInverse {m : ℝ≥0} (hm : m ≠ 0) :
    Function.LeftInverse (linearScaleInv m) (linearScale m) := by
  intro a
  rw [linearScaleInv_apply, linearScale_apply, mul_comm, mul_div_assoc, div_self hm, mul_one]

/-- **The descaled backlog** ([FID 06b] Def. 3.3): the backlog seen from the data source through
the inverse scaling, `b(t) = F(t) − S⁻¹(F_S(t))`, where `F` is the source cumulative, `F_S` the
scaled-output cumulative, and `S⁻¹` the descaling. Stated pointwise in `ℝ≥0` (truncated `−`). -/
noncomputable def descaledBacklog (Sinv F FS : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => F t - Sinv (FS t)

/-- `descaledBacklog Sinv F FS t = F t − S⁻¹(F_S t)`. -/
@[simp] theorem descaledBacklog_apply (Sinv F FS : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    descaledBacklog Sinv F FS t = F t - Sinv (FS t) := rfl

/-- **The descaled backlog of a linearly scaled output is the ordinary backlog** (`m ≠ 0`): when
the output is `F_S = linearScale m ∘ D` (the source departure `D` scaled by `m`) and the descaling
is `S⁻¹ = linearScale (1/m)`, the descaled backlog `F(t) − S⁻¹(F_S(t))` collapses to the plain
backlog `F(t) − D(t)` — descaling undoes the scaling (`linearScale_leftInverse`). So Def. 3.3
agrees with the direct backlog reading in the linear (constant) scaling regime of §12.4.2. -/
theorem descaledBacklog_linearScale {m : ℝ≥0} (hm : m ≠ 0) (F D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    descaledBacklog (linearScaleInv m) F (scale (linearScale m) D) t = F t - D t := by
  rw [descaledBacklog_apply, scale_apply, linearScale_leftInverse hm (D t)]

/-! ## Faithfulness checks against the book / [FID 06b] -/

/-- The cycle map is the composition of the two single-hop burst operations. -/
example (m2 m4 : ℝ≥0) : cycleBurst m2 m4 = hopBurst m4 ∘ hopBurst m2 := rfl

/-- The composed cycle map is the `burstSeq` affine step `σ ↦ c·σ + d`. -/
example {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) (σ : ℝ≥0) :
    cycleBurst m2 m4 σ = cycleGain m2 m4 * σ + cycleOffset m4 :=
  cycleBurst_eq h2 h4 σ

/-- Iterating the cycle map generates the geometric `burstSeq`. -/
example {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) (σ₀ : ℝ≥0) (n : ℕ) :
    (cycleBurst m2 m4)^[n] σ₀ = burstSeq (cycleGain m2 m4) (cycleOffset m4) σ₀ n :=
  cycleBurst_iterate_eq_burstSeq h2 h4 σ₀ n

/-- Def. 3.3 wording: the descaled backlog is `F(t) − S⁻¹(F_S(t))`. -/
example (Sinv F FS : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    descaledBacklog Sinv F FS t = F t - Sinv (FS t) :=
  rfl

/-! ## Scope: the general coupled served-pair network model

The two single-hop burst operations are now **composed** into the per-cycle map
(`cycleBurst = hopBurst m₄ ∘ hopBurst m₂`), the per-cycle gain is **derived** from the
scale-and-residual composition (`cycleBurst_eq`, `cycleGain_eq_perHop_prod`), iterating the
cycle map **generates** the geometric `burstSeq` (`cycleBurst_iterate_eq_burstSeq`), and the
generated backlog is the `burstTrajectory`'s, diverging to `⊤` (`backlog_burstTrajectory_cycle`).
The descaled backlog of Def. 3.3 is formalized for the linear regime
(`descaledBacklog_linearScale`). This is the **concrete 2-server cyclic recursion**, grounded in
the genuine NC output/residual operations.

What a **FULL Fig. 12.5 served-pair-relation network model** needs *beyond* this concrete
recursion — and is therefore **scoped, not formalized** (the general coupled-network dynamics
layer the library lacks):

* **A multi-flow / multi-server served-pair state with feedback coupling.** The concrete map
  here tracks a *single scalar* (server-1 burstiness) around a *fixed* loop. A general model
  carries, per server, an input/output *cumulative-function pair* `(A_i, D_i)` constrained by a
  served-pair (service-curve) relation, with each server's input wired to the *scaled outputs*
  of the servers feeding it via a topology (an arc-indexed family of scalings `m_{ij}`). The
  coupling is a *fix-point over cumulative functions* (each `D_i` depends on the `D_j` that feed
  `i`), not a scalar recursion. Building it needs a `Network`-style indexed family of
  `(server, scaling)` arcs plus a simultaneous served-pair fix-point — a network-dynamics layer
  on top of the existing single-server `Server`/`Deviations` machinery. `[infra]`.

* **The phase-by-phase adversarial *timing* of the transfers.** The book's p.285 sample path
  (phases 1–5: serve flow 2 until `t₁ = m₄/(1−m₄)`, transfer instantaneously, serve flow 1 until
  `t₂`, …) interleaves the two servers' priority service in *continuous time*. Our trajectory
  collapses each cycle to one phase boundary (the staircase `burstTrajectory`); the literal
  piecewise-linear `(A_i, D_i)` schedule with the exact transfer times is the deferred
  construction. The book itself **defers this sample path to [FID 06b]**; reconstructing it
  needs the served-pair model above instantiated with priority scheduling and the explicit phase
  durations. `[deferred]` — to do with the user against Fig. 12.6.

The per-cycle map, its derivation from the scale/residual operations, and its generation of the
geometric backlog trajectory are the achievable, faithful core; the general served-pair coupled
network and the literal continuous-time sample path are the scoped remainder. -/

end DeepWiki
