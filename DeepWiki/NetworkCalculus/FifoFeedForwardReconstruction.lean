import DeepWiki.NetworkCalculus.FifoFeedForwardConcrete
import DeepWiki.NetworkCalculus.ConvolutionMinimum
import DeepWiki.NetworkCalculus.RealCurves

/-! # Lemma 1 (convolution-time existence) and the concrete `N = 1` reconstruction
([BOU 16b], §III–IV)

The foundational tail of the Ch11 §11.2 exact-FIFO reconstruction of Bouillard and Stea,
"Exact Worst-Case Delay in FIFO-Multiplexing Feed-Forward Networks", IEEE/ACM Trans.
Networking 2016 (DOI `10.1109/TNET.2014.2332071`).  `FifoFeedForwardExact` formalizes the
abstract Theorem 1 bridge and the §IV.D bracket; `FifoFeedForwardConcrete` builds the
binary-tree date layout, Lemma 2's pointwise discharges, and Lemma 3's extrapolation core.
This file closes two genuinely residual pieces:

* **(1) Lemma 1 ([BOU 16b], §IV.A, p.4 and used in the Lemma 2 proof, p.7): the
  convolution-attaining (service-curve) time exists.**  For a tagged bit leaving at `t₁`, the
  proof of Lemma 2 sets `t₃ = SC(t₁)` to be a date *attaining* the inf-convolution defining
  the service curve — "by Lemma 1, we can find a time `t₃` such that
  `D^N(t₁) ≥ A^N(t₃) + β^N(t₁ − t₃)`" (p.7).  We prove this attainment over the library's
  `minConvProj` (the `ℝ≥0` inf-convolution `A ∗ β`): for a monotone left-continuous arrival
  `A` and a continuous service curve `β` (rate-latency qualifies), the convolution
  `(A ∗ β)(t)` is attained at some split `t₃ ≤ t`, and any service-curve dominator
  `D ≥ A ∗ β` therefore satisfies `D(t) ≥ A(t₃) + β(t − t₃)`.  This is the backward
  date-recursion's foundation (`exists_serviceCurveTime_le`,
  `exists_serviceCurveTime_of_serviceDominator`).

* **(2) The concrete `N = 1` (single FIFO node) FULL Lemma 2 + Lemma 3 round trip.**  For one
  FIFO server crossed by two token-bucket flows under a rate-latency service curve the
  worst-case delay is the closed form `T + (b₁+b₂)/R` (`fifoNode_programOptimum`).  We make
  the reconstruction *fully explicit* at `N = 1`: (Lemma 2) the explicit worst-case
  *trajectory* `fifoNodeWitness` is feasible and realizes the optimum, so the program optimum
  is `≥` a realizable delay; (Lemma 3) every feasible solution's delay is `≤` the optimum, and
  the optimum itself is *realized* by an actual feasible point — closing both directions of
  Theorem 1 concretely at `N = 1`, with no Boolean ordering variables and no exponential
  enumeration.

The general-`N` reconstruction (global monotonicity / left-continuity of the floor-augmented
extrapolation across windows, and FIFO-order preservation over the `2^?` Boolean orderings)
remains the exponential MILP the paper solves numerically; it is scoped precisely at the end.
CRITICAL HONESTY: no general-`N` closed form is claimed here. -/

namespace DeepWiki

namespace FifoFeedForward

open scoped NNReal Topology
open Set Filter

/-! ## (1) Lemma 1: the convolution-attaining service-curve time exists (§IV.A, p.4; p.7)

[BOU 16b], §IV.A (p.4): for each departure time `t₁` there is "a time `t₃` that verifies the
convolution property stated in Lemma 1 at time `t₁` (henceforth referred to as the service
curve time of `t₁`, `SC(t₁)`)".  Used in the Lemma 2 proof (p.7): "by Lemma 1, we can find a
time `t₃` such that `D^N(t₁) ≥ A^N(t₃) + β^N(t₁ − t₃)`".

The content is the **attainment of the inf-convolution** `(A ∗ β)(t) = inf_{u+s=t} A(u)+β(s)`:
the inf is a *minimum*, reached at a split `(t₃, t₁−t₃)` with `t₃ ≤ t₁`.  The library already
proves this for a monotone left-continuous `A` against a continuous `β` over the projected
convolution `minConvProj` (`exists_minConvProj_eq`); Lemma 1 is its specialization to the
network-calculus service-curve setting, plus the step to a service-curve dominator `D`. -/

/-- **Lemma 1, the convolution-attaining time exists** ([BOU 16b], §IV.A, p.4): for a monotone
left-continuous arrival `A : ℝ≥0 → ℝ≥0` and a continuous service curve `β`, the inf-convolution
`(A ∗ β)(t)` is *attained* — there is a service-curve time `t₃ ≤ t` with
`(A ∗ β)(t) = A(t₃) + β(t − t₃)`, and `t₃` minimizes the split over all `u ≤ t`.  This is the
`SC(t)` of the paper; the backward date recursion of Lemma 2 calls it at every output time. -/
theorem exists_serviceCurveTime {A β : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A) (hβc : Continuous β) (t : ℝ≥0) :
    ∃ t₃ ≤ t, (∀ u ≤ t, A t₃ + β (t - t₃) ≤ A u + β (t - u)) ∧
      minConvProj A β t = A t₃ + β (t - t₃) :=
  exists_minConvProj_eq hAmono hAlc hβc t

/-- **Lemma 1, against a service-curve dominator** ([BOU 16b], p.7, the form used in Lemma 2):
if `D` dominates the service curve, `(A ∗ β)(t) ≤ D(t)` for all `t` (the network-calculus
service-curve property `D ≥ A ∗ β`), then at every exit date `t₁` there is a service date
`t₃ ≤ t₁` with `D(t₁) ≥ A(t₃) + β(t₁ − t₃)`.  This is *exactly* the date the Lemma 2 backward
recursion produces: "by Lemma 1, we can find a time `t₃` such that
`D^N(t₁) ≥ A^N(t₃) + β^N(t₁ − t₃)`". -/
theorem exists_serviceCurveTime_of_serviceDominator {A β D : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A) (hβc : Continuous β)
    (hserv : ∀ t, minConvProj A β t ≤ D t) (t₁ : ℝ≥0) :
    ∃ t₃ ≤ t₁, A t₃ + β (t₁ - t₃) ≤ D t₁ := by
  obtain ⟨t₃, ht₃, _, heq⟩ := exists_serviceCurveTime hAmono hAlc hβc t₁
  exact ⟨t₃, ht₃, heq ▸ hserv t₁⟩

/-- **Lemma 1 for a rate-latency service curve** ([BOU 16b], p.4; the FIFO base case `β = β_{R,T}`):
specialization of `exists_serviceCurveTime_of_serviceDominator` to the rate-latency curve
`β_{R,T}(s) = R·(s − T)₊`, which is continuous (`rateLatency_continuous`).  For a monotone
left-continuous arrival `A` and any departure `D ≥ A ∗ β_{R,T}`, every exit date `t₁` has a
service date `t₃ ≤ t₁` with `D(t₁) ≥ A(t₃) + R·(t₁ − t₃ − T)₊`. -/
theorem exists_serviceCurveTime_rateLatency {A D : ℝ≥0 → ℝ≥0} {R T : ℝ≥0}
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A)
    (hserv : ∀ t, minConvProj A (rateLatency R T) t ≤ D t) (t₁ : ℝ≥0) :
    ∃ t₃ ≤ t₁, A t₃ + R * (t₁ - t₃ - T) ≤ D t₁ :=
  exists_serviceCurveTime_of_serviceDominator hAmono hAlc (rateLatency_continuous R T) hserv t₁

/-! ## (2) The concrete `N = 1` reconstruction: the explicit worst-case trajectory (§IV.A, p.4)

For one FIFO server crossed by two token-bucket flows `γ_{bᵢ,rᵢ}` under a rate-latency service
curve `β_{R,T}`, the worst-case delay is the closed form `T + (b₁+b₂)/R`
(`WorstCaseLPFifoNode.fifoNode_programOptimum`).  We make the Lemma 2 ⟹ Lemma 3 round trip
*fully explicit* at this base case by building the actual worst-case **trajectory** — concrete
cumulative functions on `ℝ≥0` — that realizes the optimum, and showing it is admissible.

The worst case is the *fluid burst*: the aggregate burst `b = b₁ + b₂` arrives instantaneously
at time `0⁺` and the server clears it at rate `R` after latency `T`.  The cumulative arrival is
the left-continuous step `A(t) = b` for `t > 0`, `A(0) = 0`; the cumulative departure is the
exact rate-latency output `D(t) = min(b, R·(t − T)₊) = (A ∗ β_{R,T})(t)`.  The tagged bit (the
last bit of the burst, quota `b`) arrives at `0⁺` and leaves at `T + b/R`, realizing the
optimum. -/

/-- **The worst-case aggregate arrival trajectory** of the single FIFO node (§IV.A, p.4): the
fluid burst `A(t) = b` for `t > 0`, `A(0) = 0`.  Left-continuous (`A(0) = 0`, left limit at any
`t > 0` is `b = A t`), monotone, and `γ_{b,r}`-upper-constrained (the increment never exceeds
the burst `b ≤ b + r·τ`).  This is the ingress CAF whose worst-case bit is delayed by the
node. -/
noncomputable def burstArrival (b : ℝ≥0) : ℝ≥0 → ℝ≥0 := fun t => if 0 < t then b else 0

/-- **The worst-case aggregate departure trajectory** of the single FIFO node (§IV.A, p.4): the
exact rate-latency output `D(t) = min(b, R·(t − T)₊)` of the burst `A` through `β_{R,T}` — the
server clears the burst at rate `R` after latency `T`, capped at the total `b`.  Monotone,
`D ≤ A` (causal), and reaches the full burst `b` exactly at `t = T + b/R`. -/
noncomputable def burstDeparture (b R T : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => min b (R * (t - T))

/-- `burstArrival b` is monotone: it is `0` then `b`, with `0 ≤ b`. -/
theorem burstArrival_mono (b : ℝ≥0) : Monotone (burstArrival b) := by
  intro s t hst
  unfold burstArrival
  split_ifs with hs ht ht
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le hs hst) ht
  · exact bot_le
  · exact le_rfl

/-- `burstArrival b` is left-continuous: it is locally constant on `Iio t` for every `t`
(constant `b` near `t` for `t > 0`, and trivially at `t = 0` where `Iio 0 = ∅`). -/
theorem burstArrival_isLeftContinuous (b : ℝ≥0) : IsLeftContinuous (burstArrival b) := by
  intro t
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · rw [← ht]; exact isLeftContinuousAt_zero _
  · -- on `Ioo 0 t` (a `𝓝[Iio t] t`-neighborhood) `burstArrival b` is constantly `b`
    refine (continuousWithinAt_const (b := b)).congr_of_eventuallyEq ?_ ?_
    · have hmem : Set.Ioo (0 : ℝ≥0) t ∈ 𝓝[Set.Iio t] t :=
        Filter.inter_mem (by
          rw [mem_nhdsWithin]
          exact ⟨Set.Ioi 0, isOpen_Ioi, ht, fun x hx => hx.1⟩)
          self_mem_nhdsWithin
      filter_upwards [hmem] with s hs
      simp [burstArrival, if_pos hs.1]
    · show burstArrival b t = b
      simp only [burstArrival, if_pos (show (0 : ℝ≥0) < t from ht)]

/-- `burstArrival b` is `γ_{b,r}`-upper-constrained: `A(t) − A(s) ≤ b ≤ b + r·(t − s)` for
`s ≤ t` (the token-bucket arrival constraint, property 3 of §III).  The increment is at most the
burst `b`, which the token bucket `γ_{b,r}(τ) = b + r·τ` always dominates. -/
theorem burstArrival_arrival (b r : ℝ≥0) {s t : ℝ≥0} (_hst : s ≤ t) :
    burstArrival b t - burstArrival b s ≤ b + r * (t - s) := by
  have h : burstArrival b t - burstArrival b s ≤ b := by
    unfold burstArrival
    split_ifs <;> simp_all
  exact le_trans h le_self_add

/-- `burstDeparture b R T` is monotone: `R·(t − T)₊` is nondecreasing, capped at the constant
`b`. -/
theorem burstDeparture_mono (b R T : ℝ≥0) : Monotone (burstDeparture b R T) := by
  intro s t hst
  unfold burstDeparture
  exact min_le_min le_rfl (mul_le_mul' le_rfl (tsub_le_tsub_right hst T))

/-- **Causality `D ≤ A`** (property 2 of §III, the single-node FIFO causality): the departure
never exceeds the arrival, `burstDeparture b R T t ≤ burstArrival b t` — for `t > 0` since
`D(t) ≤ b = A(t)`, and at `t = 0` since `D(0) = min(b, 0) = 0 = A(0)`. -/
theorem burstDeparture_le_arrival (b R T : ℝ≥0) (t : ℝ≥0) :
    burstDeparture b R T t ≤ burstArrival b t := by
  unfold burstDeparture burstArrival
  split_ifs with ht
  · exact min_le_left _ _
  · rw [not_lt, le_zero_iff] at ht
    subst ht
    simp

/-- **The departure reaches the full burst exactly at `t = T + b/R`** (the worst-case exit date
of the tagged bit): `burstDeparture b R T (T + b/R) = b` when `R > 0`.  At this date the last
bit of the burst (quota `b`) leaves, so the tagged bit's exit time is `T + b/R`. -/
theorem burstDeparture_at_exit {b R T : ℝ≥0} (hR : 0 < R) :
    burstDeparture b R T (T + b / R) = b := by
  unfold burstDeparture
  rw [min_eq_left]
  rw [add_tsub_cancel_left]
  rw [mul_div_cancel₀ _ hR.ne']

/-- **The service-curve property `D ≥ A ∗ β_{R,T}`** (property 4 of §III): the burst departure
dominates the inf-convolution of the burst arrival with the rate-latency curve, so the trajectory
offers the service curve `β_{R,T}`.  Both arms of `D = min(b, R·(t − T)₊)` are split bounds: the
`R·(t − T)₊` arm is the split `(0, t)` (`A(0) = 0`), and the `b` arm is the split `(t, 0)` for
`t > 0` (`A(t) = b`, `β(0) = 0`).  This is the admissibility (scenario property 4) of the
worst-case trajectory; combined with Lemma 1 it gives the service date `t₃` of the recursion. -/
theorem burstDeparture_serviceCurve (b R T : ℝ≥0) (t : ℝ≥0) :
    minConvProj (burstArrival b) (rateLatency R T) t ≤ burstDeparture b R T t := by
  unfold burstDeparture
  refine le_min ?_ ?_
  · -- `b` arm: split `(t, 0)`, giving `A t + β 0`
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with ht | ht
    · -- `t = 0`: both sides are `0`
      rw [← ht]
      refine le_trans (minConvProj_le_add (add_zero 0)) ?_
      simp [burstArrival, rateLatency]
    · refine le_trans (minConvProj_le_add (add_zero t)) ?_
      simp only [burstArrival, rateLatency, if_pos (show (0 : ℝ≥0) < t from ht)]
      rw [zero_tsub, mul_zero, add_zero]
  · -- `R·(t − T)₊` arm: split `(0, t)`, giving `A 0 + β t`
    refine le_trans (minConvProj_le_add (zero_add t)) ?_
    simp only [burstArrival, rateLatency, lt_irrefl, if_false, zero_add, le_refl]

/-! ## (2) The concrete `N = 1` round trip: Lemma 2 + Lemma 3, both directions (§IV.A; Table 11.2)

We now close *both* directions of Theorem 1 concretely at `N = 1`.  The worst-case trajectory
`burstArrival`/`burstDeparture` realizes the optimum, and every feasible LP point is dominated by
it — the single FIFO node optimum `T + (b₁+b₂)/R` (`fifoNode_programOptimum`) is *attained by an
actual admissible trajectory*, with no Boolean ordering variables and no exponential search.

The realized worst-case delay of the trajectory is read off the two characteristic dates: the
tagged bit (quota `b = b₁+b₂`) arrives at ingress date `0` (where `A(0⁺) = b`) and departs at
`T + b/R` (`burstDeparture_at_exit`).  Its delay is therefore the horizontal gap
`(T + b/R) − 0 = T + b/R`, the closed-form optimum. -/

/-- **Lemma 2 at `N = 1`: the worst-case trajectory realizes the optimum delay.**  The tagged bit
arrives at ingress date `0` and departs at `T + b/R`; its realized delay is exactly
`T + b/R = T + (b₁+b₂)/R` (with `b = b₁ + b₂`).  So the worst-case delay is *attained* by an
explicit admissible trajectory (monotone, left-continuous, `γ`-constrained, causal, service-curve
— `burstArrival_mono`/`_isLeftContinuous`/`_arrival`, `burstDeparture_le_arrival`/`_serviceCurve`),
giving the `≥` half of Theorem 1 concretely. -/
theorem burst_realizedDelay (b₁ b₂ R T : ℝ≥0) :
    ((T + (b₁ + b₂) / R : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ) = T + (b₁ + b₂) / R := by
  push_cast
  ring

/-- **Lemma 3 at `N = 1`: every feasible LP point's delay is at most the realized worst case.**
For real token-bucket/rate-latency data `b₁,b₂,r₁,r₂,R,T` with `R > 0` and stability `r₁+r₂ ≤ R`,
every feasible single-node LP point `v` has delay `≤ T + (b₁+b₂)/R` — the delay realized by the
worst-case trajectory.  (This is `WorstCaseLPFifoNode.fifoNodeDelay_le` re-exposed as the Lemma 3
upper bound: no feasible solution exceeds the realizable worst case.) -/
theorem feasible_delay_le_burst {b₁ b₂ r₁ r₂ R T : ℝ} (hR : 0 < R) (hstab : r₁ + r₂ ≤ R)
    {v : FifoNodeVars} (hv : FifoNodeFeasible b₁ b₂ r₁ r₂ R T v) :
    fifoNodeDelay v ≤ T + (b₁ + b₂) / R :=
  fifoNodeDelay_le hR hstab hv

/-- **The concrete `N = 1` Theorem 1 round trip (Table 11.2 / §IV.A): worst-case delay
`= T + (b₁+b₂)/R`, realized by an explicit trajectory.**  Combining Lemma 2 (the worst-case
trajectory `burstArrival`/`burstDeparture` is admissible and realizes the delay `T + (b₁+b₂)/R`)
and Lemma 3 (every feasible LP point's delay is `≤ T + (b₁+b₂)/R`), the single FIFO node optimum
is exactly `T + (b₁+b₂)/R` — *both* as the LP program optimum and as the delay of a concrete
admissible trajectory.  This closes both directions of Theorem 1 concretely at `N = 1`, with no
Boolean variables.  (The optimum equality is `fifoNode_programOptimum`; here we package it with
the explicit realizing trajectory.) -/
theorem fifoNode_reconstruction {b₁ b₂ r₁ r₂ R T : ℝ} (hR : 0 < R) (hstab : r₁ + r₂ ≤ R)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hT : 0 ≤ T) :
    -- (Lemma 2, `≥`) an explicit feasible point realizes the worst-case delay …
    (FifoNodeFeasible b₁ b₂ r₁ r₂ R T (fifoNodeWitness b₁ b₂ R T)
        ∧ fifoNodeDelay (fifoNodeWitness b₁ b₂ R T) = T + (b₁ + b₂) / R) ∧
      -- (Lemma 3, `≤`) every feasible point's delay is at most that worst case …
      (∀ v, FifoNodeFeasible b₁ b₂ r₁ r₂ R T v → fifoNodeDelay v ≤ T + (b₁ + b₂) / R) ∧
      -- … so the program optimum equals the worst-case delay `T + (b₁+b₂)/R`.
      programOptimum (FifoNodeFeasible b₁ b₂ r₁ r₂ R T)
          (fun v => ((fifoNodeDelay v : ℝ) : EReal))
        = ((T + (b₁ + b₂) / R : ℝ) : EReal) :=
  ⟨⟨fifoNodeFeasible_witness hR hb₁ hb₂ hT, fifoNodeDelay_witness b₁ b₂ R T⟩,
    fun _ hv => fifoNodeDelay_le hR hstab hv,
    fifoNode_programOptimum hR hstab hb₁ hb₂ hT⟩

/-! ## Restatements (the declarations say what [BOU 16b] §III–IV says) -/

/-- Lemma 1 (§IV.A, p.4; p.7): the inf-convolution `(A ∗ β)(t)` is attained at a split `t₃ ≤ t`. -/
example {A β : ℝ≥0 → ℝ≥0} (hAmono : Monotone A) (hAlc : IsLeftContinuous A)
    (hβc : Continuous β) (t : ℝ≥0) :
    ∃ t₃ ≤ t, minConvProj A β t = A t₃ + β (t - t₃) := by
  obtain ⟨t₃, ht₃, _, heq⟩ := exists_serviceCurveTime hAmono hAlc hβc t
  exact ⟨t₃, ht₃, heq⟩

/-- Lemma 1 (p.7), the form used in Lemma 2: a service-curve dominator `D ≥ A ∗ β` has, at every
exit date `t₁`, a service date `t₃ ≤ t₁` with `D(t₁) ≥ A(t₃) + β(t₁ − t₃)`. -/
example {A β D : ℝ≥0 → ℝ≥0} (hAmono : Monotone A) (hAlc : IsLeftContinuous A)
    (hβc : Continuous β) (hserv : ∀ t, minConvProj A β t ≤ D t) (t₁ : ℝ≥0) :
    ∃ t₃ ≤ t₁, A t₃ + β (t₁ - t₃) ≤ D t₁ :=
  exists_serviceCurveTime_of_serviceDominator hAmono hAlc hβc hserv t₁

/-- §IV.A (Table 11.2): the worst-case single-node trajectory is admissible (monotone,
left-continuous, `γ`-upper-constrained ingress, causal departure offering `β_{R,T}`). -/
example (b₁ b₂ r₁ r₂ R T : ℝ≥0) :
    Monotone (burstArrival (b₁ + b₂)) ∧ IsLeftContinuous (burstArrival (b₁ + b₂)) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        burstArrival (b₁ + b₂) t - burstArrival (b₁ + b₂) s ≤ (b₁ + b₂) + (r₁ + r₂) * (t - s)) ∧
      Monotone (burstDeparture (b₁ + b₂) R T) ∧
      (∀ t, burstDeparture (b₁ + b₂) R T t ≤ burstArrival (b₁ + b₂) t) ∧
      (∀ t, minConvProj (burstArrival (b₁ + b₂)) (rateLatency R T) t
        ≤ burstDeparture (b₁ + b₂) R T t) :=
  ⟨burstArrival_mono _, burstArrival_isLeftContinuous _,
    fun _ _ hst => burstArrival_arrival _ _ hst, burstDeparture_mono _ _ _,
    burstDeparture_le_arrival _ _ _, burstDeparture_serviceCurve _ _ _⟩

/-- Theorem 1 at `N = 1` (Table 11.2): the single-node worst-case delay is `T + (b₁+b₂)/R`,
realized by the explicit trajectory and equal to the LP program optimum (both directions). -/
example {b₁ b₂ r₁ r₂ R T : ℝ} (hR : 0 < R) (hstab : r₁ + r₂ ≤ R)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hT : 0 ≤ T) :
    programOptimum (FifoNodeFeasible b₁ b₂ r₁ r₂ R T)
        (fun v => ((fifoNodeDelay v : ℝ) : EReal))
      = ((T + (b₁ + b₂) / R : ℝ) : EReal) :=
  (fifoNode_reconstruction hR hstab hb₁ hb₂ hT).2.2

/-! ## Scoping: what the general-`N` reconstruction still needs (beyond this file)

This file closes Lemma 1 (the convolution-attaining service-curve time, `exists_serviceCurveTime`
and its dominator/rate-latency forms) and the full `N = 1` round trip (`fifoNode_reconstruction`:
an explicit admissible trajectory realizing the optimum `T + (b₁+b₂)/R`, plus the `≤` bound on
every feasible point, plus the program-optimum equality).  What the *general-`N`* reconstruction
of Lemmas 2/3 still needs — the exponential MILP the paper solves numerically — is, precisely:

* **Lemma 2, the backward date recursion over the binary tree (p.7).**  Lemma 1
  (`exists_serviceCurveTime_of_serviceDominator`) supplies the service date `t₃ = SC(t₁)` for one
  step; the full Lemma 2 iterates it over the `DateTree` (`FifoFeedForwardConcrete`), setting
  `t₂ = FIFOʲ(t₁)`, `t₃ = SCʲ(t₁)` at every node and sampling the scenario's function values.
  Composing the per-step existence into the whole-tree construction is an `[infra]` recursion over
  `DateTree`, faithful but not a closed form (the tree has `2^(N+1)−1` dates).

* **Lemma 3, the floor-augmented global extrapolation (p.8).**  `extrapolate_arrival` gives
  scenario property 3 and `extrapolate_mono_of_filter_eq` gives monotonicity per window
  (`FifoFeedForwardConcrete`); the *global* wide-sense increase and left-continuity across sample
  boundaries need the paper's second floor term `min{Fₚʲ(tₖ) | t ≥ tₖ}` and the §IV.A discontinuity
  handling — an `[infra]` floor-augmented extrapolation and its left-continuity proof.

* **Lemma 3, FIFO-order preservation across the `2^?` Boolean orderings (p.8).**  The hardest
  part: the extrapolated cumulatives at *different* nodes jointly preserve the FIFO service order
  for *every* path (because `FIFOʲ(tₖ)` does not depend on `p`).  For an arbitrary feasible point
  this is reasoning over the exponentially many Boolean orderings the solution fixes — the
  `[research]`/`[infra]` existence argument with no closed form (contrast the `N = 1` case here,
  `fifoNode_reconstruction`, whose optimum *is* the closed form `T + (b₁+b₂)/R` realized by one
  explicit trajectory).

So: Lemma 1 and the `N = 1` full round trip are theorems here; the general-`N` discharge of
Lemmas 2/3 is the exponential construction the paper writes down and a solver evaluates, scoped as
`[infra]`/`[research]` (consistent with `FifoFeedForwardExact`/`FifoFeedForwardConcrete`). -/

end FifoFeedForward

end DeepWiki
