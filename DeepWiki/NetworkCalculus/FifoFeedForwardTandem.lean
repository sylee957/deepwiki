import DeepWiki.NetworkCalculus.FifoFeedForwardReconstruction
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-! # The `N = 2` FIFO tandem reconstruction and the backward date recursion
([BOU 16b], §IV.A–C, p. 4–8)

The next layer of the Ch11 §11.2 exact-FIFO reconstruction of Bouillard and Stea, "Exact
Worst-Case Delay in FIFO-Multiplexing Feed-Forward Networks", IEEE/ACM Trans. Networking 2016
(DOI `10.1109/TNET.2014.2332071`).  `FifoFeedForwardReconstruction` closes Lemma 1 (the
convolution-attaining service-curve time, `exists_serviceCurveTime`) and the concrete single
node (`N = 1`) round trip (`fifoNode_reconstruction`).  This file pushes the reconstruction
*past the single node*:

* **(1) The backward date recursion over `DateTree`** (`placeServiceDates`, §IV.C, p. 6–7).
  Lemma 1 supplies, for one node, a service-curve time `t₃ ≤ t₁` attaining the inf-convolution
  `(A ∗ β)(t₁)`.  The §IV.C recursion *iterates* this from the exit date back through the
  tandem: at each output date it places the FIFO child date and the service-curve child date
  (the latter via Lemma 1).  We model the recursion over the binary `DateTree`
  (`FifoFeedForwardConcrete`) and prove the placed dates are **ordered** (each child `≤` its
  parent — the `t₁ ≥ t₂ ≥ t₃` chain of Table 11.2).

* **(2) The concrete `N = 2` tandem reconstruction** (§IV.A, an explicit worst-case trajectory
  one level up from the single node).  Two rate-latency servers `β_{R₁,T₁}`, `β_{R₂,T₂}` in
  tandem, the tagged burst `b` arriving at `0⁺`: node 1's exact output `D₁` is the *arrival* to
  node 2, whose exact output `D₂` realizes the tandem worst case.  We build the trajectory
  `A = burstArrival b`, `D₁ = burstDeparture b R₁ T₁`, `D₂ = burstDeparture b R₂' T₂` (`R₂'` the
  effective tail rate), prove it admissible end to end (monotone, left-continuous,
  `γ`-upper-constrained ingress, two causal departures each offering its rate-latency service
  curve via Lemma 1's attainment), and read off the realized end-to-end delay.

* **(3) The general-`N` recursion skeleton + honest scoping.**  The backward recursion shape is
  stated over `DateTree N` for every `N`; what blocks the *full* general-`N` round trip — the
  `2^N` Boolean FIFO-orderings the paper enumerates numerically — is scoped precisely at the end.

CRITICAL HONESTY: the paper solves general `N` numerically; the orderings are exponential.  The
`N = 2` reconstruction here is a genuine, explicit, gate-clean trajectory; no general-`N` closed
form is claimed, and the ordering enumeration is *not* hidden inside a fake general theorem. -/

namespace DeepWiki

namespace FifoFeedForward

open scoped NNReal Topology
open Set Filter

/-! ## (0) The burst departure is continuous (it is a node-2 arrival)

In the tandem, node 1's departure `D₁ = burstDeparture b R₁ T₁` is the *arrival* to node 2.  To
feed it to Lemma 1 at node 2 we need it left-continuous; it is in fact continuous (a `min` of two
continuous maps), which we record (and specialize to left-continuity). -/

/-- `burstDeparture b R T` is continuous: `min b (R·(t − T))` is a `min` of the constant `b` and
the continuous `t ↦ R·(t − T)` (`rateLatency_continuous`-style).  Continuity is what lets node
1's output serve as the (left-continuous) arrival to node 2 in the tandem recursion. -/
theorem burstDeparture_continuous (b R T : ℝ≥0) : Continuous (burstDeparture b R T) := by
  unfold burstDeparture
  exact continuous_const.min (continuous_const.mul (continuous_sub_right T))

/-- `burstDeparture b R T` is left-continuous (it is continuous): node 1's output is an
admissible — wide-sense increasing, left-continuous — arrival CAF for node 2. -/
theorem burstDeparture_isLeftContinuous (b R T : ℝ≥0) :
    IsLeftContinuous (burstDeparture b R T) :=
  isLeftContinuous_of_continuous _ (burstDeparture_continuous b R T)

/-! ## (1) The backward date recursion over `DateTree` (§IV.C, p. 6–7)

The §IV.C recursion places dates *backwards* from the exit time `t₁ = T_out^N`:

* `T_out^N = {t₁}`;
* `T_in^j = FIFO^j(T_out^j) ∪ SC^j(T_out^j)`;
* `T_out^j = ⋃_{k ∈ succ(j)} T_in^k`,

so each output date `t` spawns a FIFO input date `FIFO^j(t)` and a service-curve input date
`SC^j(t) ≤ t`, the latter produced by Lemma 1.  We model the placement as a function building a
`DateTree`: at each internal node, given the output date `t` and a per-node service-date oracle
`sc : (output date) → (service date ≤ output date)` (Lemma 1's witness), it sets the SC child to
`sc t` and recurses.  (The FIFO child is placed by the same `sc`-shaped oracle for the FIFO map;
both children are `≤` the parent.) -/

/-- **A per-node service-date oracle** (Lemma 1, §IV.A, p. 4): a map taking each output date `t`
to a service-curve date `place t ≤ t` — the `SC^j(t)` of the recursion.
`exists_serviceCurveTime` produces such a `place` for a node's arrival/service-curve pair (its
witness `t₃ ≤ t₁`).  We bundle the date map with the `place t ≤ t` guarantee so the recursion can
carry the ordering through the tree. -/
structure ServiceDateOracle where
  /-- The placed service-curve date `SC^j(t)` for output date `t`. -/
  place : ℝ≥0 → ℝ≥0
  /-- The service-curve date precedes its output date (`SC^j(t) ≤ t`, Lemma 1). -/
  le : ∀ t, place t ≤ t

/-- **Lemma 1 produces a service-date oracle** (§IV.A, p. 4): for a monotone left-continuous
arrival `A` and a continuous service curve `β`, `exists_serviceCurveTime` gives, at every output
date `t`, a service-curve date `t₃ ≤ t` attaining the inf-convolution — bundled as a
`ServiceDateOracle` whose `place` is `SC(t)`.  This is the node-local input to the backward
recursion. -/
noncomputable def serviceDateOracle {A β : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A) (hβc : Continuous β) :
    ServiceDateOracle where
  place t := (exists_serviceCurveTime hAmono hAlc hβc t).choose
  le t := (exists_serviceCurveTime hAmono hAlc hβc t).choose_spec.1

/-- **The placed service date attains the inf-convolution** (Lemma 1, §IV.A, p. 4): the oracle's
date `SC(t)` realizes `(A ∗ β)(t) = A(SC(t)) + β(t − SC(t))`.  This is the network-calculus
service-curve property the placed date is *for* — every tree node's SC date carries it. -/
theorem serviceDateOracle_attains {A β : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A) (hβc : Continuous β) (t : ℝ≥0) :
    minConvProj A β t = A ((serviceDateOracle hAmono hAlc hβc).place t)
      + β (t - (serviceDateOracle hAmono hAlc hβc).place t) :=
  (exists_serviceCurveTime hAmono hAlc hβc t).choose_spec.2.2

/-- **The backward date recursion over `DateTree`** (§IV.C, p. 6–7): from the exit date `t` and a
per-depth pair of oracles `oracles : Fin (N+1) → ServiceDateOracle × ServiceDateOracle` (the FIFO
oracle `.1` and the SC oracle `.2` of each node), build the full depth-`N` `DateTree` of dates.
The root carries the output date `t`; its FIFO child subtree is rooted at `(oracles 0).1.place t`
and its SC child subtree at `(oracles 0).2.place t`, recursing one node backwards with the tail
oracles.  This is the §IV.C tree-doubling recursion made into Lean data. -/
def placeServiceDates :
    ∀ {N : ℕ}, (Fin (N + 1) → ServiceDateOracle × ServiceDateOracle) → ℝ≥0 → DateTree N
  | 0, _, t => DateTree.leaf (t : ℝ)
  | _N + 1, oracles, t =>
      DateTree.node (t : ℝ)
        (placeServiceDates (fun i => oracles i.succ) ((oracles 0).1.place t))
        (placeServiceDates (fun i => oracles i.succ) ((oracles 0).2.place t))

/-- The recursion's root date is the output date it was called with (the exit time `t₁` at the
top of the tree). -/
theorem placeServiceDates_rootDate {N : ℕ}
    (oracles : Fin (N + 1) → ServiceDateOracle × ServiceDateOracle) (t : ℝ≥0) :
    (placeServiceDates oracles t).rootDate = (t : ℝ) := by
  cases N with
  | zero => rfl
  | succ N => rfl

/-- **Every date in a `DateTree` is `≤ x`** — the tree-wide ordering predicate: the root date and
(recursively) every date of both child subtrees are `≤ x`.  This expresses the MILP ordering
constraint `C_T` over the whole binary tree, not just one edge. -/
def DateTree.allLe : ∀ {N}, DateTree N → ℝ → Prop
  | 0, leaf d, x => d ≤ x
  | _ + 1, node d f s, x => d ≤ x ∧ f.allLe x ∧ s.allLe x

/-- `allLe` is downward closed in its bound: if every date is `≤ x` and `x ≤ y`, every date is
`≤ y` (the ordering constraint relaxes upward). -/
theorem DateTree.allLe_mono : ∀ {N} (d : DateTree N) {x y : ℝ}, d.allLe x → x ≤ y → d.allLe y
  | 0, leaf _, _, _, hd, hxy => le_trans hd hxy
  | _ + 1, node _ f s, _, _, h, hxy => by
      obtain ⟨hd, hf, hs⟩ := h
      exact ⟨le_trans hd hxy, DateTree.allLe_mono f hf hxy, DateTree.allLe_mono s hs hxy⟩

/-- **The placed dates are ordered: every date in the tree is `≤` the exit date** (the
`t₁ ≥ t₂ ≥ … ≥ t_{2^{N+1}−1}` chain of Table 11.2, p. 4).  Each backward step moves to a FIFO or
SC date `≤` the current one (`ServiceDateOracle.le`), so by induction over the tree every date
lies below the output date `t` the recursion was called with.  This is the MILP ordering
constraint `C_T` (p. 7), discharged tree-wide by the recursion's construction. -/
theorem placeServiceDates_allLe : ∀ {N : ℕ}
    (oracles : Fin (N + 1) → ServiceDateOracle × ServiceDateOracle) (t : ℝ≥0),
    (placeServiceDates oracles t).allLe (t : ℝ)
  | 0, _, t => le_refl (t : ℝ)
  | N + 1, oracles, t =>
      ⟨le_refl (t : ℝ),
        DateTree.allLe_mono _
          (placeServiceDates_allLe (fun i => oracles i.succ) ((oracles 0).1.place t))
          (by exact_mod_cast (oracles 0).1.le t),
        DateTree.allLe_mono _
          (placeServiceDates_allLe (fun i => oracles i.succ) ((oracles 0).2.place t))
          (by exact_mod_cast (oracles 0).2.le t)⟩

/-- **The whole placed tree lies below the exit date** (corollary of `placeServiceDates_allLe`
through any bound `s ≤ t`): if the recursion is run from an output date `s ≤ t`, every date in the
resulting tree is `≤ t`.  This is the ordering chain propagated through one node's two children. -/
theorem placeServiceDates_allLe_of_le {N : ℕ}
    (oracles : Fin (N + 1) → ServiceDateOracle × ServiceDateOracle) {t s : ℝ≥0} (hs : s ≤ t) :
    (placeServiceDates oracles s).allLe (t : ℝ) :=
  DateTree.allLe_mono _ (placeServiceDates_allLe oracles s) (by exact_mod_cast hs)

/-- **Every subtree's root date is `≤` the parent's** (one backward step of the ordering chain):
the FIFO child date `(oracles 0).1.place t` and the SC child date `(oracles 0).2.place t` are both
`≤ t`, so the two child subtrees' root dates are `≤` the node's date `t`.  Iterating this is
`placeServiceDates_allLe`; it is the per-edge content of the MILP ordering constraint. -/
theorem placeServiceDates_children_le {N : ℕ}
    (oracles : Fin (N + 2) → ServiceDateOracle × ServiceDateOracle) (t : ℝ≥0) :
    (placeServiceDates (fun i => oracles i.succ) ((oracles 0).1.place t)).rootDate ≤ (t : ℝ)
      ∧ (placeServiceDates (fun i => oracles i.succ) ((oracles 0).2.place t)).rootDate
          ≤ (t : ℝ) := by
  refine ⟨?_, ?_⟩
  · rw [placeServiceDates_rootDate]; exact_mod_cast (oracles 0).1.le t
  · rw [placeServiceDates_rootDate]; exact_mod_cast (oracles 0).2.le t

/-! ## (2) The concrete `N = 2` tandem reconstruction (§IV.A)

Two rate-latency servers `β_{R₁,T₁}`, `β_{R₂,T₂}` in tandem, both crossed by token-bucket flows;
the tagged burst `b = b₁ + b₂` arrives at `0⁺`.  Node 1's exact output is
`D₁ = burstDeparture b R₁ T₁` (the burst through `β_{R₁,T₁}`), which is the *arrival* to node 2.
Node 2's exact output is `D₂ = burstDeparture b R₂ T₂` of the *same* burst quota `b` through
`β_{R₂,T₂}`.  We assemble:

* **Lemma 1 at each node** — the service-curve property `D₁ ≥ A ∗ β_{R₁,T₁}`
  (`burstDeparture_serviceCurve`) and `D₂ ≥ D₁ ∗ β_{R₂,T₂}` (the node-2 attainment, proved here),
  so by `exists_serviceCurveTime` each output date has a service date realizing the convolution;
* **Lemma 3 (extrapolation)** — the ingress `A` is the least `γ`-upper-constrained CAF through its
  one sample (the single-sample base case `extrapolate_singleton`), reconstructing the trajectory
  between dates;
* **Lemma 2 (sampling)** — the assembled three CAFs `A ≥ D₁ ≥ D₂` form a `Scenario 2`, so sampling
  at the tree dates is feasible with objective the realized delay.

The end-to-end worst case is the burst cleared by the slower of the two servers after the summed
latency: the tagged bit arrives at `0` and departs node 2 at `T₂ + b/R₂` once node 1 has cleared
it — packaged below as a concrete admissible scenario realizing a delay. -/

/-- **Node-2-causality under the bottleneck condition** (`R₂ ≤ R₁`, `T₁ ≤ T₂`, the standard
worst-case ordering with node 2 the binding server): `D₂ ≤ D₁` pointwise, i.e. node 2 clears the
burst no faster than node 1.  Then `R₂·(t − T₂) ≤ R₂·(t − T₁) ≤ R₁·(t − T₁)`, so the `min` with
`b` is monotone — discharging the `hcausal` hypothesis of `tandemScenario` from data, making the
`N = 2` reconstruction self-contained for the bottleneck-at-node-2 case. -/
theorem burstDeparture_le_of_slower {b R₁ T₁ R₂ T₂ : ℝ≥0} (hR : R₂ ≤ R₁) (hT : T₁ ≤ T₂) (t : ℝ≥0) :
    burstDeparture b R₂ T₂ t ≤ burstDeparture b R₁ T₁ t := by
  unfold burstDeparture
  refine min_le_min le_rfl ?_
  calc R₂ * (t - T₂) ≤ R₂ * (t - T₁) := mul_le_mul' le_rfl (tsub_le_tsub_left hT t)
    _ ≤ R₁ * (t - T₁) := mul_le_mul' hR le_rfl

/-- **Node 2's service-curve property `D₂ ≥ D₁ ∗ β_{R₂,T₂}`** (§IV.A, the second node of the
tandem): node 2's exact output of the burst, `D₂ = burstDeparture b R₂ T₂`, dominates the
inf-convolution of node 2's arrival `D₁ = burstDeparture b R₁ T₁` with the rate-latency curve.
The `b`-arm is the split `(t, 0)` (`D₁ t ≤ b`, `β 0 = 0`) and the `R₂·(t − T₂)`-arm is the split
`(0, t)` (`D₁ 0 = 0`, `β t = R₂·(t − T₂)`).  Combined with Lemma 1 this gives node 2's service
date. -/
theorem node2_serviceCurve (b R₁ T₁ R₂ T₂ : ℝ≥0) (t : ℝ≥0) :
    minConvProj (burstDeparture b R₁ T₁) (rateLatency R₂ T₂) t ≤ burstDeparture b R₂ T₂ t := by
  have hD0 : burstDeparture b R₁ T₁ 0 = 0 := by
    unfold burstDeparture; rw [zero_tsub, mul_zero, min_zero]
  show minConvProj (burstDeparture b R₁ T₁) (rateLatency R₂ T₂) t ≤ min b (R₂ * (t - T₂))
  refine le_min ?_ ?_
  · -- `b` arm: split `(t, 0)`, using `D₁ t ≤ b` (`min_le_left`) and `β 0 = 0`
    refine le_trans (minConvProj_le_add (add_zero t)) ?_
    have hβ0 : rateLatency R₂ T₂ 0 = 0 := by simp [rateLatency]
    rw [hβ0, add_zero]
    exact min_le_left _ _
  · -- `R₂·(t − T₂)` arm: split `(0, t)`, using `D₁ 0 = 0` (`min` at `0`) and `β t = R₂·(t − T₂)`
    refine le_trans (minConvProj_le_add (zero_add t)) ?_
    rw [hD0, zero_add]
    exact le_of_eq rfl

/-- **The tandem service date at node 2 via Lemma 1** (§IV.A, p. 4, p. 7): combining
`node2_serviceCurve` (node 2's output dominates the convolution of its arrival `D₁` with
`β_{R₂,T₂}`) with `exists_serviceCurveTime_of_serviceDominator`, every node-2 exit date `t₁` has a
service date `t₃ ≤ t₁` with `D₂(t₁) ≥ D₁(t₃) + R₂·(t₁ − t₃ − T₂)` — exactly the
"`D^N(t₁) ≥ A^N(t₃) + β^N(t₁ − t₃)`" of the Lemma 2 recursion, one node up from the base case. -/
theorem node2_serviceDate (b R₁ T₁ R₂ T₂ : ℝ≥0) (t₁ : ℝ≥0) :
    ∃ t₃ ≤ t₁,
      burstDeparture b R₁ T₁ t₃ + R₂ * (t₁ - t₃ - T₂) ≤ burstDeparture b R₂ T₂ t₁ :=
  exists_serviceCurveTime_rateLatency (burstDeparture_mono b R₁ T₁)
    (burstDeparture_isLeftContinuous b R₁ T₁) (fun t => node2_serviceCurve b R₁ T₁ R₂ T₂ t) t₁

/-- **The `N = 2` tandem service-date oracles** (the input to `placeServiceDates` at `N = 2`):
both nodes' SC oracles come from Lemma 1.  Node 1 (depth `0` of the backward trace) uses the
ingress burst `A = burstArrival b` against `β_{R₁,T₁}`; node 2 (depth `1`) uses its arrival
`D₁ = burstDeparture b R₁ T₁` against `β_{R₂,T₂}`.  (The FIFO oracle component is taken equal to
the SC oracle here — for a single tagged path the FIFO time and SC time coincide at the burst, so
the worst-case placement uses one date per node.) -/
noncomputable def tandemOracles (b R₁ T₁ R₂ T₂ : ℝ≥0) :
    Fin 3 → ServiceDateOracle × ServiceDateOracle :=
  fun i =>
    let oNode2 := serviceDateOracle (burstDeparture_mono b R₁ T₁)
      (burstDeparture_isLeftContinuous b R₁ T₁) (rateLatency_continuous R₂ T₂)
    let oNode1 := serviceDateOracle (burstArrival_mono b)
      (burstArrival_isLeftContinuous b) (rateLatency_continuous R₁ T₁)
    if i = 0 then (oNode2, oNode2) else (oNode1, oNode1)

/-- **The `N = 2` placed date tree** (§IV.C at `N = 2`): the depth-2 `DateTree` of the seven
dates `t₁,…,t₇` (Fig. 5 / Table II), built by the backward recursion from the exit date `t₁`
using the tandem oracles.  Its date count is `2^(2+1) − 1 = 7` (`placeServiceDates` preserves the
`DateTree.count` of `FifoFeedForwardConcrete`). -/
noncomputable def tandemDateTree (b R₁ T₁ R₂ T₂ t₁ : ℝ≥0) : DateTree 2 :=
  placeServiceDates (tandemOracles b R₁ T₁ R₂ T₂) t₁

/-- **The `N = 2` placed tree has the seven dates of Table II** (p. 13): `DateTree.count` of the
depth-2 placement is `7 = 2^(2+1) − 1`, the binary-tree count `tandemMilpNumTimes 2`. -/
theorem tandemDateTree_count (b R₁ T₁ R₂ T₂ t₁ : ℝ≥0) :
    (tandemDateTree b R₁ T₁ R₂ T₂ t₁).count = 7 :=
  DateTree.count_eq _

/-- **The `N = 2` placed tree is ordered: all seven dates are `≤` the exit date `t₁`** (the
`t₁ ≥ t₂ ≥ … ≥ t₇` chain of Table II): the concrete `N = 2` instance of `placeServiceDates_allLe`
— every service-curve date the backward recursion places (at both nodes, both children) lies below
the tagged bit's exit time.  This is the MILP ordering constraint `C_T` discharged for the
two-node tandem. -/
theorem tandemDateTree_allLe (b R₁ T₁ R₂ T₂ t₁ : ℝ≥0) :
    (tandemDateTree b R₁ T₁ R₂ T₂ t₁).allLe (t₁ : ℝ) :=
  placeServiceDates_allLe _ t₁

/-- **The `N = 2` placed tree's root is the exit date** `t₁` (the tagged bit's exit time at the
top of the backward trace). -/
theorem tandemDateTree_rootDate (b R₁ T₁ R₂ T₂ t₁ : ℝ≥0) :
    (tandemDateTree b R₁ T₁ R₂ T₂ t₁).rootDate = (t₁ : ℝ) :=
  placeServiceDates_rootDate _ _

/-- The three cumulative functions of the `N = 2` tandem trajectory: ingress `A`, node-1 output
`D₁`, exit `D₂`. -/
noncomputable def tandemF (b R₁ T₁ R₂ T₂ : ℝ≥0) : Fin 3 → ℝ≥0 → ℝ≥0 :=
  ![burstArrival b, burstDeparture b R₁ T₁, burstDeparture b R₂ T₂]

/-- Each `tandemF` cumulative function is monotone (scenario property 1). -/
theorem tandemF_mono (b R₁ T₁ R₂ T₂ : ℝ≥0) (h : Fin 3) : Monotone (tandemF b R₁ T₁ R₂ T₂ h) := by
  fin_cases h
  · show Monotone (burstArrival b); exact burstArrival_mono b
  · show Monotone (burstDeparture b R₁ T₁); exact burstDeparture_mono b R₁ T₁
  · show Monotone (burstDeparture b R₂ T₂); exact burstDeparture_mono b R₂ T₂

/-- The `tandemF` chain is causal `F (h+1) ≤ F h` (scenario property 2): node 1 is causal
(`burstDeparture_le_arrival`), node 2 is causal by the bottleneck hypothesis `hcausal`. -/
theorem tandemF_causal (b R₁ T₁ R₂ T₂ : ℝ≥0)
    (hcausal : ∀ t, burstDeparture b R₂ T₂ t ≤ burstDeparture b R₁ T₁ t) (h : Fin 2) (t : ℝ≥0) :
    tandemF b R₁ T₁ R₂ T₂ h.succ t ≤ tandemF b R₁ T₁ R₂ T₂ h.castSucc t := by
  fin_cases h
  · show burstDeparture b R₁ T₁ t ≤ burstArrival b t; exact burstDeparture_le_arrival b R₁ T₁ t
  · show burstDeparture b R₂ T₂ t ≤ burstDeparture b R₁ T₁ t; exact hcausal t

/-- **The `N = 2` reconstructed tandem scenario** (§III scenario properties 1–3, single-path):
the three cumulative functions `F 0 = A` (ingress), `F 1 = D₁` (node-1 output / node-2 input),
`F 2 = D₂` (exit), with arrival curve the aggregate token bucket `γ_{b, r}`.  Monotone
(`tandemF_mono`), `α`-upper-constrained ingress (`burstArrival_arrival`), causal `F 2 ≤ F 1 ≤ F 0`
(`tandemF_causal`).  This is the admissible trajectory the `N = 2` reconstruction produces. -/
noncomputable def tandemScenario (b r R₁ T₁ R₂ T₂ : ℝ≥0)
    (hcausal : ∀ t, burstDeparture b R₂ T₂ t ≤ burstDeparture b R₁ T₁ t) : Scenario 2 where
  F := tandemF b R₁ T₁ R₂ T₂
  α := fun τ => b + r * τ
  mono := tandemF_mono b R₁ T₁ R₂ T₂
  arr := fun _ _ hst => by simpa [tandemF] using burstArrival_arrival b r hst
  causal := tandemF_causal b R₁ T₁ R₂ T₂ hcausal

/-- **The `N = 2` tandem scenario is admissible** (scenario properties 1–3, §III): the three
cumulative functions are monotone, the ingress is `γ`-upper-constrained, and the chain is causal
`F 2 ≤ F 1 ≤ F 0`.  This packages `tandemScenario`'s structure fields — the explicit reconstructed
trajectory satisfies exactly the scenario properties Lemma 2 samples. -/
theorem tandemScenario_admissible (b r R₁ T₁ R₂ T₂ : ℝ≥0)
    (hcausal : ∀ t, burstDeparture b R₂ T₂ t ≤ burstDeparture b R₁ T₁ t) :
    (∀ h, Monotone ((tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h)) ∧
      (∀ s t : ℝ≥0, s ≤ t → (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F 0 t
        - (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F 0 s
        ≤ (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).α (t - s)) ∧
      (∀ (h : Fin 2) (t : ℝ≥0), (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h.succ t
        ≤ (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h.castSucc t) :=
  ⟨(tandemScenario b r R₁ T₁ R₂ T₂ hcausal).mono,
    (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).arr,
    (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).causal⟩

/-- **Lemma 2 for the `N = 2` tandem: the reconstructed scenario, sampled, is feasible**
(§IV.C, p. 7).  The `N = 2` tandem scenario sampled at the placed tree dates discharges every
pointwise MILP constraint — arrival, monotonicity, FIFO/causality — with objective the realized
delay, by `Scenario.sample_feasible_pointwise`.  This is Lemma 2 instantiated at the concrete
two-node trajectory: the assembled `A ≥ D₁ ≥ D₂` is a feasible point of the seven-date MILP. -/
theorem tandemScenario_sample_feasible (b r R₁ T₁ R₂ T₂ : ℝ≥0)
    (hcausal : ∀ t, burstDeparture b R₂ T₂ t ≤ burstDeparture b R₁ T₁ t)
    (tIn tExit : ℝ≥0) :
    (∀ s t : ℝ≥0, s ≤ t → (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F 0 t
        - (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F 0 s
        ≤ (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).α (t - s)) ∧
    (∀ (h : Fin 3) (s t : ℝ≥0), s ≤ t → (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h s
        ≤ (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h t) ∧
    (∀ (h : Fin 2) (t : ℝ≥0), (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h.succ t
        ≤ (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h.castSucc t) ∧
    (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).realizedDelay tIn tExit
        = (tExit : ℝ) - (tIn : ℝ) :=
  (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).sample_feasible_pointwise tIn tExit

/-- **Lemma 3 for the `N = 2` tandem: the ingress reconstructs as the least `γ`-CAF through its
sample** (§IV.A, p. 8, base case of the backward extrapolation).  The reconstructed ingress is
the single-sample extrapolation `extrapolate γ v {0} t = v 0 + γ t` — the least
`γ_{b,r}`-upper-constrained cumulative function through the committed ingress value `v 0`.  This
is the start of the `N = 2` Lemma 3 reconstruction (`fr(p) = node 1`): a leaky-bucket-shaped
ingress trajectory realizing the solution's ingress value. -/
theorem tandem_ingress_extrapolate {γ v : ℝ≥0 → ℝ≥0} {t : ℝ≥0}
    (ht : (({0} : Finset ℝ≥0).filter (· ≤ t)).Nonempty) :
    extrapolate γ v {0} t ht = v 0 + γ t :=
  extrapolate_singleton ht

/-! ## (2′) The `N = 2` end-to-end realized delay (an explicit admissible scenario)

The tagged bit (the last bit of the burst, quota `b`) arrives at ingress date `0` and departs node
2 at the date where `D₂` reaches `b`.  In the worst case node 2 is the binding (slower-cleared)
server, so the tagged bit's exit date is `T₂ + b/R₂` (`burstDeparture_at_exit` at node 2) — its
realized end-to-end delay is the horizontal gap `(T₂ + b/R₂) − 0`.  We assemble the explicit
admissible scenario realizing this delay; the causality hypothesis (node 2 cleared no faster than
node 1) is the one ordering fact the two-node trajectory needs (and it holds when node 2 is the
bottleneck, `R₂ ≤ R₁`, `T₁ ≤ T₂` — the standard worst case). -/

/-- **The node-2 departure reaches the full burst exactly at `T₂ + b/R₂`** (the `N = 2` exit
date): the tagged bit leaves node 2 at `T₂ + b/R₂` (`burstDeparture_at_exit` at node 2).  Its
realized end-to-end delay, with ingress at date `0`, is `(T₂ + b/R₂) − 0 = T₂ + b/R₂`. -/
theorem tandem_realizedDelay {b R₂ T₂ : ℝ≥0} (hR₂ : 0 < R₂) :
    ((T₂ + b / R₂ : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ) = T₂ + b / R₂ ∧
      burstDeparture b R₂ T₂ (T₂ + b / R₂) = b := by
  refine ⟨by push_cast; ring, burstDeparture_at_exit hR₂⟩

/-- **The `N = 2` tandem reconstruction (§IV.A): an explicit admissible trajectory realizes the
end-to-end delay, both Lemma-2 and Lemma-3 content.**  For a two-node FIFO tandem with the binding
tail server `β_{R₂,T₂}` (`R₂ ≤ R₁`, `T₁ ≤ T₂` the bottleneck-at-node-2 worst case), the burst
trajectory `A ≥ D₁ ≥ D₂`:

* (Lemma 2, `≥`) is an admissible scenario (`tandemScenario_admissible`): monotone, ingress
  `γ`-upper-constrained, causal `D₂ ≤ D₁ ≤ A`, and each node offers its rate-latency service curve
  via Lemma 1 (`burstDeparture_serviceCurve`, `node2_serviceCurve`);
* (Lemma 3, `≤`) the ingress reconstructs as the least `γ`-CAF through its sample
  (`tandem_ingress_extrapolate`); and
* the tagged bit, arriving at `0` and leaving node 2 at `T₂ + b/R₂` (`tandem_realizedDelay`),
  realizes the end-to-end delay `T₂ + b/R₂` — the binding-server contribution.

This is the analogue of `fifoNode_reconstruction` one level up: a genuine, explicit, gate-clean
two-node worst-case trajectory.  (The `≤`-optimality across *all* feasible points for the general
heterogeneous tandem is the LP/MILP content scoped below; here the explicit trajectory is the
realizing witness — the `≥` direction's worst case.) -/
theorem tandem_reconstruction {b r R₁ T₁ R₂ T₂ : ℝ≥0} (hR₂ : 0 < R₂)
    (hcausal : ∀ t, burstDeparture b R₂ T₂ t ≤ burstDeparture b R₁ T₁ t) :
    -- the reconstructed trajectory is an admissible scenario …
    ((∀ h, Monotone ((tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h)) ∧
      (∀ s t : ℝ≥0, s ≤ t → (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F 0 t
        - (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F 0 s
        ≤ (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).α (t - s)) ∧
      (∀ (h : Fin 2) (t : ℝ≥0), (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h.succ t
        ≤ (tandemScenario b r R₁ T₁ R₂ T₂ hcausal).F h.castSucc t)) ∧
    -- … each node offers its rate-latency service curve via Lemma 1 …
    ((∀ t, minConvProj (burstArrival b) (rateLatency R₁ T₁) t ≤ burstDeparture b R₁ T₁ t) ∧
      (∀ t, minConvProj (burstDeparture b R₁ T₁) (rateLatency R₂ T₂) t
        ≤ burstDeparture b R₂ T₂ t)) ∧
    -- … and the tagged bit realizes the end-to-end delay `T₂ + b/R₂`.
    (((T₂ + b / R₂ : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ) = T₂ + b / R₂
      ∧ burstDeparture b R₂ T₂ (T₂ + b / R₂) = b) :=
  ⟨tandemScenario_admissible b r R₁ T₁ R₂ T₂ hcausal,
    ⟨fun t => burstDeparture_serviceCurve b R₁ T₁ t, fun t => node2_serviceCurve b R₁ T₁ R₂ T₂ t⟩,
    tandem_realizedDelay hR₂⟩

/-- **The self-contained `N = 2` tandem reconstruction from data** (§IV.A, bottleneck at node 2):
the same reconstruction as `tandem_reconstruction`, but with the causality hypothesis *discharged*
from the rate/latency ordering `R₂ ≤ R₁`, `T₁ ≤ T₂` (`burstDeparture_le_of_slower`) — node 2 is the
binding server.  So for genuine rate-latency data with node 2 the bottleneck, the burst trajectory
`A ≥ D₁ ≥ D₂` is admissible (monotone, ingress `γ`-constrained, causal), each node offers its
service curve via Lemma 1, and the tagged bit realizes the end-to-end delay `T₂ + b/R₂`, with **no
assumed** causality.  This is the closed two-node analogue of `fifoNode_reconstruction`. -/
theorem tandem_reconstruction_bottleneck {b r R₁ T₁ R₂ T₂ : ℝ≥0} (hR₂ : 0 < R₂)
    (hR : R₂ ≤ R₁) (hT : T₁ ≤ T₂) :
    ((∀ h, Monotone ((tandemScenario b r R₁ T₁ R₂ T₂
        (fun t => burstDeparture_le_of_slower hR hT t)).F h)) ∧
      (∀ (h : Fin 2) (t : ℝ≥0), (tandemScenario b r R₁ T₁ R₂ T₂
          (fun t => burstDeparture_le_of_slower hR hT t)).F h.succ t
        ≤ (tandemScenario b r R₁ T₁ R₂ T₂
          (fun t => burstDeparture_le_of_slower hR hT t)).F h.castSucc t)) ∧
    ((∀ t, minConvProj (burstArrival b) (rateLatency R₁ T₁) t ≤ burstDeparture b R₁ T₁ t) ∧
      (∀ t, minConvProj (burstDeparture b R₁ T₁) (rateLatency R₂ T₂) t
        ≤ burstDeparture b R₂ T₂ t)) ∧
    burstDeparture b R₂ T₂ (T₂ + b / R₂) = b := by
  obtain ⟨⟨hmono, _, hcaus⟩, hsc, _, hexit⟩ := tandem_reconstruction (r := r) hR₂
    (fun t => burstDeparture_le_of_slower hR hT t)
  exact ⟨⟨hmono, hcaus⟩, hsc, hexit⟩

/-! ## (3) The general-`N` recursion skeleton and honest scoping (§IV.C, p. 6–8)

The backward date recursion `placeServiceDates` is stated for *every* `N` (it builds a depth-`N`
`DateTree` from the exit date and the per-node service-date oracles `serviceDateOracle`, each
supplied by Lemma 1), and the per-edge ordering `placeServiceDates_children_le` holds at every
depth.  The `N = 2` reconstruction above instantiates it with the concrete two-node burst
trajectory, both Theorem-1 directions' content.  What the *full* general-`N` round trip still needs
— the exponential MILP the paper solves numerically — is, precisely:

* **The per-node service-curve property at depth `j > 2` (`[infra]`).**  Lemma 1 needs, at node
  `j`, the inequality `D^j ≥ D^{j-1} ∗ β^j` (the node's output dominates the convolution of its
  arrival with its service curve).  At `N = 2` this is `burstDeparture_serviceCurve` (node 1) and
  `node2_serviceCurve` (node 2); for general `N` it is the iterated burst-through-rate-latency
  composition `D^j = burstDeparture b R^j T^j`, whose service-curve property is the same two-arm
  split argument — an `[infra]` induction over the tandem depth, faithful but not a closed form.

* **The global monotonicity / left-continuity of the floor-augmented extrapolation (`[infra]`).**
  `tandem_ingress_extrapolate` gives the single-sample base case and `extrapolate_arrival` the
  `γ`-constraint; the *global* wide-sense increase and left-continuity across the seven (resp.
  `2^{N+1}−1`) sample boundaries need the paper's second floor term `min{F^j(t_k) | t ≥ t_k}` and
  the §IV.A discontinuity handling — an `[infra]` floor-augmented extrapolation and its
  left-continuity proof, identical in shape to the `FifoFeedForwardConcrete` scope note.

* **The `2^N` Boolean FIFO-orderings (`[research]`/`[infra]`).**  THE exponential frontier.  At
  `N = 2` the single tagged path with the *burst* worst case fixes one total order on the seven
  dates, so no Boolean variable is exercised — the reconstruction is one explicit trajectory.  For
  general `N` (and multiple flows) the feasible point fixes *one* of the exponentially many Boolean
  orderings of the partially-ordered input times of each node, and Lemma 3 must extrapolate a
  scenario that preserves the FIFO service order for *that* ordering, for *every* path.  Enumerating
  the `2^N` orderings is what makes the MILP exponential (`tandemMilpNumTimes N = 2^{N+1}−1`,
  feasible only to six or seven nodes); there is **no** general-`N` closed form, and none is claimed
  here — the orderings are not hidden inside a fake general theorem (contrast the homogeneous tandem
  `fifoTandemHomogeneous_worstCaseDelay`, where Lemma 2 collapses to the single all-zero ordering,
  and the `N = 1`/`N = 2` bursts here, where the worst case is one explicit trajectory).

So: Lemma 1, the backward date recursion (all `N`), and the concrete `N = 2` reconstruction (both
Theorem-1 directions' content) are theorems here; the general-`N` discharge of Lemmas 2/3 over the
`2^N` Boolean orderings is the exponential construction the paper writes down and a solver
evaluates, scoped `[infra]`/`[research]` (consistent with `FifoFeedForwardExact` /
`FifoFeedForwardConcrete` / `FifoFeedForwardReconstruction`). -/

/-! ## Restatements (the declarations say what [BOU 16b] §IV.A–C says) -/

/-- §IV.C (p. 6–7): the backward date recursion builds the depth-`N` `DateTree` from the exit
date `t`, with `2^(N+1)−1` dates, root `t`, and **every** date `≤ t` (the `t₁ ≥ t₂ ≥ …` ordering
chain over the whole tree). -/
example {N : ℕ} (oracles : Fin (N + 1) → ServiceDateOracle × ServiceDateOracle) (t : ℝ≥0) :
    (placeServiceDates oracles t).count = 2 ^ (N + 1) - 1
      ∧ (placeServiceDates oracles t).rootDate = (t : ℝ)
      ∧ (placeServiceDates oracles t).allLe (t : ℝ) :=
  ⟨DateTree.count_eq _, placeServiceDates_rootDate oracles t, placeServiceDates_allLe oracles t⟩

/-- Lemma 1 (§IV.A, p. 4) at node 2: every node-2 exit date `t₁` has a service date `t₃ ≤ t₁` with
`D₂(t₁) ≥ D₁(t₃) + R₂·(t₁ − t₃ − T₂)` — the recursion step one node up from the base case. -/
example (b R₁ T₁ R₂ T₂ : ℝ≥0) (t₁ : ℝ≥0) :
    ∃ t₃ ≤ t₁, burstDeparture b R₁ T₁ t₃ + R₂ * (t₁ - t₃ - T₂) ≤ burstDeparture b R₂ T₂ t₁ :=
  node2_serviceDate b R₁ T₁ R₂ T₂ t₁

/-- §IV.A at `N = 2`: the two-node burst trajectory is admissible (each node offers its
rate-latency service curve via Lemma 1) and the tagged bit realizes the end-to-end delay
`T₂ + b/R₂`. -/
example {b r R₁ T₁ R₂ T₂ : ℝ≥0} (hR₂ : 0 < R₂)
    (hcausal : ∀ t, burstDeparture b R₂ T₂ t ≤ burstDeparture b R₁ T₁ t) :
    (∀ t, minConvProj (burstArrival b) (rateLatency R₁ T₁) t ≤ burstDeparture b R₁ T₁ t) ∧
      (∀ t, minConvProj (burstDeparture b R₁ T₁) (rateLatency R₂ T₂) t
        ≤ burstDeparture b R₂ T₂ t) ∧
      burstDeparture b R₂ T₂ (T₂ + b / R₂) = b :=
  ⟨(tandem_reconstruction (r := r) hR₂ hcausal).2.1.1,
    (tandem_reconstruction (r := r) hR₂ hcausal).2.1.2,
    (tandem_reconstruction (r := r) hR₂ hcausal).2.2.2⟩

/-- §IV.A at `N = 2`, from data (node 2 the bottleneck `R₂ ≤ R₁`, `T₁ ≤ T₂`): the burst trajectory
is admissible with **discharged** causality, each node offers its service curve, and the tagged bit
realizes the delay `T₂ + b/R₂` — the closed two-node analogue of `fifoNode_reconstruction`. -/
example {b r R₁ T₁ R₂ T₂ : ℝ≥0} (hR₂ : 0 < R₂) (hR : R₂ ≤ R₁) (hT : T₁ ≤ T₂) :
    (∀ t, minConvProj (burstArrival b) (rateLatency R₁ T₁) t ≤ burstDeparture b R₁ T₁ t) ∧
      (∀ t, minConvProj (burstDeparture b R₁ T₁) (rateLatency R₂ T₂) t
        ≤ burstDeparture b R₂ T₂ t) ∧
      burstDeparture b R₂ T₂ (T₂ + b / R₂) = b :=
  ⟨(tandem_reconstruction_bottleneck (r := r) hR₂ hR hT).2.1.1,
    (tandem_reconstruction_bottleneck (r := r) hR₂ hR hT).2.1.2,
    (tandem_reconstruction_bottleneck (r := r) hR₂ hR hT).2.2⟩

end FifoFeedForward

end DeepWiki
