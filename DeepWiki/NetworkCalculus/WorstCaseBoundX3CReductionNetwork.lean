import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReductionBridge

/-! # The network-dynamics realization of the X3C worst-case backlog (DNC Theorem 10.2)
The bridge (`WorstCaseBoundX3CReductionBridge`) establishes the *combinatorial* target:
the worst-case backlog at the bottom server `W` of the Figure-10.7 network is
`3(s−q) + (max saturatedCount)`, reaching the threshold `3s − 2q` iff an exact
3-cover exists. What that bridge takes as given — and what this file *builds from
the served rate equations* — is the actual per-server backlog computation: that at
an integral routing (an `IsAssignment`, the extremal vertex `r ∈ {0,1}`), the
cumulative dynamics realize exactly `3(s−q) + saturatedCount` at the bottom server
at time `1⁻`.

The construction (Figure 10.7, faithfully): under the greedy adversary every
interfering flow sends `min(t,1)` (rate `1` on `[0,1)`, total `1` by time `1`), and
each of the `3s` flows `(i, e)` (subset `i`, element `e ∈ members i`) is served at
the upper stage at rate `r_{i,e}`, an integral routing assigning `r_{i,e} = 1` iff
`assign e = i`. The book's rate equations then give, at time `1⁻`:

* upper-stage backlog `= 3s − Σ_{i,e} r_{i,e} = 3(s−q)` (each of the `3q` elements
  contributes routed weight `1`, so `Σ r = 3q`);
* middle-server `i` is fed at rate `min(3, load i)` where `load i = Σ_{e∈cᵢ} r_{i,e}`,
  and with strict service rate `2` its backlog grows at `[load i − 2]⁺`; summed over
  the subsets this is the number of *saturated* subsets;
* the bottom server `W` (rate `R > 3s`, hence non-binding before time `1`) accumulates
  the sum, so its backlog at `1⁻` is `3(s−q) + saturatedCount`.

What is **proved** here is this realization — `backlogAtW_eq_backlogValue` — as exact
arithmetic over the served rate equations (the routing constraint, the per-stage
totals, the `[·−2]⁺ = saturated` step), plus the transfer of the worst-case value and
the `3s − 2q` threshold to this network model. What is **scoped** (recorded in
`## SCOPE` at the end) is the genuine remaining analysis: that the *continuous-time*
fluid trajectories on `[0,1)` integrate these rates (so the discrete cumulative model
*is* the time-`1⁻` value), and that no *fractional* routing beats the integral vertices
(the convex-maximization-attains-vertices step). The first is a Mathlib analysis layer
(rate integration / `Curve`-valued ODE), the second a finite-dimensional convexity fact;
both sit *above* the served-equation arithmetic this file makes rigorous. -/

namespace DeepWiki

open Finset

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

/-! ## The integral routing read off an assignment
The extremal vertex `r_{i,e} ∈ {0,1}` of the Figure-10.7 rate polytope realized by
an assignment: flow `(i, e)` is served at the upper stage at rate `1` iff `e` is
routed to subset `i`, and `0` otherwise. -/

/-- The **upper-stage service rate** `r_{i,e}` of flow `(i, e)` at the integral
vertex of the routing polytope realized by `assign`: `1` iff element `e` is routed
to subset `i` (and `i` indeed contains `e`), else `0`. -/
def X3CInstance.routeRate (I : X3CInstance ι α) (assign : α → ι) (i : ι) (e : α) : ℕ :=
  if e ∈ I.members i ∧ assign e = i then 1 else 0

/-- `routeRate` is `0/1`: an integral extremal vertex of the rate polytope. -/
theorem X3CInstance.routeRate_le_one (I : X3CInstance ι α) (assign : α → ι)
    (i : ι) (e : α) : I.routeRate assign i e ≤ 1 := by
  unfold X3CInstance.routeRate; split <;> simp

/-! ## The routing constraint `Σ_{i ∋ e} r_{i,e} = 1`
The polytope constraint at the integral vertex: each element's served weight,
summed over the subsets containing it, is exactly `1` — it routes to the single
subset `assign e`. -/

/-- **The routing constraint** at the integral vertex: for a valid assignment, each
element `e`'s total served weight `Σ_i r_{i,e}` is `1` (it is served only by the
subset `assign e`, which contains it). -/
theorem X3CInstance.sum_routeRate_eq_one (I : X3CInstance ι α) {assign : α → ι}
    (hassign : I.IsAssignment assign) (e : α) :
    ∑ i, I.routeRate assign i e = 1 := by
  rw [Finset.sum_eq_single (assign e)]
  · unfold X3CInstance.routeRate; rw [if_pos ⟨hassign e, rfl⟩]
  · intro i _ hne
    unfold X3CInstance.routeRate
    rw [if_neg]; rintro ⟨_, rfl⟩; exact hne rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The upper-stage served total and backlog
Summing the routing constraint over the `3q` elements gives the upper-stage served
total `Σ_{i,e} r_{i,e} = 3q`, so the upper-stage backlog at time `1⁻` (arrivals
`3s` minus served `3q`) is `3(s−q)`. -/

/-- The **upper-stage served total** `Σ_{i,e} r_{i,e}` at the integral vertex. -/
def X3CInstance.upperServedTotal (I : X3CInstance ι α) (assign : α → ι) : ℕ :=
  ∑ i, ∑ e, I.routeRate assign i e

/-- **The upper-stage served total is `3q`** (`= |α|`): each of the `3q` elements
routes with total weight `1` (the routing constraint summed over elements). -/
theorem X3CInstance.upperServedTotal_eq (I : X3CInstance ι α) {assign : α → ι}
    (hassign : I.IsAssignment assign) :
    I.upperServedTotal assign = 3 * I.q := by
  unfold X3CInstance.upperServedTotal
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun e _ => I.sum_routeRate_eq_one hassign e)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, I.card_elts]

/-- The **total greedy arrivals at the upper stage** by time `1⁻`: `3s = 3 · |ι|`,
since each of the `3s` flows (`3` per subset) sends `min(t,1) → 1` by time `1`. -/
def X3CInstance.upperArrivalsTotal (I : X3CInstance ι α) : ℕ := 3 * I.numSubsets

/-- The **upper-stage backlog at time `1⁻`**: arrivals `3s` minus served `Σ r_{i,e}`.
At the integral vertex this is the assignment-independent constant `3(s−q)`. -/
def X3CInstance.upperBacklogAt (I : X3CInstance ι α) (assign : α → ι) : ℕ :=
  I.upperArrivalsTotal - I.upperServedTotal assign

/-- **The upper-stage backlog at `1⁻` is `3(s−q)`** — the served-equation derivation
of the constant term of `backlogValue`: `3s − 3q`. -/
theorem X3CInstance.upperBacklogAt_eq (I : X3CInstance ι α) {assign : α → ι}
    (hassign : I.IsAssignment assign) :
    I.upperBacklogAt assign = 3 * (I.numSubsets - I.q) := by
  unfold X3CInstance.upperBacklogAt X3CInstance.upperArrivalsTotal
  rw [I.upperServedTotal_eq hassign]; omega

/-! ## The middle-stage load and `[·−2]⁺ = saturated` step
Middle-server `i` is fed by `U_i` at rate `min(3, load i)`, where `load i = Σ_{e∈cᵢ}
r_{i,e}` is the number of `i`'s elements that route to `i`. With strict service rate
`2`, its backlog grows at `[load i − 2]⁺`. Since `load i ≤ 3` (a subset has three
elements), `[load i − 2]⁺` is `1` for a *saturated* subset (`load = 3`) and `0`
otherwise — the served-equation derivation of the saturation objective. -/

/-- The **load of middle-server `i`** at the integral vertex: `Σ_{e ∈ cᵢ} r_{i,e}`,
the number of `i`'s own elements routed to `i`. -/
def X3CInstance.load (I : X3CInstance ι α) (assign : α → ι) (i : ι) : ℕ :=
  ∑ e ∈ I.members i, I.routeRate assign i e

/-- The load counts the members of `i` routed to `i`:
`load i = #{e ∈ cᵢ | assign e = i}`. -/
theorem X3CInstance.load_eq_card (I : X3CInstance ι α) (assign : α → ι) (i : ι) :
    I.load assign i = ((I.members i).filter (fun e => assign e = i)).card := by
  unfold X3CInstance.load X3CInstance.routeRate
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [he, true_and]

/-- **The load is at most `3`**: a subset has three elements, so at most three of
them can route to it. -/
theorem X3CInstance.load_le_three (I : X3CInstance ι α) (assign : α → ι) (i : ι) :
    I.load assign i ≤ 3 := by
  rw [I.load_eq_card]
  calc ((I.members i).filter (fun e => assign e = i)).card
      ≤ (I.members i).card := Finset.card_filter_le _ _
    _ = 3 := I.card_members i

/-- **The load is `3` iff the subset is saturated**: all three of `i`'s elements
route to `i` exactly when each does. -/
theorem X3CInstance.load_eq_three_iff_saturated (I : X3CInstance ι α)
    (assign : α → ι) (i : ι) :
    I.load assign i = 3 ↔ I.IsSaturated assign i := by
  rw [I.load_eq_card, X3CInstance.IsSaturated]
  constructor
  · intro hcard e he
    by_contra hne
    have hssub : (I.members i).filter (fun e => assign e = i) ⊂ I.members i :=
      Finset.filter_ssubset.mpr ⟨e, he, hne⟩
    have := Finset.card_lt_card hssub
    rw [hcard, I.card_members i] at this; exact lt_irrefl _ this
  · intro hsat
    rw [Finset.filter_true_of_mem (fun e he => hsat e he), I.card_members i]

/-- The middle-server `i` backlog rate `[load i − 2]⁺` is `1` when `i` is saturated
and `0` otherwise — the per-subset contribution to the saturation objective. -/
theorem X3CInstance.middleRate_eq (I : X3CInstance ι α) (assign : α → ι) (i : ι) :
    I.load assign i - 2 = if I.IsSaturated assign i then 1 else 0 := by
  have hle := I.load_le_three assign i
  by_cases hsat : I.IsSaturated assign i
  · rw [if_pos hsat, (I.load_eq_three_iff_saturated assign i).mpr hsat]
  · rw [if_neg hsat]
    have hne : I.load assign i ≠ 3 := fun h =>
      hsat ((I.load_eq_three_iff_saturated assign i).mp h)
    omega

/-- The **middle-stage backlog at time `1⁻`**: `Σ_i [load i − 2]⁺`, the sum over the
subsets of the strict-service-`2` backlog growth at server `Vᵢ`. -/
def X3CInstance.middleBacklogAt (I : X3CInstance ι α) (assign : α → ι) : ℕ :=
  ∑ i, (I.load assign i - 2)

/-- **The middle-stage backlog at `1⁻` is the saturated count** — the served-equation
derivation of the saturation objective: `Σ_i [load i − 2]⁺ = #{saturated subsets}`. -/
theorem X3CInstance.middleBacklogAt_eq (I : X3CInstance ι α) (assign : α → ι) :
    I.middleBacklogAt assign = I.saturatedCount assign := by
  unfold X3CInstance.middleBacklogAt X3CInstance.saturatedCount X3CInstance.saturated
  rw [Finset.sum_congr rfl (fun i _ => I.middleRate_eq assign i)]
  rw [Finset.sum_boole, Finset.card_filter]
  norm_cast

/-! ## The backlog at the bottom server `W` (time `1⁻`)
The bottom server `W` has rate `R > 3s`, so before time `1` it serves everything
offered and its backlog is the *total* backlog of the upstream system, i.e. the sum
of the upper-stage and middle-stage backlogs. At the integral vertex this is
`3(s−q) + saturatedCount`, which is exactly `backlogValue assign` from the bridge —
the realization of the combinatorial objective by the served rate equations. -/

/-- The **backlog at the bottom server `W` at time `1⁻`** realized by the integral
routing: the total upstream backlog (upper stage `+` middle stage). The `R > 3s`
bottom rate is non-binding before time `1`, so `W`'s backlog is this sum. -/
def X3CInstance.backlogAtW (I : X3CInstance ι α) (assign : α → ι) : ℕ :=
  I.upperBacklogAt assign + I.middleBacklogAt assign

/-- **The network realization (Theorem 10.2, integral vertex)**: the backlog at `W`
at time `1⁻` realized by the integral routing equals the combinatorial backlog value
`3(s−q) + saturatedCount`. This is the served-equation computation underlying the
bridge's `backlogValue` — the worst-case backlog *is* what the network dynamics
produce at the extremal vertices. -/
theorem X3CInstance.backlogAtW_eq_backlogValue (I : X3CInstance ι α)
    {assign : α → ι} (hassign : I.IsAssignment assign) :
    I.backlogAtW assign = I.backlogValue assign := by
  unfold X3CInstance.backlogAtW X3CInstance.backlogValue
  rw [I.upperBacklogAt_eq hassign, I.middleBacklogAt_eq assign]

/-- The realized backlog at `W` is dominated by the worst-case backlog (the bridge's
`worstCaseBacklog`): every integral routing's `W`-backlog lower-bounds the optimum. -/
theorem X3CInstance.backlogAtW_le_worstCaseBacklog (I : X3CInstance ι α)
    {assign : α → ι} (hassign : I.IsAssignment assign) :
    I.backlogAtW assign ≤ I.worstCaseBacklog := by
  rw [I.backlogAtW_eq_backlogValue hassign]
  exact I.backlogValue_le_worstCaseBacklog hassign

/-! ## Worst-case `W`-backlog over integral routings = the combinatorial optimum
The worst case over the *integral* extremal vertices (the `IsAssignment` routings) of
the realized `W`-backlog is, by `backlogAtW_eq_backlogValue`, exactly the bridge's
`worstCaseBacklog`. Hence the whole threshold correspondence transfers verbatim to
this network model: the worst case reaches `3s − 2q` iff an X3C cover exists. -/

/-- The **worst-case `W`-backlog over integral routings**: the supremum of the realized
`W`-backlog over the integral extremal vertices (the valid assignments). -/
noncomputable def X3CInstance.worstCaseBacklogAtW (I : X3CInstance ι α) : ℕ :=
  ⨆ c : {assign // I.IsAssignment assign}, I.backlogAtW c.1

/-- **The worst-case `W`-backlog over integral routings is the combinatorial optimum**:
the network realization (`backlogAtW = backlogValue` on valid assignments) makes the
two supremums coincide, so the served-equation `W`-backlog optimum is the bridge's
`worstCaseBacklog`. -/
theorem X3CInstance.worstCaseBacklogAtW_eq (I : X3CInstance ι α)
    (hne : I.HasAssignment) :
    I.worstCaseBacklogAtW = I.worstCaseBacklog := by
  obtain ⟨a0, ha0⟩ := hne
  haveI : Nonempty {assign // I.IsAssignment assign} := ⟨⟨a0, ha0⟩⟩
  unfold X3CInstance.worstCaseBacklogAtW X3CInstance.worstCaseBacklog
  exact iSup_congr fun c => I.backlogAtW_eq_backlogValue c.2

/-- **The network worst-case `W`-backlog is `≤ 3s − 2q`** (the book's upper bound,
realized): the served-equation optimum over the integral vertices does not exceed the
cover threshold. -/
theorem X3CInstance.worstCaseBacklogAtW_le (I : X3CInstance ι α)
    (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    I.worstCaseBacklogAtW ≤ 3 * I.numSubsets - 2 * I.q := by
  rw [I.worstCaseBacklogAtW_eq hne]; exact I.worstCaseBacklog_le hne hsq

/-- **The network worst-case `W`-backlog reaches `3s − 2q` iff an exact cover exists**
(Theorem 10.2 at the network level): deciding whether the served-equation worst-case
`W`-backlog is at least `3s − 2q` is exactly deciding X3C. This is the threshold
correspondence transferred from the bridge to the realized network dynamics. -/
theorem X3CInstance.threshold_le_worstCaseBacklogAtW_iff_exists_cover
    (I : X3CInstance ι α) (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    3 * I.numSubsets - 2 * I.q ≤ I.worstCaseBacklogAtW ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) := by
  rw [I.worstCaseBacklogAtW_eq hne]
  exact I.threshold_le_worstCaseBacklog_iff_exists_cover hne hsq

/-! ## Book restatement (Theorem 10.2, network realization at the integral vertices)
At an integral routing the Figure-10.7 served rate equations produce, at the bottom
server `W` and time `1⁻`, a backlog of `3(s−q) + saturatedCount` (upper-stage backlog
`3(s−q)` plus middle-stage backlog `Σᵢ [loadᵢ − 2]⁺ = saturatedCount`). The worst case
over the integral vertices is the combinatorial optimum, bounded by `3s − 2q` and
reaching it iff an X3C cover exists — the served-equation realization of the
NP-hardness threshold. -/
example (I : X3CInstance ι α) {assign : α → ι} (hassign : I.IsAssignment assign) :
    -- the realized backlog at `W` is `3(s−q) + saturatedCount`
    I.backlogAtW assign = 3 * (I.numSubsets - I.q) + I.saturatedCount assign :=
  I.backlogAtW_eq_backlogValue hassign

example (I : X3CInstance ι α) (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    -- the network worst case is bounded by `3s − 2q` and reaches it iff a cover
    I.worstCaseBacklogAtW ≤ 3 * I.numSubsets - 2 * I.q ∧
    (3 * I.numSubsets - 2 * I.q ≤ I.worstCaseBacklogAtW ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i)) :=
  ⟨I.worstCaseBacklogAtW_le hne hsq,
   I.threshold_le_worstCaseBacklogAtW_iff_exists_cover hne hsq⟩

/-! ## SCOPE — what a full fluid-dynamics realization needs beyond this
This file realizes the worst-case backlog from the served rate equations **at the
integral extremal vertices** of the Figure-10.7 polytope. Three layers sit above the
served-equation arithmetic proved here, and are *not* formalized:

* **[infra] Continuous-time rate integration.** The book's quantities are *rates* over
  the infinitesimal interval; the time-`1⁻` cumulative values are their integrals over
  `[0,1)` against the greedy arrivals `min(t,1)`. Turning the rate model into actual
  `Curve`-valued cumulative input/output functions `A_W, D_W : ℝ≥0 → ℝ≥0` and reading
  `backlog A_W D_W = ⨆_t (A_W t − D_W t)` at `t → 1⁻` (`Deviation.backlog`,
  `IsStrictMinimalServiceCurve` for the rate-`2` middle servers, `start`-of-backlog on
  `[0,1)`) needs a rate-integration / piecewise-linear-trajectory layer. This is a
  Mathlib *analysis* layer (integrate-a-rate, left-limit at `1`), not a new combinatorial
  fact; the arithmetic it would integrate to is exactly `backlogAtW`.

* **[research] Fractional-vs-integral optimality (the convex-maximization step).** The
  objective `Σᵢ [Σⱼ r_{i,j} − 2]⁺` is *convex* in the routing `r` over the feasibility
  polytope `{r ≥ 0 : Σ_{i∋j} r_{i,j} = 1}`, so its maximum is attained at an extremal
  vertex, and the vertices are exactly the integral routings (`r ∈ {0,1}`, the
  `IsAssignment`s). Proving that *no fractional fluid routing beats the integral
  vertices* is a finite-dimensional convexity fact (maximum of a convex function on a
  polytope is at a vertex; the polytope here is a product of simplices whose vertices are
  integral). It is *finite/convexity*, not an open analysis gap — but it needs a polytope/
  convex-maximization layer (vertices of `∏ⱼ Δ(subsets ∋ j)`, convexity of `[·−2]⁺`) not
  yet built. Until then, `worstCaseBacklogAtW` is the worst case *over the integral
  vertices*, which by this argument is the worst case over the whole polytope.

* **[external] The `Complexity.NPHard` wrapper.** Packaging "X3C ≤ₚ worst-case-backlog"
  as a formal NP-hardness statement needs a complexity-class framework Mathlib does not
  provide. The polynomial-time reduction *map* and its *correctness bi-implication* (the
  threshold ⟺ cover correspondence) are what is formalizable, and are done here and in the
  bridge.

The **combinatorial correspondence** (cover ⟺ threshold) and the **integral-vertex
served-equation realization** (`backlogAtW_eq_backlogValue`) are complete and exact; the
gaps above are the *attainment* analysis (rate integration; vertex-optimality), strictly
above the served-equation layer. -/

end DeepWiki
