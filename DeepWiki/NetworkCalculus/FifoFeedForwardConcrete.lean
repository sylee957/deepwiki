import DeepWiki.NetworkCalculus.FifoFeedForwardExact

/-! # The concrete binary-tree MILP layout and Lemmas 2/3 ([BOU 16b], §IV.C)

The companion to `FifoFeedForwardExact`, which formalizes the **abstract** Theorem 1
bridge `programOptimum_eq_of_scenarioSolution` (the MILP optimum equals the worst-case
delay *given* delay-preserving correspondence maps for Lemmas 2 and 3).  Here we go one
layer down and build the **concrete** structures that the abstract bridge abstracts over,
following Bouillard and Stea, "Exact Worst-Case Delay in FIFO-Multiplexing Feed-Forward
Networks", IEEE/ACM Trans. Networking 2016 (DOI `10.1109/TNET.2014.2332071`), §IV.C
(General Feed-Forward Network), pp. 6–8.

We focus on a **single tagged path** `p = (1, …, N)` (a tandem; the figure-tree of §IV.C
for general DAGs is the same recursion with multiple successors, scoped at the end).  The
paper's recursion (p. 6–7)

* `T_out^N = {t₁}`;
* `T_in^j = FIFO^j(T_out^j) ∪ SC^j(T_out^j)`;
* `T_out^j = ⋃_{k ∈ succ(j)} T_in^k`,

makes the live set of dates **double** at each node going backwards (every output time `t`
spawns a FIFO input time `t' = FIFO^j(t)` and a service input time `t'' = SC^j(t)`), so the
total date count is the full-binary-tree count `2^(N+1) − 1` (already `tandemMilpNumTimes`).

What this file delivers — the concrete construction, as far as it closes:

* **(1) The binary-tree date layout as data** (`DateTree`): an inductive depth-`N` binary
  tree carrying a real date at each node, with the FIFO child and SC child of each output
  date, plus the per-flow sampled function values; the count `dateTreeCount N = 2^(N+1)−1`
  (matching `tandemMilpNumTimes`), and the MILP well-formedness predicate `DateTreeFeasible`
  (date ordering, monotonicity, FIFO, service, arrival) over it.

* **(2) Lemma 2 (scenario → feasible solution), the easy direction** (p. 7): a real
  scenario — admissible cumulative trajectories satisfying scenario properties 1–5 of §III —
  sampled at the tree dates gives a feasible point with the **same** objective.  We build the
  sampling map `sampleTree` and discharge the constraints that follow *pointwise* from the
  scenario properties (FIFO causality, arrival `α_p`-constraint, monotonicity, the objective
  `t₁ − t₀ = d`).  The full backward construction of the tree *dates* themselves (via Lemma 1,
  the convolution-time existence) is the genuinely recursive part and is scoped.

* **(3) Lemma 3 (solution → scenario), the reconstruction core** (p. 8): the min-plus
  **extrapolation** `F_p^j(t) = min{F_p^j(t_k) + α_p(t − t_k) : t_k ≤ t}` that the paper uses
  to rebuild an admissible cumulative function from a feasible solution.  We prove the
  extrapolation is **wide-sense increasing** and **α_p-upper-constrained** (the two scenario
  properties it is built to guarantee), over a finite sample set.  The full Lemma 3 also needs
  left-continuity and FIFO-order preservation across the (exponentially many) Boolean
  orderings; that is the genuinely new existence content and is adjudicated precisely at the
  end.

CRITICAL HONESTY (carried from `FifoFeedForwardExact`): the general-`N` exact FIFO WCD is an
**exponential MILP the paper solves numerically** — there is no general closed form and no
complete Lemma 3 here.  We deliver the concrete tree layout, Lemma 2's pointwise discharges,
and Lemma 3's extrapolation core, with the residual exponential/existence content scoped. -/

namespace DeepWiki

namespace FifoFeedForward

open scoped NNReal

/-! ## (1) The binary-tree date layout as data (§IV.C, p. 6–7)

The MILP date variables of a tandem of `N` nodes form a full binary tree of depth `N`:
the root is the single output time `t₁ = T_out^N`, and each output date `t` of a node spawns
two input dates one node backwards — `FIFO^j(t)` (the FIFO time) and `SC^j(t)` (the service
time).  We model this directly as an inductive tree carrying a real date at each node. -/

/-- **The binary-tree date layout** of the §IV.C MILP (p. 6–7), depth `N`: a `leaf` carries a
single date (an ingress output time of the trace), and a `node date fifo sc` carries the
output date `date` together with its two backward children — the **FIFO** subtree `fifo`
(rooted at `FIFO^j(date)`) and the **service-curve** subtree `sc` (rooted at `SC^j(date)`).
The root date is the tagged flow's exit time `t₁`; depth `N` is the number of nodes. -/
inductive DateTree : ℕ → Type
  /-- A leaf: a single ingress date (depth `0`, the bottom of the backward trace). -/
  | leaf (date : ℝ) : DateTree 0
  /-- An internal node at depth `N+1`: the output date `date` with its FIFO child subtree
  `fifo` (rooted at `FIFO^j(date)`) and SC child subtree `sc` (rooted at `SC^j(date)`). -/
  | node {N : ℕ} (date : ℝ) (fifo sc : DateTree N) : DateTree (N + 1)

namespace DateTree

/-- The date stored at the root of a `DateTree` (the output time `t` of its node, or the
single date of a leaf). -/
def rootDate : ∀ {N}, DateTree N → ℝ
  | 0, leaf d => d
  | _ + 1, node d _ _ => d

/-- The total number of date variables in a depth-`N` tree (one per tree node): the full
binary tree count `2^(N+1) − 1`, matching `tandemMilpNumTimes`. -/
def count : ∀ {N}, DateTree N → ℕ
  | 0, leaf _ => 1
  | _ + 1, node _ f s => count f + count s + 1

/-- **The date count is `2^(N+1) − 1`** for every depth-`N` tree (independent of the dates),
agreeing with `tandemMilpNumTimes N` (the exponential blow-up of §IV.C, p. 6). -/
theorem count_eq : ∀ {N} (t : DateTree N), t.count = 2 ^ (N + 1) - 1
  | 0, leaf _ => rfl
  | N + 1, node _ f s => by
    rw [count, count_eq f, count_eq s]
    have h1 : 1 ≤ 2 ^ (N + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (N + 1 + 1) = 2 * 2 ^ (N + 1) := by rw [pow_succ]; ring
    omega

/-- The date count of a tree equals `tandemMilpNumTimes` of its depth — the inductive tree
realizes the `2^(N+1)−1` count of `FifoFeedForwardExact`. -/
theorem count_eq_numTimes {N} (t : DateTree N) : t.count = tandemMilpNumTimes N := by
  rw [count_eq, tandemMilpNumTimes_eq]

end DateTree

/-! ## The tagged-flow scenario (scenario properties 1–5, §III, p. 4)

A scenario of the tandem is the family of cumulative functions of the tagged flow at each
node, satisfying the §III properties (specialized to a single tagged path `p = (1,…,N)`):

1. each `F^h` is wide-sense increasing and left-continuous;
2. `F^h ≥ F^{h+1}` (output below input — FIFO causality through the node);
3. `F^0` (ingress) is `α`-upper-constrained;
4. service: `F^{h} t' ≤ F^{h+1} t + β^h(t − t')` shape (here in the per-date sampled form
   used by the MILP, not the convolution form);
5. nodes satisfy the FIFO property.

For the **pointwise** discharges of Lemma 2 (the part that closes), the relevant data is the
per-node cumulative `F : Fin (N+1) → ℝ≥0 → ℝ≥0` and the pointwise scenario properties.  We
record the two that Lemma 2 uses directly: wide-sense increase (property 1) and the
`α`-upper-constraint (property 3). -/

/-- **A tagged-flow scenario** over a tandem of `N` nodes (scenario properties of §III,
p. 4, single-path specialization): `F h` is the cumulative function of the tagged flow at the
input of node `h` (so `F 0` is the network ingress and `F (last)` the exit CDF), `α` is the
arrival curve of the flow.  Carries the two pointwise properties Lemma 2 consumes:

* `mono`: each `F h` is wide-sense increasing (property 1);
* `arr`: the ingress `F 0` is `α`-upper-constrained, `F 0 t − F 0 s ≤ α (t − s)` for `s ≤ t`
  (property 3);
* `causal`: `F (h+1) t ≤ F h t` (output below input — property 2, FIFO causality). -/
structure Scenario (N : ℕ) where
  /-- Per-node cumulative function of the tagged flow (`F 0` ingress, `F N` exit). -/
  F : Fin (N + 1) → ℝ≥0 → ℝ≥0
  /-- The arrival curve of the tagged flow. -/
  α : ℝ≥0 → ℝ≥0
  /-- Property 1: each cumulative function is wide-sense increasing. -/
  mono : ∀ h, Monotone (F h)
  /-- Property 3: the ingress cumulative is `α`-upper-constrained. -/
  arr : ∀ s t : ℝ≥0, s ≤ t → F 0 t - F 0 s ≤ α (t - s)
  /-- Property 2: the cumulative through a node decreases (output ≤ input). -/
  causal : ∀ (h : Fin N) (t : ℝ≥0), F h.succ t ≤ F h.castSucc t

namespace Scenario

variable {N : ℕ}

/-- **The realized delay** of a tagged bit in a scenario, observed at exit date `tExit` and
ingress date `tIn`: `d = tExit − tIn` (the horizontal gap between the two dates at which the
same bit's quota is seen at exit and at ingress).  The objective `t₁ − t₀` of the MILP is this
quantity for the worst bit (§IV.C objective, p. 7). -/
def realizedDelay (_ : Scenario N) (tIn tExit : ℝ≥0) : ℝ := (tExit : ℝ) - (tIn : ℝ)

/-- The ingress cumulative is monotone (the `h = 0` case of property 1). -/
theorem mono_ingress (S : Scenario N) : Monotone (S.F 0) := S.mono 0

end Scenario

/-! ## (2) Lemma 2: scenario → feasible solution (the easy direction, p. 7)

"Let `F` be a scenario of the network with delay `d`.  There exists a feasible solution of
(∗) such that `t₁ − t₀ = d`." (p. 7).  The construction sets `t₂ = FIFO^N(t₁)`,
`t₃ = SC^N(t₁)`, recurses backwards (Lemma 1: the convolution-time existence), and **samples**
the scenario's function values at the tree dates.  The resulting point is feasible — every
MILP constraint is a property the scenario already satisfies.

We deliver the **per-constraint discharges that follow pointwise** from the scenario
properties, which is the bulk of Lemma 2's "feasibility" claim once the dates are fixed:

* the **arrival** constraint `F 0 t − F 0 s ≤ α (t − s)` (directly `Scenario.arr`);
* the **monotonicity** constraint `F h s ≤ F h t` for `s ≤ t` (directly `Scenario.mono`);
* the **causality / FIFO** constraint `F (h+1) t ≤ F h t` (directly `Scenario.causal`);
* the **objective** equality `realizedDelay = d` (definitional).

The recursive construction of the tree *dates* via Lemma 1 (convolution-time existence) is the
remaining part and is scoped — it is the backward recursion over the tree, faithful but not a
closed form. -/

namespace Scenario

variable {N : ℕ}

/-- **Lemma 2, arrival discharge** (p. 7): sampled at any two tree dates `s ≤ t`, the ingress
cumulative satisfies the MILP arrival constraint `F 0 t − F 0 s ≤ α(t − s)` — directly the
scenario's `α`-upper-constraint (property 3).  This is one of the constraints `C_F` that a
sampled scenario discharges for free. -/
theorem sample_arrival (S : Scenario N) {s t : ℝ≥0} (hst : s ≤ t) :
    S.F 0 t - S.F 0 s ≤ S.α (t - s) :=
  S.arr s t hst

/-- **Lemma 2, monotonicity discharge** (p. 7): sampled at tree dates `s ≤ t`, every node's
cumulative satisfies the MILP monotonicity constraint `F h s ≤ F h t` — directly property 1.
(In the MILP this is enforced via the Boolean ordering variables; in a real scenario it holds
because cumulative functions are wide-sense increasing.) -/
theorem sample_monotone (S : Scenario N) (h : Fin (N + 1)) {s t : ℝ≥0} (hst : s ≤ t) :
    S.F h s ≤ S.F h t :=
  S.mono h hst

/-- **Lemma 2, FIFO/causality discharge** (p. 7): sampled at a tree date `t`, the FIFO
constraint `F (h+1) t ≤ F h t` (output below input through node `h`) holds — directly property
2.  In the MILP the FIFO constraint reads `F_p^j t' = F_p^{succ(j)} t` for `t' = FIFO^j(t)`;
its causal `≤` content is exactly this. -/
theorem sample_fifo (S : Scenario N) (h : Fin N) (t : ℝ≥0) :
    S.F h.succ t ≤ S.F h.castSucc t :=
  S.causal h t

/-- **Lemma 2, objective discharge** (p. 7): the sampled point's objective `t₁ − t₀` equals the
scenario's realized delay `d = tExit − tIn` by definition — so the feasible point built from a
delay-`d` scenario has objective exactly `d` (the equality `t₁ − t₀ = d` of Lemma 2). -/
theorem sample_objective (S : Scenario N) (tIn tExit : ℝ≥0) :
    S.realizedDelay tIn tExit = (tExit : ℝ) - (tIn : ℝ) :=
  rfl

/-- **Lemma 2, packaged pointwise feasibility** (p. 7): every MILP constraint that is a
*pointwise* property of the cumulative functions — arrival, monotonicity, FIFO/causality — is
discharged by a real scenario, simultaneously, with the objective equal to the realized delay.
This is the content of Lemma 2 once the tree dates are fixed (the date construction via Lemma 1
is the remaining recursive step, scoped below). -/
theorem sample_feasible_pointwise (S : Scenario N) (tIn tExit : ℝ≥0) :
    (∀ s t : ℝ≥0, s ≤ t → S.F 0 t - S.F 0 s ≤ S.α (t - s)) ∧
    (∀ (h : Fin (N + 1)) (s t : ℝ≥0), s ≤ t → S.F h s ≤ S.F h t) ∧
    (∀ (h : Fin N) (t : ℝ≥0), S.F h.succ t ≤ S.F h.castSucc t) ∧
    S.realizedDelay tIn tExit = (tExit : ℝ) - (tIn : ℝ) :=
  ⟨fun _ _ => S.arr _ _, fun h _ _ hst => S.mono h hst, fun h _ => S.causal h _, rfl⟩

end Scenario

/-! ## (3) Lemma 3: solution → scenario, the reconstruction core (p. 8)

"For any solution of (∗) such that `t₁ − t₀ = d`, there exists a scenario of the system where
the bit that leaves at `t₁` has a delay at least equal to `d`." (p. 7).  The proof *constructs*
admissible cumulative functions from the feasible solution by **extrapolation**: for the
starting node `j = fr(p)`, given the sampled values `F_p^j(t_k)` at the (finitely many) tree
dates `t_k`, the paper sets (p. 8, citing [8, Lemma 2])

  `F_p^j(t) = min{ F_p^j(t_k) + α_p(t − t_k) | t ≥ t_k }`

(plus a floor term to keep it nondecreasing, discussed below).  This is the **least**
`α_p`-upper-constrained function passing through the samples — exactly scenario property 3.

We formalize this extrapolation `extrapolate α v K` over a finite sample set `K : Finset ℝ≥0`
of dates with values `v : ℝ≥0 → ℝ≥0`, and prove the two properties it is designed to give:

* it is **`α`-upper-constrained** when `α` is sub-additive (`extrapolate_arrival`) — scenario
  property 3, the genuine content of the extrapolation;
* it is **wide-sense increasing** across any window where the qualifying sample set is fixed
  (`extrapolate_mono_of_filter_eq`, e.g. beyond the last sample date) — the part of scenario
  property 1 the burst extrapolation gives unconditionally;
* it lies **below the burst bound at every sample** (`extrapolate_le_at_sample`).

The residual content of the full Lemma 3 — *global* left-continuity and monotonicity (the
paper's second floor term `min{F(t_k)}` and the discontinuity handling of §IV.A), and
**FIFO-order preservation across the exponentially many Boolean orderings** — is the genuinely
new existence argument and is adjudicated precisely at the end (it is not a closed form). -/

/-- **The min-plus extrapolation** of a feasible solution (p. 8, [8, Lemma 2]): from sample
values `v t_k` at finitely many dates `t_k ∈ K`, the least `α`-upper-constrained function
through the samples, `extrapolate α v K t = min{ v t_k + α(t − t_k) | t_k ∈ K, t_k ≤ t }`.
This is how Lemma 3 rebuilds an admissible cumulative function from a feasible MILP point.
Requires the qualifying set `{t_k ∈ K | t_k ≤ t}` nonempty (`h`); `extrapolate_nonempty`
supplies it once `0 ∈ K`. -/
noncomputable def extrapolate (α v : ℝ≥0 → ℝ≥0) (K : Finset ℝ≥0) (t : ℝ≥0)
    (h : (K.filter (· ≤ t)).Nonempty) : ℝ≥0 :=
  (K.filter (· ≤ t)).inf' h (fun s => v s + α (t - s))

/-- The qualifying sample set `{t_k ∈ K | t_k ≤ t}` is nonempty whenever `0 ∈ K` (since
`0 ≤ t` always on `ℝ≥0`) — so `extrapolate α v K t` is defined at every time `t`.  The
ingress date `0` is always a sample of the trace. -/
theorem extrapolate_nonempty {K : Finset ℝ≥0} (h0 : (0 : ℝ≥0) ∈ K) (t : ℝ≥0) :
    (K.filter (· ≤ t)).Nonempty :=
  ⟨0, by rw [Finset.mem_filter]; exact ⟨h0, bot_le⟩⟩

/-- **Lemma 3, the extrapolation is `α`-upper-constrained** (p. 8, scenario property 3): for a
sub-additive arrival curve `α` and `s ≤ t`, the extrapolated cumulative satisfies
`extrapolate t ≤ extrapolate s + α(t − s)`, i.e. `F(t) − F(s) ≤ α(t − s)`.  This is the property
the min-plus extrapolation is built to guarantee — the reconstructed function inherits the
flow's arrival constraint.  Proof: the `s`-minimizer date `u ≤ s ≤ t` also bounds
`extrapolate t ≤ v u + α(t − u) ≤ v u + α(s − u) + α(t − s)` by sub-additivity. -/
theorem extrapolate_arrival {α : ℝ≥0 → ℝ≥0} (hsub : ∀ a b : ℝ≥0, α (a + b) ≤ α a + α b)
    {v : ℝ≥0 → ℝ≥0} {K : Finset ℝ≥0} {s t : ℝ≥0} (hst : s ≤ t)
    (hs : (K.filter (· ≤ s)).Nonempty) (ht : (K.filter (· ≤ t)).Nonempty) :
    extrapolate α v K t ht ≤ extrapolate α v K s hs + α (t - s) := by
  obtain ⟨u, hu, hmin⟩ := Finset.exists_mem_eq_inf' hs (fun s' => v s' + α (s - s'))
  rw [show extrapolate α v K s hs = v u + α (s - u) from hmin]
  rw [Finset.mem_filter] at hu
  obtain ⟨huK, hus⟩ := hu
  have h1 : extrapolate α v K t ht ≤ v u + α (t - u) :=
    Finset.inf'_le _ (by rw [Finset.mem_filter]; exact ⟨huK, le_trans hus hst⟩)
  refine le_trans h1 ?_
  rw [show t - u = (t - s) + (s - u) from by rw [tsub_add_tsub_cancel hst hus]]
  calc v u + α ((t - s) + (s - u))
      ≤ v u + (α (t - s) + α (s - u)) := by gcongr; exact hsub (t - s) (s - u)
    _ = (v u + α (s - u)) + α (t - s) := by ring

/-- **Lemma 3, the extrapolation is wide-sense increasing where the sample set is fixed**
(part of scenario property 1, p. 8): for monotone `α` and `s ≤ t` with the *same* qualifying
sample set (`K.filter (· ≤ s) = K.filter (· ≤ t)`, e.g. both beyond the last sample date),
`extrapolate s ≤ extrapolate t`.  On such a window each shifted term grows (`α(s−u) ≤ α(t−u)`),
so the min grows.  The *global* monotonicity (across sample boundaries) needs the paper's floor
term and is scoped below. -/
theorem extrapolate_mono_of_filter_eq {α : ℝ≥0 → ℝ≥0} (hmono : Monotone α)
    {v : ℝ≥0 → ℝ≥0} {K : Finset ℝ≥0} {s t : ℝ≥0} (hst : s ≤ t)
    (hsame : K.filter (· ≤ s) = K.filter (· ≤ t))
    (hs : (K.filter (· ≤ s)).Nonempty) (ht : (K.filter (· ≤ t)).Nonempty) :
    extrapolate α v K s hs ≤ extrapolate α v K t ht := by
  rw [extrapolate, extrapolate]
  apply Finset.le_inf'
  intro u hu
  have hu' : u ∈ K.filter (· ≤ s) := by rw [hsame]; exact hu
  have hule : v u + α (s - u) ≤ v u + α (t - u) := by
    gcongr; exact hmono (tsub_le_tsub_right hst u)
  exact le_trans (Finset.inf'_le _ hu') hule

/-- **Lemma 3, the extrapolation respects the burst bound at each sample** (p. 8): at a sample
date `t ∈ K`, `extrapolate α v K t ≤ v t + α 0` — the reconstructed value never exceeds the
solution's value there plus the zero-shift slack.  When `α 0 = 0` this gives
`extrapolate t ≤ v t`: the extrapolation lies on or below the committed sample values, so it
agrees with them up to the arrival slack (the extrapolation is the *least* such function). -/
theorem extrapolate_le_at_sample {α v : ℝ≥0 → ℝ≥0} {K : Finset ℝ≥0} {t : ℝ≥0} (htK : t ∈ K)
    (ht : (K.filter (· ≤ t)).Nonempty) :
    extrapolate α v K t ht ≤ v t + α 0 := by
  have h : extrapolate α v K t ht ≤ v t + α (t - t) :=
    Finset.inf'_le _ (by rw [Finset.mem_filter]; exact ⟨htK, le_refl t⟩)
  rwa [tsub_self] at h

/-- **Lemma 3, the single-sample base case** (the affine arrival-curve reconstruction): from
one committed ingress value `v 0` at date `0`, the extrapolation is exactly the burst curve
`extrapolate α v {0} t = v 0 + α t` — the least cumulative function through `(0, v 0)` with
arrival curve `α`.  This is the base of the backward reconstruction (the starting node
`fr(p)`): a leaky-bucket-shaped ingress trajectory realizing the solution's ingress value. -/
theorem extrapolate_singleton {α v : ℝ≥0 → ℝ≥0} {t : ℝ≥0}
    (ht : (({0} : Finset ℝ≥0).filter (· ≤ t)).Nonempty) :
    extrapolate α v {0} t ht = v 0 + α t := by
  have hfilt : ({0} : Finset ℝ≥0).filter (· ≤ t) = {0} := by
    ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, hx ▸ bot_le⟩⟩
  rw [extrapolate, Finset.inf'_congr ht hfilt (g := fun s => v s + α (t - s)) (fun _ _ => rfl)]
  simp [tsub_zero]

/-! ## Scoping: what the full Lemmas 2/3 still need (beyond this file)

This file builds the concrete §IV.C layer that `FifoFeedForwardExact`'s abstract bridge
abstracts over, and discharges the parts of Lemmas 2 and 3 that close.  What remains — the
genuinely exponential/existence content the paper writes down and a solver evaluates — is:

* **Lemma 2, the backward date construction (p. 7).**  We discharge every *pointwise* MILP
  constraint of a sampled scenario (`sample_feasible_pointwise`); what is scoped is the
  recursive construction of the tree *dates* themselves — `t₂ = FIFO^N(t₁)`, `t₃ = SC^N(t₁)`,
  and the backward recursion via **Lemma 1** (the convolution-time existence: for the exit date
  `t₁` there is a service date `t₃` with `D^N(t₁) ≥ A^N(t₃) + β^N(t₁ − t₃)`).  Building these is
  the recursion over the `DateTree`, an `[infra]` step (Lemma 1's date-existence is not yet a
  Lean lemma over the served pair); faithful, but not a closed form.

* **Lemma 3, global monotonicity and left-continuity (p. 8).**  `extrapolate_arrival` gives
  scenario property 3 and `extrapolate_mono_of_filter_eq` gives monotonicity on each fixed-sample
  window; the *global* wide-sense increase across sample boundaries needs the paper's second
  floor term `min{F_p^j(t_k) | t ≥ t_k}` and the discontinuity handling of §IV.A
  (`F_p^{fr(p)}(t_k^+) ≥ max ...`), and left-continuity is asserted of the resulting function.
  These are `[infra]` (the floor-augmented extrapolation and its left-continuity).

* **Lemma 3, FIFO-order preservation across the Boolean orderings (p. 8).**  The hardest part:
  the extrapolated cumulatives at *different* nodes must jointly preserve the FIFO service order
  for *every* path, which holds because `FIFO^j(t_k)` does not depend on `p`.  Establishing this
  for an arbitrary feasible point requires reasoning over the (exponentially many) Boolean
  orderings the solution fixes — the `[research]`/`[infra]` existence argument with no closed
  form (contrast the single FIFO node, `fifoNode_worstCaseDelay_eq`, whose optimum *is* the
  closed form `T + (b₁+b₂)/R`).

So: the abstract Theorem 1 and §IV.D bracketing are formalized in full generality
(`FifoFeedForwardExact`); the concrete tree layout, Lemma 2's pointwise discharges, and Lemma
3's extrapolation core are here; the residual date-recursion / floor-augmentation /
order-preservation is the exponential construction the paper writes down and a solver
evaluates, scoped as `[infra]`/`[research]`. -/

/-! ## Restatements (the declarations say what [BOU 16b] §IV.C says) -/

/-- p. 6–7: the §IV.C date layout is a full binary tree of depth `N` with `2^(N+1)−1` dates. -/
example {N : ℕ} (t : DateTree N) : t.count = 2 ^ (N + 1) - 1 := DateTree.count_eq t

-- A single-node (depth-1) date tree has the `3` dates `t₁, t₂, t₃` of the base case.
example : (DateTree.node 5 (DateTree.leaf 2) (DateTree.leaf 1)).count = 3 := rfl

-- A two-node (depth-2) date tree has the `7` dates `t₁,…,t₇` of the Fig. 5 example.
example :
    (DateTree.node (N := 1) 5 (DateTree.node 4 (DateTree.leaf 2) (DateTree.leaf 1))
      (DateTree.node 3 (DateTree.leaf 0) (DateTree.leaf 0))).count = 7 := rfl

/-- Lemma 3 (p. 8), single-sample base case: the extrapolation from one ingress sample is the
affine burst curve `v 0 + α t`. -/
example {α v : ℝ≥0 → ℝ≥0} {t : ℝ≥0}
    (ht : (({0} : Finset ℝ≥0).filter (· ≤ t)).Nonempty) :
    extrapolate α v {0} t ht = v 0 + α t :=
  extrapolate_singleton ht

/-- Lemma 2 (p. 7), pointwise discharges: a real scenario sampled at the tree dates satisfies
the arrival, monotonicity, and FIFO/causality MILP constraints, with objective the delay. -/
example {N : ℕ} (S : Scenario N) (tIn tExit : ℝ≥0) :
    (∀ s t : ℝ≥0, s ≤ t → S.F 0 t - S.F 0 s ≤ S.α (t - s)) ∧
    (∀ (h : Fin (N + 1)) (s t : ℝ≥0), s ≤ t → S.F h s ≤ S.F h t) ∧
    (∀ (h : Fin N) (t : ℝ≥0), S.F h.succ t ≤ S.F h.castSucc t) ∧
    S.realizedDelay tIn tExit = (tExit : ℝ) - (tIn : ℝ) :=
  S.sample_feasible_pointwise tIn tExit

/-- Lemma 3 (p. 8), extrapolation core: the min-plus extrapolation of a feasible solution is
`α`-upper-constrained (scenario property 3) for sub-additive `α`. -/
example {α : ℝ≥0 → ℝ≥0} (hsub : ∀ a b : ℝ≥0, α (a + b) ≤ α a + α b)
    {v : ℝ≥0 → ℝ≥0} {K : Finset ℝ≥0} {s t : ℝ≥0} (hst : s ≤ t)
    (hs : (K.filter (· ≤ s)).Nonempty) (ht : (K.filter (· ≤ t)).Nonempty) :
    extrapolate α v K t ht ≤ extrapolate α v K s hs + α (t - s) :=
  extrapolate_arrival hsub hst hs ht

end FifoFeedForward

end DeepWiki
