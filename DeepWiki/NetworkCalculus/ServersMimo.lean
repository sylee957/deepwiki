import DeepWiki.NetworkCalculus.Servers
import DeepWiki.NetworkCalculus.ServersBacklog

/-! # MIMO servers
A MIMO (`n`-)server relates a vector of input cumulative processes to a
vector of outputs, causally per flow. Two reductions return the analysis
to single-flow servers: the **aggregate server** relates the summed
input to the summed output, and the **residual server** for flow `i`
projects the relation onto coordinate `i` (the other flows are the
cross-traffic). A residual server of a deterministic MIMO server can be
non-deterministic — the book's reason for the relational server model.
Aggregate/residual *service curves* of a MIMO server are, by definition,
service curves of its aggregate/residual servers. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- An `n`-server relation is causal per flow: each output never exceeds
its own input, `S A D → D i ≤ A i`. -/
def IsCausalN {ι : Type*} (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ A D, S A D → ∀ i, D i ≤ A i

/-- An `n`-server relation is left-total: every input vector has an
output vector. -/
def IsLeftTotalN {ι : Type*} (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ A, ∃ D, S A D

/-- **MIMO (`n`-)server**: a per-flow causal, left-total relation between
input and output vectors of cumulative processes. -/
def IsServerN {ι : Type*} (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  IsCausalN S ∧ IsLeftTotalN S

/-- The **aggregate server** of an `n`-server: it relates the summed
input to the summed output. -/
def aggregateServer {ι : Type*} [Fintype ι]
    (S : (ι → Curve) → (ι → Curve) → Prop) : Curve → Curve → Prop :=
  fun A D => ∃ As Ds, S As Ds ∧ A = ∑ i, As i ∧ D = ∑ i, Ds i

/-- The **residual server** of an `n`-server for flow `i`: the projection
of the relation onto the `i`-th coordinate. -/
def residualServer {ι : Type*}
    (S : (ι → Curve) → (ι → Curve) → Prop) (i : ι) :
    Curve → Curve → Prop :=
  fun A D => ∃ As Ds, S As Ds ∧ As i = A ∧ Ds i = D

/-- Intro: an `n`-server pair aggregates into an aggregate-server pair. -/
theorem aggregateServer_sum {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {As Ds : ι → Curve}
    (hp : S As Ds) : aggregateServer S (∑ i, As i) (∑ i, Ds i) :=
  ⟨As, Ds, hp, rfl, rfl⟩

/-- The **`J`-restricted aggregate server**: like `aggregateServer`, but summing the input and
output vectors only over the flow set `J` (the flows present at a hop). -/
def aggregateServerOn {ι : Type*}
    (S : (ι → Curve) → (ι → Curve) → Prop) (J : Finset ι) :
    Curve → Curve → Prop :=
  fun A D => ∃ As Ds, S As Ds ∧ A = ∑ i ∈ J, As i ∧ D = ∑ i ∈ J, Ds i

/-- Intro: the `J`-aggregate of an `n`-server pair lies in the `J`-restricted aggregate server. -/
theorem aggregateServerOn_sum {ι : Type*}
    {S : (ι → Curve) → (ι → Curve) → Prop} {J : Finset ι} {As Ds : ι → Curve}
    (hp : S As Ds) : aggregateServerOn S J (∑ i ∈ J, As i) (∑ i ∈ J, Ds i) :=
  ⟨As, Ds, hp, rfl, rfl⟩

/-- Intro: an `n`-server pair projects onto a residual-server pair. -/
theorem residualServer_apply {ι : Type*}
    {S : (ι → Curve) → (ι → Curve) → Prop} {As Ds : ι → Curve}
    (hp : S As Ds) (i : ι) : residualServer S i (As i) (Ds i) :=
  ⟨As, Ds, hp, rfl, rfl⟩

/-- **The aggregate of an `n`-server is a server**: causality sums, and
an input decomposes by loading it onto one flow. -/
theorem isServer_aggregateServer {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} (hS : IsServerN S) :
    IsServer (aggregateServer S) := by
  constructor
  · rintro A D ⟨As, Ds, hp, rfl, rfl⟩ t
    rw [Curve.sum_apply, Curve.sum_apply]
    exact Finset.sum_le_sum fun i _ => hS.1 As Ds hp i t
  · intro A
    obtain ⟨j⟩ := ‹Nonempty ι›
    obtain ⟨Ds, hDs⟩ := hS.2 (Pi.single j A)
    refine ⟨∑ i, Ds i, Pi.single j A, Ds, hDs, ?_, rfl⟩
    refine Curve.ext fun t => ?_
    rw [Curve.sum_apply]
    simp [Pi.single_apply, apply_ite (fun B : Curve => B t)]

/-- An aggregate backlog instant disaggregates: at each backlogged
instant of the aggregate pair some flow is backlogged, and conversely
(for causal families). -/
theorem isBacklogged_sum_iff {ι : Type*} [Fintype ι]
    {A D : ι → ℝ≥0 → ℝ≥0} (hc : ∀ j x, D j x ≤ A j x) {I : Set ℝ≥0} :
    IsBacklogged (fun x => ∑ j, A j x) (fun x => ∑ j, D j x) I
      ↔ ∀ u ∈ I, ∃ i, D i u < A i u := by
  constructor
  · intro h u hu
    by_contra hcon
    push Not at hcon
    exact absurd (h u hu)
      (not_lt.mpr (Finset.sum_le_sum fun j _ => hcon j))
  · intro h u hu
    obtain ⟨i, hi⟩ := h u hu
    exact Finset.sum_lt_sum (fun j _ => hc j u) ⟨i, Finset.mem_univ i, hi⟩

/-- A backlogged period for one flow is a backlogged period for any
aggregate containing it (for causal families). -/
theorem isBacklogged_sum_of_isBacklogged {ι : Type*} {s : Finset ι}
    {A D : ι → ℝ≥0 → ℝ≥0} (hc : ∀ j ∈ s, ∀ x, D j x ≤ A j x) {I : Set ℝ≥0}
    {i : ι} (hi : i ∈ s) (hbl : IsBacklogged (A i) (D i) I) :
    IsBacklogged (fun x => ∑ j ∈ s, A j x) (fun x => ∑ j ∈ s, D j x) I :=
  fun u hu =>
    Finset.sum_lt_sum (fun j hj => hc j hj u) ⟨i, hi, hbl u hu⟩

/-- A backlogged period of a sub-aggregate is one of any larger
aggregate (for causal families): the extra flows only add slack. -/
theorem isBacklogged_sum_of_isBacklogged_subset {ι : Type*}
    {s s' : Finset ι} {A D : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ j ∈ s', ∀ x, D j x ≤ A j x) (hsub : s ⊆ s') {I : Set ℝ≥0}
    (hbl : IsBacklogged (fun x => ∑ j ∈ s, A j x)
      (fun x => ∑ j ∈ s, D j x) I) :
    IsBacklogged (fun x => ∑ j ∈ s', A j x)
      (fun x => ∑ j ∈ s', D j x) I := by
  intro u hu
  show (∑ j ∈ s', D j u) < ∑ j ∈ s', A j u
  rw [← Finset.sum_sdiff hsub, ← Finset.sum_sdiff (f := fun j => A j u) hsub]
  exact add_lt_add_of_le_of_lt
    (Finset.sum_le_sum fun j hj => hc j (Finset.mem_sdiff.mp hj).1 u)
    (hbl u hu)

/-- **Per-flow equality at the start of an aggregate backlogged period**:
at `start (∑ Aⱼ) (∑ Dⱼ) t` every flow has served exactly its arrivals
(for causal, left-continuous, null-at-origin families). -/
theorem apply_start_sum_eq {ι : Type*} [Fintype ι]
    {A D : ι → ℝ≥0 → ℝ≥0} (hc : ∀ j x, D j x ≤ A j x)
    (hAlc : ∀ j, IsLeftContinuous (A j)) (hDlc : ∀ j, IsLeftContinuous (D j))
    (h0 : ∀ j, A j 0 = D j 0) (t : ℝ≥0) (i : ι) :
    D i (start (fun x => ∑ j, A j x) (fun x => ∑ j, D j x) t)
      = A i (start (fun x => ∑ j, A j x) (fun x => ∑ j, D j x) t) := by
  set s₀ := start (fun x => ∑ j, A j x) (fun x => ∑ j, D j x) t
  have haggeq : (∑ j, A j s₀) = ∑ j, D j s₀ :=
    apply_start_eq
      (isLeftContinuous_sum _ fun j _ => hAlc j)
      (isLeftContinuous_sum _ fun j _ => hDlc j)
      (by show (∑ j, A j 0) = ∑ j, D j 0
          exact Finset.sum_congr rfl fun j _ => h0 j)
      (fun x => Finset.sum_le_sum fun j _ => hc j x) t
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hc j s₀)).mp haggeq.symm i
    (Finset.mem_univ i)

/-- **Restricted-aggregate start-equality**: `apply_start_sum_eq` over an arbitrary flow set
`s'` rather than `univ`. At the start of the `s'`-aggregate's backlogged period, every member
`i ∈ s'` is fully served, `Dᵢ(start) = Aᵢ(start)`. -/
theorem apply_start_sum_finset_eq {ι : Type*}
    {A D : ι → ℝ≥0 → ℝ≥0} (s' : Finset ι) (hc : ∀ j x, D j x ≤ A j x)
    (hAlc : ∀ j, IsLeftContinuous (A j)) (hDlc : ∀ j, IsLeftContinuous (D j))
    (h0 : ∀ j, A j 0 = D j 0) (t : ℝ≥0) {i : ι} (hi : i ∈ s') :
    D i (start (fun x => ∑ j ∈ s', A j x) (fun x => ∑ j ∈ s', D j x) t)
      = A i (start (fun x => ∑ j ∈ s', A j x) (fun x => ∑ j ∈ s', D j x) t) := by
  set s₀ := start (fun x => ∑ j ∈ s', A j x) (fun x => ∑ j ∈ s', D j x) t
  have haggeq : (∑ j ∈ s', A j s₀) = ∑ j ∈ s', D j s₀ :=
    apply_start_eq
      (isLeftContinuous_sum _ fun j _ => hAlc j)
      (isLeftContinuous_sum _ fun j _ => hDlc j)
      (by show (∑ j ∈ s', A j 0) = ∑ j ∈ s', D j 0
          exact Finset.sum_congr rfl fun j _ => h0 j)
      (fun x => Finset.sum_le_sum fun j _ => hc j x) t
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hc j s₀)).mp haggeq.symm i hi

/-- `apply_start_sum_eq` with `Curve` bundles: causality alone remains,
the regularity hypotheses discharge from the curve fields. -/
theorem Curve.apply_start_sum_eq {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} (hc : ∀ j, Ds j ≤ As j) (t : ℝ≥0) (i : ι) :
    (Ds i) (start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t)
      = (As i) (start (fun x => ∑ j, (As j) x)
          (fun x => ∑ j, (Ds j) x) t) :=
  _root_.DeepWiki.apply_start_sum_eq (fun j x => hc j x)
    (fun j => (As j).leftCont) (fun j => (Ds j).leftCont)
    (fun j => ((As j).zero : (As j) 0 = 0).trans
      ((Ds j).zero : (Ds j) 0 = 0).symm) t i

/-- **Each residual of an `n`-server is a server**: causality projects,
and an input extends to the constant vector. -/
theorem isServer_residualServer {ι : Type*}
    {S : (ι → Curve) → (ι → Curve) → Prop} (hS : IsServerN S) (i : ι) :
    IsServer (residualServer S i) := by
  constructor
  · rintro A D ⟨As, Ds, hp, rfl, rfl⟩
    exact hS.1 As Ds hp i
  · intro A
    obtain ⟨Ds, hDs⟩ := hS.2 (fun _ => A)
    exact ⟨Ds i, fun _ => A, Ds, hDs, rfl, rfl⟩

end DeepWiki
