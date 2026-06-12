import Book.Servers

/-! # MIMO servers
A MIMO (`n`-)server relates a vector of input cumulative processes to a
vector of outputs, causally per flow. Two reductions return the analysis
to single-flow servers: the **aggregate server** relates the summed
input to the summed output, and the **residual server** for flow `i`
projects the relation onto coordinate `i` (the other flows are the
cross-traffic). A residual server of a deterministic MIMO server is in
general non-deterministic — the relational server model is essential.
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
