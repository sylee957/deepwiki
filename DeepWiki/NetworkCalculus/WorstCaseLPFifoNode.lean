import DeepWiki.NetworkCalculus.WorstCaseLP

/-! # The single-node FIFO linear program (Table 11.2)
The explicit finite linear program of §11.2.1 for the worst-case delay of one FIFO server
crossed by two token-bucket flows `γ_{bᵢ,rᵢ}` under a rate-latency service curve `β_{R,T}`.
Variables are the dates `t₁ ≥ t₂ ≥ t₃` and the cumulative-function values `Aᵢ`, `Dᵢ` sampled at
them; the constraints are the network-calculus ones (monotonicity, arrival, service) plus the
FIFO coupling `Dᵢ(t₁) = Aᵢ(t₂)`. Unlike the general tandem MILP this base case has *no* Boolean
variables, and its optimum is computed here directly: `programOptimum = T + (b₁+b₂)/R`, the
worst-case FIFO delay of the aggregate. Both bounds are pure linear arithmetic on the program
variables — the `≤` bound from the constraints, the `≥` from an explicit feasible point. -/

namespace DeepWiki

open scoped NNReal

/-- The variables of the single-node FIFO program: the dates `t₁,t₂,t₃` and the sampled
cumulative-function values `Aᵢ(tⱼ)` (arrivals) and `Dᵢ(t₁)` (departures) of the two flows. -/
structure FifoNodeVars where
  t₁ : ℝ
  t₂ : ℝ
  t₃ : ℝ
  A₁t₁ : ℝ
  A₁t₂ : ℝ
  A₁t₃ : ℝ
  A₂t₁ : ℝ
  A₂t₂ : ℝ
  A₂t₃ : ℝ
  D₁t₁ : ℝ
  D₂t₁ : ℝ

/-- **The feasible set of Table 11.2** for token-bucket flows `γ_{bᵢ,rᵢ}` and a rate-latency
server `β_{R,T}`: the date ordering, the per-flow monotonicity and arrival (`α`) constraints,
the aggregate service (`β`) constraint, and the FIFO coupling `Dᵢ(t₁) = Aᵢ(t₂)`. -/
def FifoNodeFeasible (b₁ b₂ r₁ r₂ R T : ℝ) (v : FifoNodeVars) : Prop :=
  v.t₂ ≤ v.t₁ ∧ v.t₃ ≤ v.t₂ ∧
  v.A₁t₂ ≤ v.A₁t₁ ∧ v.A₂t₂ ≤ v.A₂t₁ ∧
  v.A₁t₂ - v.A₁t₃ ≤ b₁ + r₁ * (v.t₂ - v.t₃) ∧
  v.A₂t₂ - v.A₂t₃ ≤ b₂ + r₂ * (v.t₂ - v.t₃) ∧
  v.A₁t₃ + v.A₂t₃ + R * v.t₁ - R * v.t₃ - R * T ≤ v.D₁t₁ + v.D₂t₁ ∧
  v.D₁t₁ = v.A₁t₂ ∧ v.D₂t₁ = v.A₂t₂

/-- The program's objective: the delay `t₁ − t₂` of the bit of flow 1 departing at `t₁` (which,
by FIFO, arrived at `t₂`). -/
def fifoNodeDelay (v : FifoNodeVars) : ℝ := v.t₁ - v.t₂

/-- **Upper bound (Table 11.2 `≤`).** Under stability `r₁ + r₂ ≤ R`, every feasible point's
delay is at most `T + (b₁+b₂)/R`: the service-curve constraint forces the aggregate departure to
catch up, and the arrival constraint caps the backlog at the aggregate burst `b₁+b₂`. -/
theorem fifoNodeDelay_le {b₁ b₂ r₁ r₂ R T : ℝ} (hR : 0 < R) (hstab : r₁ + r₂ ≤ R)
    {v : FifoNodeVars} (hv : FifoNodeFeasible b₁ b₂ r₁ r₂ R T v) :
    fifoNodeDelay v ≤ T + (b₁ + b₂) / R := by
  obtain ⟨ht₁, ht₂, _, _, harr₁, harr₂, hserv, hfifo₁, hfifo₂⟩ := hv
  have hd : R * fifoNodeDelay v ≤ R * T + (b₁ + b₂) := by
    rw [fifoNodeDelay]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ R - (r₁ + r₂)) (by linarith : (0:ℝ) ≤ v.t₂ - v.t₃),
      harr₁, harr₂, hserv, hfifo₁, hfifo₂]
  have hdiv : fifoNodeDelay v ≤ (R * T + (b₁ + b₂)) / R :=
    (le_div_iff₀ hR).mpr (by linarith [hd, mul_comm R (fifoNodeDelay v)])
  calc fifoNodeDelay v ≤ (R * T + (b₁ + b₂)) / R := hdiv
    _ = T + (b₁ + b₂) / R := by
        rw [add_div]; congr 1; rw [mul_comm R T, mul_div_assoc, div_self hR.ne', mul_one]

/-- An explicit feasible point attaining the bound: the aggregate burst `b₁+b₂` arrives at
`t₂ = t₃ = 0` and clears at rate `R` after latency `T`, so the tagged bit departs at
`t₁ = T + (b₁+b₂)/R`. -/
noncomputable def fifoNodeWitness (b₁ b₂ R T : ℝ) : FifoNodeVars where
  t₁ := T + (b₁ + b₂) / R
  t₂ := 0
  t₃ := 0
  A₁t₁ := b₁
  A₁t₂ := b₁
  A₁t₃ := 0
  A₂t₁ := b₂
  A₂t₂ := b₂
  A₂t₃ := 0
  D₁t₁ := b₁
  D₂t₁ := b₂

/-- The witness point is feasible (for nonnegative burst, latency, and positive rate). -/
theorem fifoNodeFeasible_witness {b₁ b₂ r₁ r₂ R T : ℝ} (hR : 0 < R)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hT : 0 ≤ T) :
    FifoNodeFeasible b₁ b₂ r₁ r₂ R T (fifoNodeWitness b₁ b₂ R T) := by
  have hmul : R * (T + (b₁ + b₂) / R) = R * T + (b₁ + b₂) := by
    rw [mul_add, mul_div_cancel₀ _ hR.ne']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩ <;> simp only [fifoNodeWitness] <;>
    nlinarith [hmul, hT, hb₁, hb₂, div_nonneg (show (0:ℝ) ≤ b₁ + b₂ by linarith) hR.le]

/-- The objective at the witness is exactly the bound. -/
theorem fifoNodeDelay_witness (b₁ b₂ R T : ℝ) :
    fifoNodeDelay (fifoNodeWitness b₁ b₂ R T) = T + (b₁ + b₂) / R := by
  simp [fifoNodeDelay, fifoNodeWitness]

/-- **Theorem 11.2, single FIFO node (Table 11.2): the program optimum is the worst-case delay.**
For two token-bucket flows `γ_{bᵢ,rᵢ}` through a rate-latency FIFO server `β_{R,T}` with
`r₁+r₂ ≤ R`, the optimum of the delay program is `T + (b₁+b₂)/R` — the upper bound holds on every
feasible point and the explicit witness attains it, so the finite LP computes the exact worst-case
FIFO delay. -/
theorem fifoNode_programOptimum {b₁ b₂ r₁ r₂ R T : ℝ} (hR : 0 < R) (hstab : r₁ + r₂ ≤ R)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hT : 0 ≤ T) :
    programOptimum (FifoNodeFeasible b₁ b₂ r₁ r₂ R T) (fun v => ((fifoNodeDelay v : ℝ) : EReal))
      = ((T + (b₁ + b₂) / R : ℝ) : EReal) := by
  apply le_antisymm
  · exact programOptimum_le fun v hv => by exact_mod_cast fifoNodeDelay_le hR hstab hv
  · have h := le_programOptimum (Feasible := FifoNodeFeasible b₁ b₂ r₁ r₂ R T)
      (obj := fun v => ((fifoNodeDelay v : ℝ) : EReal)) (fifoNodeFeasible_witness hR hb₁ hb₂ hT)
    simp only [fifoNodeDelay_witness] at h
    exact h

end DeepWiki
