import DeepWiki.NetworkCalculus.WorstCaseLP

/-! # The single-node arbitrary-multiplexing linear program (Table 11.1, n = 1)
The explicit finite linear program of §11.1 for the worst-case delay of a *tagged* flow 1
(token-bucket `γ_{b₁,r₁}`) sharing one strict rate-latency server `β_{R,T}` with a cross flow 2
(`γ_{b₂,r₂}`) under **arbitrary (blind) multiplexing**. Variables: the dates `t₀ ≤ u ≤ t₁` (start
of the backlogged period, arrival of the tagged bit, its departure) and the sampled cumulative
values `Aᵢ`, `Dᵢ`. Unlike the FIFO node there is no FIFO coupling — instead the tagged bit may be
served behind all the cross traffic, so the optimum is the residual-service delay
`(R·T + b₁ + b₂)/(R − r₂)`, not the FIFO `T + (b₁+b₂)/R`. Both bounds are linear arithmetic on the
program variables (the `≤` from the constraints, the `≥` from an explicit feasible point). -/

namespace DeepWiki

open scoped NNReal

/-- The variables of the single-node arbitrary-multiplexing program (Table 11.1, n = 1): the
dates `t₀ ≤ u ≤ t₁` and the sampled arrival values `Aᵢ` and departure values `Dᵢ`, with `A₁u` the
arrival cumulative of the tagged flow at the bit-of-interest's arrival date `u`. -/
structure ArbMuxNodeVars where
  t₀ : ℝ
  u : ℝ
  t₁ : ℝ
  A₁t₀ : ℝ
  A₁u : ℝ
  A₁t₁ : ℝ
  A₂t₀ : ℝ
  A₂t₁ : ℝ
  D₁t₀ : ℝ
  D₁t₁ : ℝ
  D₂t₀ : ℝ
  D₂t₁ : ℝ

/-- **The feasible set of the single-node arbitrary-multiplexing LP** (Table 11.1, n = 1): the
date/insertion ordering, monotonicity, the backlogged-period start (`Aᵢ(t₀)=Dᵢ(t₀)`), causality
(`Dᵢ ≤ Aᵢ` at `t₁`), per-flow arrival, the aggregate strict-service constraint, and the
`u`-insertion bound placing the tagged bit's departure level at its arrival cumulative. -/
def ArbMuxNodeFeasible (b₁ b₂ r₁ r₂ R T : ℝ) (v : ArbMuxNodeVars) : Prop :=
  v.t₀ ≤ v.u ∧ v.u ≤ v.t₁ ∧
  v.A₁t₀ ≤ v.A₁t₁ ∧ v.A₂t₀ ≤ v.A₂t₁ ∧ v.A₁t₀ ≤ v.A₁u ∧ v.A₁u ≤ v.A₁t₁ ∧
  v.D₁t₀ ≤ v.D₁t₁ ∧ v.D₂t₀ ≤ v.D₂t₁ ∧
  v.A₁t₀ = v.D₁t₀ ∧ v.A₂t₀ = v.D₂t₀ ∧
  v.D₁t₁ ≤ v.A₁t₁ ∧ v.D₂t₁ ≤ v.A₂t₁ ∧
  v.A₁t₁ - v.A₁t₀ ≤ b₁ + r₁ * (v.t₁ - v.t₀) ∧
  v.A₂t₁ - v.A₂t₀ ≤ b₂ + r₂ * (v.t₁ - v.t₀) ∧
  v.D₁t₀ + v.D₂t₀ + R * (v.t₁ - v.t₀) - R * T ≤ v.D₁t₁ + v.D₂t₁ ∧
  v.D₁t₀ + v.D₂t₀ ≤ v.D₁t₁ + v.D₂t₁ ∧
  v.D₁t₁ ≤ v.A₁u ∧
  v.A₁u - v.A₁t₀ ≤ b₁ + r₁ * (v.u - v.t₀)

/-- The program's objective: the delay `t₁ − u` of the tagged bit (departing at `t₁`, arrived
at `u`). -/
def arbMuxNodeDelay (v : ArbMuxNodeVars) : ℝ := v.t₁ - v.u

/-- **Upper bound (blind-mux, `≤`).** With flow-1 residual stability `r₂ < R` and aggregate
stability `r₁+r₂ ≤ R`, every feasible point's delay is at most `(R·T+b₁+b₂)/(R−r₂)`: the
service constraint clears the aggregate, the cross flow can absorb service ahead of the tagged
bit (causality + arrival), and the `u`-insertion bound pins the tagged bit's level — the burst it
waits behind is the *aggregate* `b₁+b₂`, cleared at the residual rate `R−r₂`. -/
theorem arbMuxNodeDelay_le {b₁ b₂ r₁ r₂ R T : ℝ} (hRr₂ : r₂ < R) (hstab : r₁ + r₂ ≤ R)
    {v : ArbMuxNodeVars} (hv : ArbMuxNodeFeasible b₁ b₂ r₁ r₂ R T v) :
    arbMuxNodeDelay v ≤ (R * T + b₁ + b₂) / (R - r₂) := by
  obtain ⟨ht0u, _, _, _, _, _, _, _, hbk1, hbk2, _, hcaus2, _, harr2, hserv, _, hins1, hinsa⟩ := hv
  have hRr : (0:ℝ) < R - r₂ := by linarith
  have hkey : (R - r₂) * (v.t₁ - v.t₀) ≤ R * T + b₁ + b₂ + r₁ * (v.u - v.t₀) := by
    nlinarith [hbk1, hbk2, hcaus2, harr2, hserv, hins1, hinsa]
  have hslack : (0:ℝ) ≤ (R - r₁ - r₂) * (v.u - v.t₀) :=
    mul_nonneg (by linarith) (by linarith)
  have hd : (R - r₂) * (v.t₁ - v.u) ≤ R * T + b₁ + b₂ := by nlinarith [hkey, hslack]
  rw [arbMuxNodeDelay, le_div_iff₀ hRr]
  nlinarith [hd]

/-- An explicit feasible point attaining the bound: the aggregate burst arrives at the origin,
the cross flow saturates the service, and the tagged bit (arriving at `u = 0`) departs at
`t₁ = (R·T+b₁+b₂)/(R−r₂)` once the aggregate has cleared at the residual rate. -/
noncomputable def arbMuxNodeWitness (b₁ b₂ r₁ r₂ R T : ℝ) : ArbMuxNodeVars where
  t₀ := 0
  u := 0
  t₁ := (R * T + b₁ + b₂) / (R - r₂)
  A₁t₀ := 0
  A₁u := b₁
  A₁t₁ := b₁ + r₁ * ((R * T + b₁ + b₂) / (R - r₂))
  A₂t₀ := 0
  A₂t₁ := b₂ + r₂ * ((R * T + b₁ + b₂) / (R - r₂))
  D₁t₀ := 0
  D₁t₁ := b₁
  D₂t₀ := 0
  D₂t₁ := b₂ + r₂ * ((R * T + b₁ + b₂) / (R - r₂))

/-- The witness point is feasible (nonnegative bursts/rates/latency, residual stability `r₂<R`). -/
theorem arbMuxNodeFeasible_witness {b₁ b₂ r₁ r₂ R T : ℝ} (hRr₂ : r₂ < R)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hT : 0 ≤ T) :
    ArbMuxNodeFeasible b₁ b₂ r₁ r₂ R T (arbMuxNodeWitness b₁ b₂ r₁ r₂ R T) := by
  have hRr : (0:ℝ) < R - r₂ := by linarith
  have hR0 : (0:ℝ) ≤ R := by linarith
  have ht0 : (0:ℝ) ≤ (R * T + b₁ + b₂) / (R - r₂) :=
    div_nonneg (by positivity) hRr.le
  have hmul : (R - r₂) * ((R * T + b₁ + b₂) / (R - r₂)) = R * T + b₁ + b₂ :=
    mul_div_cancel₀ _ hRr.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [arbMuxNodeWitness] <;>
    nlinarith [hmul, ht0, hb₁, hb₂, hr₁, hr₂, hT, mul_nonneg hr₁ ht0, mul_nonneg hr₂ ht0]

/-- The objective at the witness is exactly the bound. -/
theorem arbMuxNodeDelay_witness (b₁ b₂ r₁ r₂ R T : ℝ) :
    arbMuxNodeDelay (arbMuxNodeWitness b₁ b₂ r₁ r₂ R T) = (R * T + b₁ + b₂) / (R - r₂) := by
  simp [arbMuxNodeDelay, arbMuxNodeWitness]

/-- **Theorem 11.1, single node under arbitrary multiplexing (Table 11.1, n = 1): the program
optimum is the worst-case delay.** For a tagged token-bucket flow `γ_{b₁,r₁}` sharing a strict
rate-latency server `β_{R,T}` with a cross flow `γ_{b₂,r₂}` under blind multiplexing
(`r₂ < R`, `r₁+r₂ ≤ R`), the optimum of the delay program is the residual-service delay
`(R·T+b₁+b₂)/(R−r₂)` — the upper bound holds on every feasible point and the explicit witness
attains it, so the finite LP computes the exact worst-case blind-multiplexing delay. -/
theorem arbMuxNode_programOptimum {b₁ b₂ r₁ r₂ R T : ℝ} (hRr₂ : r₂ < R) (hstab : r₁ + r₂ ≤ R)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hT : 0 ≤ T) :
    programOptimum (ArbMuxNodeFeasible b₁ b₂ r₁ r₂ R T)
        (fun v => ((arbMuxNodeDelay v : ℝ) : EReal))
      = ((R * T + b₁ + b₂) / (R - r₂) : ℝ) := by
  apply le_antisymm
  · exact programOptimum_le fun v hv => by exact_mod_cast arbMuxNodeDelay_le hRr₂ hstab hv
  · have h := le_programOptimum (Feasible := ArbMuxNodeFeasible b₁ b₂ r₁ r₂ R T)
      (obj := fun v => ((arbMuxNodeDelay v : ℝ) : EReal))
      (arbMuxNodeFeasible_witness hRr₂ hb₁ hb₂ hr₁ hr₂ hT)
    simp only [arbMuxNodeDelay_witness] at h
    exact h

/-! ## The single-node aggregate-backlog program (§11.1.2 backlog objective) -/

/-- The single-node program with the **backlog objective** (maximize the aggregate in-flight
data at server `n`): the Table 11.1 constraints minus the `u`-insertion ones. -/
def ArbMuxNodeBacklogFeasible (b₁ b₂ r₁ r₂ R T : ℝ) (v : ArbMuxNodeVars) : Prop :=
  v.t₀ ≤ v.t₁ ∧
  v.A₁t₀ ≤ v.A₁t₁ ∧ v.A₂t₀ ≤ v.A₂t₁ ∧
  v.A₁t₀ = v.D₁t₀ ∧ v.A₂t₀ = v.D₂t₀ ∧
  v.A₁t₁ - v.A₁t₀ ≤ b₁ + r₁ * (v.t₁ - v.t₀) ∧
  v.A₂t₁ - v.A₂t₀ ≤ b₂ + r₂ * (v.t₁ - v.t₀) ∧
  v.D₁t₀ + v.D₂t₀ + R * (v.t₁ - v.t₀) - R * T ≤ v.D₁t₁ + v.D₂t₁ ∧
  v.D₁t₀ + v.D₂t₀ ≤ v.D₁t₁ + v.D₂t₁

/-- The aggregate backlog at server `n`: `(A₁+A₂)(t₁) − (D₁+D₂)(t₁)`. -/
def arbMuxNodeBacklog (v : ArbMuxNodeVars) : ℝ :=
  (v.A₁t₁ + v.A₂t₁) - (v.D₁t₁ + v.D₂t₁)

/-- **Backlog upper bound (`≤`).** Under aggregate stability `r₁+r₂ ≤ R`, every feasible point's
backlog is at most `(b₁+b₂) + (r₁+r₂)·T` — the aggregate vertical deviation, maximized at the
rate-latency knee `t₁−t₀ = T`. The proof splits on whether the backlogged interval is below the
latency (service idle, the `≥ 0` piece binds) or above it (the rate-latency piece binds). -/
theorem arbMuxNodeBacklog_le {b₁ b₂ r₁ r₂ R T : ℝ} (hstab : r₁ + r₂ ≤ R)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    {v : ArbMuxNodeVars} (hv : ArbMuxNodeBacklogFeasible b₁ b₂ r₁ r₂ R T v) :
    arbMuxNodeBacklog v ≤ (b₁ + b₂) + (r₁ + r₂) * T := by
  obtain ⟨_, _, _, hbk1, hbk2, harr1, harr2, hservRL, hserv0⟩ := hv
  rw [arbMuxNodeBacklog]
  rcases le_total (v.t₁ - v.t₀) T with hle | hge
  · nlinarith [hbk1, hbk2, harr1, harr2, hserv0,
      mul_nonneg (show (0:ℝ) ≤ r₁ + r₂ by linarith) (show (0:ℝ) ≤ T - (v.t₁ - v.t₀) by linarith)]
  · nlinarith [hbk1, hbk2, harr1, harr2, hservRL,
      mul_nonneg (show (0:ℝ) ≤ R - r₁ - r₂ by linarith) (show (0:ℝ) ≤ (v.t₁ - v.t₀) - T by linarith)]

/-- The backlog witness: aggregate burst arrives at the origin and grows at `r₁+r₂` until the
latency `T`, while service stays idle (departures held at the backlogged-start value). -/
noncomputable def arbMuxNodeBacklogWitness (b₁ b₂ r₁ r₂ T : ℝ) : ArbMuxNodeVars where
  t₀ := 0
  u := 0
  t₁ := T
  A₁t₀ := 0
  A₁u := 0
  A₁t₁ := b₁ + r₁ * T
  A₂t₀ := 0
  A₂t₁ := b₂ + r₂ * T
  D₁t₀ := 0
  D₁t₁ := 0
  D₂t₀ := 0
  D₂t₁ := 0

/-- The backlog witness is feasible. -/
theorem arbMuxNodeBacklogFeasible_witness {b₁ b₂ r₁ r₂ R T : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hT : 0 ≤ T) :
    ArbMuxNodeBacklogFeasible b₁ b₂ r₁ r₂ R T (arbMuxNodeBacklogWitness b₁ b₂ r₁ r₂ T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arbMuxNodeBacklogWitness] <;>
    nlinarith [hb₁, hb₂, hr₁, hr₂, hT, mul_nonneg hr₁ hT, mul_nonneg hr₂ hT]

/-- The backlog objective at the witness is exactly the bound. -/
theorem arbMuxNodeBacklog_witness (b₁ b₂ r₁ r₂ T : ℝ) :
    arbMuxNodeBacklog (arbMuxNodeBacklogWitness b₁ b₂ r₁ r₂ T) = (b₁ + b₂) + (r₁ + r₂) * T := by
  simp only [arbMuxNodeBacklog, arbMuxNodeBacklogWitness]; ring

/-- **Single-node aggregate-backlog program optimum** (§11.1.2 backlog objective): the optimum is
`(b₁+b₂) + (r₁+r₂)·T`, the aggregate vertical deviation `vDev(γ_{b₁+b₂,r₁+r₂}, β_{R,T})` — bound on
every feasible point, attained by the witness. Policy-independent (FIFO and blind multiplexing
share this aggregate backlog). -/
theorem arbMuxNodeBacklog_programOptimum {b₁ b₂ r₁ r₂ R T : ℝ} (hstab : r₁ + r₂ ≤ R)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hT : 0 ≤ T) :
    programOptimum (ArbMuxNodeBacklogFeasible b₁ b₂ r₁ r₂ R T)
        (fun v => ((arbMuxNodeBacklog v : ℝ) : EReal))
      = (((b₁ + b₂) + (r₁ + r₂) * T : ℝ) : EReal) := by
  apply le_antisymm
  · exact programOptimum_le fun v hv => by exact_mod_cast arbMuxNodeBacklog_le hstab hr₁ hr₂ hv
  · have h := le_programOptimum (Feasible := ArbMuxNodeBacklogFeasible b₁ b₂ r₁ r₂ R T)
      (obj := fun v => ((arbMuxNodeBacklog v : ℝ) : EReal))
      (arbMuxNodeBacklogFeasible_witness hb₁ hb₂ hr₁ hr₂ hT)
    simp only [arbMuxNodeBacklog_witness] at h
    exact h

end DeepWiki
