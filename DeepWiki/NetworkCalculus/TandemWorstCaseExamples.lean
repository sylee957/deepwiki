import DeepWiki.NetworkCalculus.WorstCaseLPFifoNode
import DeepWiki.NetworkCalculus.TandemLinearProgram

/-! # Worked worst-case examples (DNC §11.1.1 / §11.2.1)

The two worked examples of Chapter 11, instantiating the finite worst-case linear
programs on the curves of Figure 10.2 (two flows crossing two servers, token-bucket
arrival curves `γ_{r,b}` and rate-latency strict service curves `β_{R,T}`).

* **Example 11.2** (§11.2.1, single FIFO node): the Table 11.2 program for one FIFO
  server crossed by two token-bucket flows `γ_{bᵢ,rᵢ}` under a rate-latency curve
  `β_{R,T}` has *exact* optimum `T + (b₁+b₂)/R` — closed-form, both bounds being linear
  arithmetic (`fifoNode_programOptimum`).
* **Example 11.1** (§11.1.1, two-server tandem): the Table 11.1 program for a single
  aggregate flow through two rate-latency strict-service servers in series.  Here only
  the *soundness* half is closed-form: a feasible LP point's end-to-end delay is bounded
  by the objective value `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)` (`delay_le_objectiveValue`); on the
  symmetric instance (`R₁=R₂=R`, `T₁=T₂=T`, two flows `γ_{r,b}`) this is `(2RT + 2b)/(R − 2r)`.

The figures give the curves *symbolically* (token-bucket `γ_{r,b}`, rate-latency `β_{R,T}`),
so the examples are formalized with symbolic curve parameters, which is more faithful than
inventing numeric values. -/

namespace DeepWiki

open scoped NNReal

namespace TandemWorstCaseExamples

/-! ## Example 11.2 — single FIFO node (§11.2.1, Table 11.2)

The Figure 10.2 single-server picture: two token-bucket flows `γ_{b₁,r₁}`, `γ_{b₂,r₂}`
cross one FIFO rate-latency server `β_{R,T}`.  The Table 11.2 linear program computes the
*exact* worst-case delay of the aggregate, `T + (b₁+b₂)/R`. -/

/-- **Example 11.2 (single FIFO node): the worst-case FIFO delay is `T + (b₁+b₂)/R`.**
For two token-bucket flows `γ_{b₁,r₁}`, `γ_{b₂,r₂}` through a rate-latency FIFO server
`β_{R,T}` with stability `r₁+r₂ ≤ R` (and nonnegative bursts/latency, positive rate), the
optimum of the Table 11.2 delay program is exactly `T + (b₁+b₂)/R`.  This single-node case
is closed-form: the upper bound holds on every feasible point and an explicit witness
attains it, so the finite LP itself computes the worst case. -/
theorem example_11_2_fifo_optimum {b₁ b₂ r₁ r₂ R T : ℝ}
    (hR : 0 < R) (hstab : r₁ + r₂ ≤ R) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hT : 0 ≤ T) :
    programOptimum (FifoNodeFeasible b₁ b₂ r₁ r₂ R T)
        (fun v => ((fifoNodeDelay v : ℝ) : EReal))
      = ((T + (b₁ + b₂) / R : ℝ) : EReal) :=
  fifoNode_programOptimum hR hstab hb₁ hb₂ hT

/-- Book restatement of Example 11.2: the single FIFO node program optimum is `T + (b₁+b₂)/R`. -/
example {b₁ b₂ r₁ r₂ R T : ℝ}
    (hR : 0 < R) (hstab : r₁ + r₂ ≤ R) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hT : 0 ≤ T) :
    programOptimum (FifoNodeFeasible b₁ b₂ r₁ r₂ R T)
        (fun v => ((fifoNodeDelay v : ℝ) : EReal))
      = ((T + (b₁ + b₂) / R : ℝ) : EReal) :=
  example_11_2_fifo_optimum hR hstab hb₁ hb₂ hT

/-- **Example 11.2, equal-flow specialization** (`b₁=b₂=b`, `r₁=r₂=r`, the Figure-10.2
symmetric two-flow case): the worst-case FIFO delay is `T + 2b/R`. -/
theorem example_11_2_fifo_optimum_symmetric {b r R T : ℝ}
    (hR : 0 < R) (hstab : 2 * r ≤ R) (hb : 0 ≤ b) (hT : 0 ≤ T) :
    programOptimum (FifoNodeFeasible b b r r R T)
        (fun v => ((fifoNodeDelay v : ℝ) : EReal))
      = ((T + 2 * b / R : ℝ) : EReal) := by
  have h := example_11_2_fifo_optimum (b₁ := b) (b₂ := b) (r₁ := r) (r₂ := r)
    (R := R) (T := T) hR (by linarith) hb hb hT
  rw [h]; norm_num; ring_nf

/-! ## Example 11.1 — two servers in tandem (§11.1.1, Table 11.1)

The Figure 10.2 two-server picture, taken as a single aggregate flow: two token-bucket
flows `γ_{r,b}` aggregate to `γ_{2r,2b}` at the source, and cross two rate-latency
*strict service* servers `β_{R,T}` in series.  We instantiate `TandemLP.Tandem 2` with
this data and state the §11.1.3 soundness bound. -/

/-- **The two-server tandem instance of Example 11.1** (Figure 10.2): a single aggregate
flow `γ_{2r,2b}` (two flows `γ_{r,b}`) crossing two identical rate-latency strict-service
servers `β_{R,T}`. -/
def example_11_1_tandem (b r R T : ℝ) : TandemLP.Tandem 2 where
  burst := 2 * b
  rate0 := 2 * r
  rate := fun _ => R
  lat := fun _ => T

/-- The two-server objective value at the bottleneck rate `R` is `(2RT + 2b)/(R − 2r)`:
both servers contribute `R·T`, the aggregate burst is `2b`, and the residual rate is `R − 2r`. -/
theorem example_11_1_objectiveValue (b r R T : ℝ) :
    TandemLP.objectiveValue (example_11_1_tandem b r R T) R
      = (2 * (R * T) + 2 * b) / (R - 2 * r) := by
  rw [TandemLP.objectiveValue]
  congr 1
  simp only [example_11_1_tandem, Fin.sum_univ_two]
  ring

/-- **Example 11.1 (two servers in tandem): the worst-case end-to-end delay bound.**
For the Figure-10.2 instance (aggregate flow `γ_{2r,2b}`, two strict rate-latency servers
`β_{R,T}`) with stability `2r < R`, every feasible point of the Table 11.1 linear program
has its end-to-end delay bounded by the objective value `(2RT + 2b)/(R − 2r)`.  This is the
soundness half of the §11.1.3 equivalence theorem: a feasible LP point is a valid
worst-case scenario, so the objective upper-bounds the realized delay. -/
theorem example_11_1_delay_bound {b r R T : ℝ} (hstab : 2 * r < R)
    {v : TandemLP.Vars 2} (hv : TandemLP.Feasible (example_11_1_tandem b r R T) v) :
    TandemLP.delay v ≤ (2 * (R * T) + 2 * b) / (R - 2 * r) := by
  have hRmin : ∀ h : Fin 2, R ≤ (example_11_1_tandem b r R T).rate h := fun _ => le_rfl
  have hstab' : (example_11_1_tandem b r R T).rate0 < R := by
    simp only [example_11_1_tandem]; exact hstab
  have := TandemLP.delay_le_objectiveValue hv hRmin hstab'
  rwa [example_11_1_objectiveValue] at this

/-- Book restatement of Example 11.1: a feasible two-server-tandem LP point has end-to-end
delay at most `(2RT + 2b)/(R − 2r)` (the §11.1.3 soundness bound on the Figure-10.2 instance). -/
example {b r R T : ℝ} (hstab : 2 * r < R)
    {v : TandemLP.Vars 2} (hv : TandemLP.Feasible (example_11_1_tandem b r R T) v) :
    TandemLP.delay v ≤ (2 * (R * T) + 2 * b) / (R - 2 * r) :=
  example_11_1_delay_bound hstab hv

end TandemWorstCaseExamples

end DeepWiki
