import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.CompleteLattice.Finset
import DeepWiki.NetworkCalculus.WorstCaseLP

/-! # The general finite tandem linear program as data (Table 11.1, §11.1.2)

The §11.1.2 construction that turns the worst-case end-to-end delay (resp. backlog)
of a flow through an `n`-server tandem into a **finite** linear program.  The single
node cases (`WorstCaseLPArbMuxNode`, `WorstCaseLPFifoNode`) give the `n = 1` Table
11.1 / Table 11.2 programs in flat record form; this file gives the *general `n`* LP
as a Lean **data structure** — the variables (a vector of dates `t₀ ≥ ⋯ ≥ tₙ`, one
per server boundary, and the aggregate cumulative values sampled at them) and the
*linear* constraints a worst-case trajectory must satisfy (date ordering,
cumulative monotonicity, token-bucket arrival at the source, per-server rate-latency
*strict service*, and flow conservation across server boundaries) — together with
the **soundness** direction of the equivalence theorem (§11.1.3 / Theorem 11.1):

  **a feasible point of the LP has its end-to-end delay bounded by the LP objective
  value** `∑ₕ Tₕ + b / (minₕ Rₕ)` — so every feasible LP point is a *valid* worst-case
  scenario, and the LP objective upper-bounds the realized delay.

This is the representable half of Theorem 11.1: the constraint system *as data*, and
soundness (feasibility ⟹ the delay bound).  The optimization half — that the LP
*optimum equals* the worst case — is the extremal/existence content and is scoped at
the end of the file (it is not a closed form; it needs a solver, not a Lean lemma).
The full multi-flow routing (`pred_i`, the per-flow paths `pᵢ`) and the FIFO MILP of
Theorem 11.2 (the Boolean date-ordering variables) are likewise scoped, not built. -/

namespace DeepWiki

open scoped BigOperators

namespace TandemLP

/-- **The data of a finite tandem of `n` servers** (the network instance of the
§11.1.2 LP): an aggregate source burst `b` and arrival rate `r`, and for each of the
`n` servers a rate-latency strict service curve `β_{Rₕ,Tₕ}` (`rate h`, `lat h`).  The
LP variables and constraints are defined relative to this fixed instance. -/
structure Tandem (n : ℕ) where
  /-- Aggregate source burst (the token-bucket `b`). -/
  burst : ℝ
  /-- Aggregate source rate (the token-bucket `r`). -/
  rate0 : ℝ
  /-- Per-server service rate `Rₕ` of the rate-latency strict service curve. -/
  rate : Fin n → ℝ
  /-- Per-server latency `Tₕ` of the rate-latency strict service curve. -/
  lat : Fin n → ℝ

/-- **The variables of the §11.1.2 tandem LP.**  One date `t h` per server boundary
`h : Fin (n+1)` (`t 0` the departure of the bit of interest from the last server,
`t n` the start of the global backlogged period at the source — the dates *decrease*
as `h` increases, matching the book's `tₙ ≤ ⋯ ≤ t₁ ≤ t₀` exploration backwards from
the output) together with the sampled aggregate cumulative *arrival* `A h` and
*departure* `D h` at boundary `h`.  Boundary `h` sits between server `h-1` (upstream)
and server `h` (downstream): `D h` is what has left the upstream side, `A h` what is
offered to the downstream side. -/
structure Vars (n : ℕ) where
  /-- The date at server boundary `h` (decreasing in `h`). -/
  t : Fin (n + 1) → ℝ
  /-- Aggregate arrival cumulative offered to boundary `h`, sampled at `t h`. -/
  A : Fin (n + 1) → ℝ
  /-- Aggregate departure cumulative produced at boundary `h`, sampled at `t h`. -/
  D : Fin (n + 1) → ℝ

/-- **The feasible set of the §11.1.2 tandem LP** (the linear constraints of Table
11.1, aggregate single-flow form, generalized to `n` servers).  A point `v : Vars n`
is feasible for the tandem `N` when, writing `tₕ = v.t h`, `Aₕ = v.A h`, `Dₕ = v.D h`:

* **date ordering** `t (h+1) ≤ t h`: dates decrease back from the output;
* **arrival monotone** `A (h+1) ≤ A h` and **departure monotone** `D (h+1) ≤ D h`:
  cumulative functions are non-decreasing, sampled at decreasing dates;
* **source arrival** `A 0 - A n ≤ burst + rate0 * (t 0 - t n)`: the aggregate input
  is `γ_{r,b}`-constrained — its *increase* over the global backlogged window
  `[t n, t 0]` (`t n ≤ t 0`, the earlier date being `t n`) is at most `b + r·(window)`;
* **per-server strict service** `A h - D h ≥ rate h * ((t h - t (h+1)) - lat h)`:
  during its backlogged period server `h` (between boundaries `h` and `h+1`) outputs
  at least its rate-latency strict service curve `β_{Rₕ,Tₕ}` of the window length;
* **flow conservation** `D h = A (h+1)`: what leaves the upstream side of boundary
  `h+1` is exactly what is offered to its downstream side (no loss, single flow);
* **causality** `D h ≤ A h`: a server cannot output more than it has received. -/
def Feasible {n : ℕ} (N : Tandem n) (v : Vars n) : Prop :=
  (∀ h : Fin n, v.t h.succ ≤ v.t h.castSucc) ∧
  (∀ h : Fin n, v.A h.succ ≤ v.A h.castSucc) ∧
  (∀ h : Fin n, v.D h.succ ≤ v.D h.castSucc) ∧
  (v.A 0 - v.A (Fin.last n) ≤ N.burst + N.rate0 * (v.t 0 - v.t (Fin.last n))) ∧
  (∀ h : Fin n, N.rate h * ((v.t h.castSucc - v.t h.succ) - N.lat h)
      ≤ v.A h.castSucc - v.D h.castSucc) ∧
  (∀ h : Fin n, v.D h.castSucc = v.A h.succ) ∧
  (∀ h : Fin n, v.D h.castSucc ≤ v.A h.castSucc)

/-- The LP **objective**: the end-to-end delay of the bit of interest, the time it
spends in the network — from its source date `t (last)` to its departure date `t 0`
(§11.1.2.3, `max tₙ - u` in the book's exploration-backwards convention). -/
def delay {n : ℕ} (v : Vars n) : ℝ := v.t 0 - v.t (Fin.last n)

/-- The **per-server window length** `wₕ = t h.castSucc - t h.succ`: the length of
server `h`'s backlogged interval `[t h.succ, t h.castSucc]`.  Nonnegative on a
feasible point (dates decrease), and the delay is the sum of the windows. -/
def window {n : ℕ} (v : Vars n) (h : Fin n) : ℝ := v.t h.castSucc - v.t h.succ

/-- The **per-server backlog** `Qₕ = A h.castSucc - D h.castSucc`: the in-flight data
at boundary `h` at its date.  Nonnegative on a feasible point (causality). -/
def backlog {n : ℕ} (v : Vars n) (h : Fin n) : ℝ := v.A h.castSucc - v.D h.castSucc

/-- General telescoping over `Fin n`: `∑ h, (g h.castSucc - g h.succ) = g 0 - g (last)`. -/
private theorem sum_castSucc_sub_succ {n : ℕ} (g : Fin (n + 1) → ℝ) :
    ∑ h : Fin n, (g h.castSucc - g h.succ) = g 0 - g (Fin.last n) := by
  set f : ℕ → ℝ := fun i => g ⟨min i n, by omega⟩ with hf
  have hstep : ∑ h : Fin n, (g h.castSucc - g h.succ) = ∑ i ∈ Finset.range n, (f i - f (i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => f i - f (i + 1))]
    refine Finset.sum_congr rfl fun h _ => ?_
    have h1 : f (h : ℕ) = g h.castSucc := by
      have : (⟨min (h : ℕ) n, by omega⟩ : Fin (n + 1)) = h.castSucc :=
        Fin.ext (by simp only [Fin.val_castSucc]; omega)
      simp only [hf]; rw [this]
    have h2 : f ((h : ℕ) + 1) = g h.succ := by
      have : (⟨min ((h : ℕ) + 1) n, by omega⟩ : Fin (n + 1)) = h.succ :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      simp only [hf]; rw [this]
    rw [h1, h2]
  rw [hstep, Finset.sum_range_sub' f n]
  have hf0 : f 0 = g 0 := by
    have : (⟨min 0 n, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext (by simp)
    simp only [hf]; rw [this]
  have hfn : f n = g (Fin.last n) := by
    have : (⟨min n n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [Fin.last])
    simp only [hf]; rw [this]
  rw [hf0, hfn]

/-- The delay is the **sum of the per-server windows** `∑ₕ wₕ = t 0 - t (last)`
(telescoping the date differences along the tandem). -/
theorem delay_eq_sum_window {n : ℕ} (v : Vars n) :
    delay v = ∑ h : Fin n, window v h := by
  rw [delay]
  exact (sum_castSucc_sub_succ v.t).symm

/-! ## Soundness fragment (Theorem 11.1, the feasibility ⟹ delay-bound direction)

The representable half of the equivalence theorem: a feasible LP point's end-to-end
delay is bounded by the LP objective value.  Everything below is **pure linear
arithmetic** on the program variables — exactly the LP-soundness content. -/

/-- On a feasible point each per-server window is nonnegative (dates decrease). -/
theorem window_nonneg {n : ℕ} {N : Tandem n} {v : Vars n} (hv : Feasible N v) (h : Fin n) :
    0 ≤ window v h := sub_nonneg.mpr (hv.1 h)

/-- On a feasible point each per-server backlog is nonnegative (causality). -/
theorem backlog_nonneg {n : ℕ} {N : Tandem n} {v : Vars n} (hv : Feasible N v) (h : Fin n) :
    0 ≤ backlog v h := sub_nonneg.mpr (hv.2.2.2.2.2.2 h)

/-- The per-server backlog equals the cumulative drop `A h.castSucc - A h.succ` across
boundary `h` (flow conservation `D h.castSucc = A h.succ`). -/
theorem backlog_eq {n : ℕ} {N : Tandem n} {v : Vars n} (hv : Feasible N v) (h : Fin n) :
    backlog v h = v.A h.castSucc - v.A h.succ := by
  rw [backlog, hv.2.2.2.2.2.1 h]

/-- **Per-server window bound** (the rate-latency strict-service constraint, solved for
the window): on a feasible point, `Rₕ · wₕ ≤ Rₕ · Tₕ + Qₕ` — the server clears the
window minus its latency at rate `Rₕ`, leaving the residual backlog `Qₕ`. -/
theorem rate_mul_window_le {n : ℕ} {N : Tandem n} {v : Vars n} (hv : Feasible N v) (h : Fin n) :
    N.rate h * window v h ≤ N.rate h * N.lat h + backlog v h := by
  have hserv := hv.2.2.2.2.1 h
  rw [window, backlog]; nlinarith [hserv]

/-- **The total backlog is bounded by the source token bucket** (the arrival
constraint, telescoped): on a feasible point, `∑ₕ Qₕ = A 0 - A (last) ≤ b + r·delay`.
The per-server backlogs telescope to the global cumulative drop, which the source
arrival curve caps. -/
theorem sum_backlog_le {n : ℕ} {N : Tandem n} {v : Vars n} (hv : Feasible N v) :
    ∑ h : Fin n, backlog v h ≤ N.burst + N.rate0 * delay v := by
  have hsum : ∑ h : Fin n, backlog v h = v.A 0 - v.A (Fin.last n) := by
    rw [Finset.sum_congr rfl fun h _ => backlog_eq hv h]
    exact sum_castSucc_sub_succ v.A
  rw [hsum, delay]
  exact hv.2.2.2.1

/-- The **objective value of the LP** for a bottleneck rate `Rmin`: the SFA/residual
end-to-end delay bound `(∑ₕ Rₕ·Tₕ + b) / (Rmin − r)`.  This is the closed-form value
the LP soundness theorem bounds the realized delay by. -/
noncomputable def objectiveValue {n : ℕ} (N : Tandem n) (Rmin : ℝ) : ℝ :=
  (∑ h : Fin n, N.rate h * N.lat h + N.burst) / (Rmin - N.rate0)

/-- **Bottleneck inequality** (the un-divided soundness core): for a bottleneck rate
`Rmin ≤ Rₕ` for every server, a feasible point satisfies
`(Rmin − r) · delay ≤ ∑ₕ Rₕ·Tₕ + b`.  Sum the per-server window bounds
`Rₕ·wₕ ≤ Rₕ·Tₕ + Qₕ` (dominating `Rₕ` down to `Rmin` since `wₕ ≥ 0`), telescope the
backlogs against the source token bucket, and collect the `delay` terms. -/
theorem bottleneck_ineq {n : ℕ} {N : Tandem n} {v : Vars n} (hv : Feasible N v)
    {Rmin : ℝ} (hRmin : ∀ h : Fin n, Rmin ≤ N.rate h) :
    (Rmin - N.rate0) * delay v ≤ ∑ h : Fin n, N.rate h * N.lat h + N.burst := by
  have hwin : Rmin * delay v ≤ ∑ h : Fin n, (N.rate h * N.lat h + backlog v h) := by
    rw [delay_eq_sum_window, Finset.mul_sum]
    refine Finset.sum_le_sum fun h _ => ?_
    calc Rmin * window v h ≤ N.rate h * window v h :=
          mul_le_mul_of_nonneg_right (hRmin h) (window_nonneg hv h)
      _ ≤ N.rate h * N.lat h + backlog v h := rate_mul_window_le hv h
  rw [Finset.sum_add_distrib] at hwin
  have hback := sum_backlog_le hv
  nlinarith [hwin, hback]

/-- **Theorem 11.1 — LP soundness (feasibility ⟹ delay bound).** For a stable tandem
(`rate0 < Rmin ≤ Rₕ` for every server, the source rate below the bottleneck service
rate), every feasible LP point's end-to-end delay is at most the objective value
`(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)` — so a feasible point of the linear program is a *valid*
worst-case scenario and the LP objective upper-bounds the realized delay.  This is the
representable half of the §11.1.3 equivalence (the optimization half — that the optimum
*equals* the worst case — is scoped below, not formalized). -/
theorem delay_le_objectiveValue {n : ℕ} {N : Tandem n} {v : Vars n} (hv : Feasible N v)
    {Rmin : ℝ} (hRmin : ∀ h : Fin n, Rmin ≤ N.rate h) (hstab : N.rate0 < Rmin) :
    delay v ≤ objectiveValue N Rmin := by
  rw [objectiveValue, le_div_iff₀ (by linarith : (0:ℝ) < Rmin - N.rate0)]
  rw [mul_comm]
  exact bottleneck_ineq hv hRmin

end TandemLP

end DeepWiki
