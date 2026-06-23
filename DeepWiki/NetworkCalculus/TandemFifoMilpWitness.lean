import DeepWiki.NetworkCalculus.TandemFifoMilp
import DeepWiki.NetworkCalculus.TandemLinearProgramWitness

/-! # The FIFO tandem MILP worst-case witness (the attainment half of Theorem 11.2)

`TandemFifoMilp.lean` builds the §11.2.2 FIFO tandem MILP as data — the big-M Boolean
date-ordering primitive (`BigMOrder`/`bigMOrder_iff`), the augmented variables `FifoVars`,
the feasible set `FifoFeasible`, and the **soundness** direction `fifoDelay_le_objectiveValue`
(a FIFO-feasible point's end-to-end delay is at most the §11.1 objective).  This file builds
the **attainment** direction for the homogeneous-rate tandem: an explicit FIFO-feasible MILP
point — the §11.1 worst-case vertex `tandemWitness` lifted with a concrete Boolean ordering —
whose `fifoDelay` *equals* the objective, so the MILP optimum is *reached*, not merely
upper-bounded.  By `le_antisymm` (soundness + witness) the MILP optimum *equals* the
worst-case delay.

**The Boolean ordering is decided.** On the worst-case vertex the dates decrease back from
the output (`t h.succ ≤ t h.castSucc`), so every per-server FIFO date comparison resolves to
the **same** branch: the selector `z h = 0` (`b = 0 ⟹ x ≤ y`).  The MILP's exponential
`2^?` ordering choices collapse, on this extremal trajectory, to the single all-zero
assignment — the worst-case ordering — which is what makes the n=1/n=2 attainment a *finite*
computation rather than an enumeration.  The dates are boxed in `[0, M]` for any big-M
constant `M ≥ Δ = objectiveValue` (the output date `t 0 = Δ` is the maximum date).

**The honest scope** (inherited from `TandemLinearProgramWitness`).  The objective
`objectiveValue N Rmin = (∑ₕ Rₕ·Tₕ + b)/(Rmin − r)` is *attained* — and so equals the MILP
optimum — exactly on a **homogeneous-rate** tandem (`Rₕ = Rmin` for every server).  We deliver
the FIFO MILP witness and the optimum-equals-objective theorem under that hypothesis (which
subsumes the single server `n = 1` and the two-server `n = 2` example cases), and adjudicate
the heterogeneous and general-`n` cases at the end. -/

namespace DeepWiki

open scoped BigOperators

namespace TandemFifo

/-! ## The witness dates are boxed in `[0, Δ]`

The §11.1 worst-case vertex `tandemWitness` has nonnegative, monotone-decreasing dates, all
sitting in `[0, t 0]` with `t 0 = ∑ₕ witnessWindow = Δ` the maximum (the output date).  The
big-M FIFO ordering needs each compared date in `[0, M]`; these two bounds give it for any
`M ≥ Δ`. -/

/-- Every witness date is nonnegative (a sub-sum of nonnegative per-server windows). -/
theorem tandemWitness_t_nonneg {n : ℕ} {N : TandemLP.Tandem n} {Rmin : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : ∀ h : Fin n, 0 ≤ N.rate h)
    (hlat : ∀ h : Fin n, 0 ≤ N.lat h) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (h : Fin (n + 1)) : 0 ≤ (TandemLP.tandemWitness N Rmin).t h := by
  simp only [TandemLP.tandemWitness]
  refine Finset.sum_nonneg fun k _ => ?_
  split
  · exact TandemLP.witnessWindow_nonneg hRmin hrate0 hrate hlat hb hstab k
  · exact le_refl 0

/-- Every witness date is at most the output date `t 0 = Δ` (a sub-sum of the full
nonnegative window sum): `t h ≤ ∑ₖ witnessWindow k`. -/
theorem tandemWitness_t_le_sum {n : ℕ} {N : TandemLP.Tandem n} {Rmin : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : ∀ h : Fin n, 0 ≤ N.rate h)
    (hlat : ∀ h : Fin n, 0 ≤ N.lat h) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (h : Fin (n + 1)) :
    (TandemLP.tandemWitness N Rmin).t h ≤ ∑ k : Fin n, TandemLP.witnessWindow N Rmin k := by
  simp only [TandemLP.tandemWitness]
  refine Finset.sum_le_sum fun k _ => ?_
  split
  · exact le_refl _
  · exact TandemLP.witnessWindow_nonneg hRmin hrate0 hrate hlat hb hstab k

/-! ## The FIFO MILP witness (the lifted vertex with the worst-case Boolean ordering) -/

/-- **The FIFO tandem MILP witness**: the §11.1 worst-case vertex `tandemWitness` augmented
with the all-zero Boolean date-ordering `z = 0` — the worst-case ordering, in which every
per-server date comparison resolves to `t h.succ ≤ t h.castSucc` (the `b = 0` branch). -/
noncomputable def fifoTandemWitness {n : ℕ} (N : TandemLP.Tandem n) (Rmin : ℝ) : FifoVars n where
  base := TandemLP.tandemWitness N Rmin
  z := fun _ => 0

/-- The FIFO witness's objective equals the underlying §11.1 vertex's delay (the FIFO MILP
objective is the same end-to-end delay, read off `base`). -/
theorem fifoDelay_fifoTandemWitness {n : ℕ} (N : TandemLP.Tandem n) (Rmin : ℝ) :
    fifoDelay (fifoTandemWitness N Rmin) = TandemLP.delay (TandemLP.tandemWitness N Rmin) := rfl

/-- **The FIFO MILP witness is FIFO-feasible** on a homogeneous-rate stable tandem with
nonnegative data, for any big-M constant `M` bounding the witness dates (`Δ ≤ M`): the
underlying vertex is `TandemLP.Feasible` (`feasible_tandemWitness`), and per server the
all-zero selector `z h = 0` consistently picks `t h.succ ≤ t h.castSucc` with the dates boxed
in `[0, M]` and the big-M pair satisfied. -/
theorem fifoFeasible_fifoTandemWitness {n : ℕ} (N : TandemLP.Tandem (n + 1)) {Rmin M : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : ∀ h : Fin (n + 1), N.rate h = Rmin)
    (hlat : ∀ h : Fin (n + 1), 0 ≤ N.lat h) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (hM : (∑ k : Fin (n + 1), TandemLP.witnessWindow N Rmin k) ≤ M) :
    FifoFeasible N M (fifoTandemWitness N Rmin) := by
  have hrate' : ∀ h : Fin (n + 1), 0 ≤ N.rate h := fun h => by rw [hrate h]; exact hRmin.le
  have hnn : ∀ h : Fin (n + 2), 0 ≤ (TandemLP.tandemWitness N Rmin).t h := fun h =>
    tandemWitness_t_nonneg hRmin hrate0 hrate' hlat hb hstab h
  have hle : ∀ h : Fin (n + 2), (TandemLP.tandemWitness N Rmin).t h ≤ M := fun h =>
    le_trans (tandemWitness_t_le_sum hRmin hrate0 hrate' hlat hb hstab h) hM
  have hfeas : TandemLP.Feasible N (TandemLP.tandemWitness N Rmin) :=
    TandemLP.feasible_tandemWitness N hRmin hrate0 hrate hlat hb hstab
  refine ⟨hfeas, fun h => ?_⟩
  -- dates decrease (date ordering of the underlying vertex)
  have hdec : (TandemLP.tandemWitness N Rmin).t h.succ
      ≤ (TandemLP.tandemWitness N Rmin).t h.castSucc := hfeas.1 h
  refine
    { bBool := Or.inl rfl
      xge0 := hnn h.succ
      xleM := hle h.succ
      yge0 := hnn h.castSucc
      yleM := hle h.castSucc
      hxy := ?_
      hyx := ?_ }
  · -- `x + (1 - 0) * M ≥ y` : `y ≤ M ≤ x + M` since `x ≥ 0`
    simp only [fifoTandemWitness, sub_zero, one_mul, ge_iff_le]
    linarith [hle h.castSucc, hnn h.succ]
  · -- `y + 0 * M ≥ x` : exactly the date ordering `x ≤ y`
    simp only [fifoTandemWitness, zero_mul, add_zero, ge_iff_le]
    exact hdec

/-! ## Optimum = worst case (the completed FIFO MILP equivalence, homogeneous tandem) -/

/-- **Theorem 11.2, homogeneous tandem: the FIFO MILP optimum is the worst-case delay.**  For a
homogeneous-rate stable tandem (`Rₕ = Rmin` for every server, `0 ≤ r < Rmin`, nonnegative
latencies and burst) and any big-M constant `M ≥ Δ = (∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`, the optimum of
the §11.2.2 FIFO tandem delay MILP *equals* its objective value `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`: the
soundness bound `fifoDelay_le_objectiveValue` upper-bounds it on every FIFO-feasible point, and
`fifoTandemWitness` (the §11.1 vertex with the all-zero worst-case Boolean ordering) is a
FIFO-feasible point attaining it.  This closes the "optimum = worst case" half of Theorem 11.2 for
the homogeneous tandem; the heterogeneous and general-`n` cases are adjudicated below. -/
theorem fifoTandem_programOptimum_homogeneous {n : ℕ} (N : TandemLP.Tandem (n + 1)) {Rmin M : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : ∀ h : Fin (n + 1), N.rate h = Rmin)
    (hlat : ∀ h : Fin (n + 1), 0 ≤ N.lat h) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (hM : (∑ k : Fin (n + 1), TandemLP.witnessWindow N Rmin k) ≤ M) :
    programOptimum (FifoFeasible N M) (fun v => ((fifoDelay v : ℝ) : EReal))
      = ((TandemLP.objectiveValue N Rmin : ℝ) : EReal) := by
  have hRle : ∀ h : Fin (n + 1), Rmin ≤ N.rate h := fun h => by rw [hrate h]
  apply le_antisymm
  · exact programOptimum_le fun v hv => by
      exact_mod_cast fifoDelay_le_objectiveValue hv hRle hstab
  · have h := le_programOptimum (Feasible := FifoFeasible N M)
      (obj := fun v => ((fifoDelay v : ℝ) : EReal))
      (fifoFeasible_fifoTandemWitness N hRmin hrate0 hrate hlat hb hstab hM)
    rwa [fifoDelay_fifoTandemWitness, TandemLP.delay_tandemWitness N hRmin hrate hstab] at h

/-- **`n = 1` instance — the single FIFO server via the MILP encoding** (§11.2 base case): the
optimum of the one-server FIFO tandem delay MILP equals `(R·T + b)/(R − r)`, for any big-M
constant `M` bounding the worst-case date.  The single-server case of
`fifoTandem_programOptimum_homogeneous` (homogeneity is vacuous for one server) — bridging the
n=1 FIFO MILP encoding to the closed-form single-FIFO-server worst case. -/
theorem fifoTandem_programOptimum_one (N : TandemLP.Tandem 1) {Rmin M : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : N.rate 0 = Rmin)
    (hlat : 0 ≤ N.lat 0) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (hM : (∑ k : Fin 1, TandemLP.witnessWindow N Rmin k) ≤ M) :
    programOptimum (FifoFeasible N M) (fun v => ((fifoDelay v : ℝ) : EReal))
      = ((TandemLP.objectiveValue N Rmin : ℝ) : EReal) :=
  fifoTandem_programOptimum_homogeneous N hRmin hrate0
    (fun h => by rw [Fin.eq_zero h]; exact hrate)
    (fun h => by rw [Fin.eq_zero h]; exact hlat) hb hstab hM

/-- **`n = 2` instance — the two-server FIFO tandem MILP** (Example 11.2, equal-rate case): the
optimum of the two-server FIFO tandem delay MILP equals `(R·(T₀+T₁) + b)/(R − r)`, for any big-M
constant `M` bounding the worst-case date.  The two-server case of
`fifoTandem_programOptimum_homogeneous` with both servers at the common rate `R = Rmin` — the
attainment witness for the FIFO tandem of the §11.2 example. -/
theorem fifoTandem_programOptimum_two (N : TandemLP.Tandem 2) {Rmin M : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0)
    (hrate : ∀ h : Fin 2, N.rate h = Rmin) (hlat : ∀ h : Fin 2, 0 ≤ N.lat h)
    (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (hM : (∑ k : Fin 2, TandemLP.witnessWindow N Rmin k) ≤ M) :
    programOptimum (FifoFeasible N M) (fun v => ((fifoDelay v : ℝ) : EReal))
      = ((TandemLP.objectiveValue N Rmin : ℝ) : EReal) :=
  fifoTandem_programOptimum_homogeneous N hRmin hrate0 hrate hlat hb hstab hM

/-- **A concrete two-server FIFO tandem MILP optimum** (the §11.2 example, worked): two
servers each `β_{2,1}` (rate `2`, latency `1`), aggregate source `γ_{0,4}` (burst `4`, rate
`0`); the FIFO tandem MILP optimum equals `(2·1 + 2·1 + 4)/(2 − 0) = 4`.  An instance of
`fifoTandem_programOptimum_two` exhibiting the attainment witness reaching a numeric
worst-case delay. -/
theorem fifoTandem_programOptimum_two_example :
    programOptimum
        (FifoFeasible ⟨4, 0, ![2, 2], ![1, 1]⟩ 4)
        (fun v => ((fifoDelay v : ℝ) : EReal))
      = ((4 : ℝ) : EReal) := by
  have h := fifoTandem_programOptimum_two ⟨4, 0, ![2, 2], ![1, 1]⟩ (Rmin := 2) (M := 4)
    (by norm_num) (le_refl 0)
    (by rw [Fin.forall_fin_two]; constructor <;> norm_num)
    (by rw [Fin.forall_fin_two]; constructor <;> norm_num)
    (by norm_num) (by norm_num) ?_
  · rw [h]
    norm_num [TandemLP.objectiveValue, Fin.sum_univ_two]
  · -- the witness-window sum equals Δ = 4 ≤ M = 4 (source rate r = 0 ⟹ windows sum to Δ)
    rw [TandemLP.sum_witnessWindow_eq_of_pos, TandemLP.objectiveValue, Fin.sum_univ_two,
      Fin.sum_univ_two]
    norm_num

/-! ## The n=1 tandem-LP FIFO model is NOT the Table 11.2 single-FIFO-node model

A reader might expect the n=1 FIFO MILP optimum to equal the *tight* single-FIFO-node worst
case `T + (b₁+b₂)/R` proved in `WorstCaseLPFifoNode` (`fifoNode_programOptimum`).  It does
**not**: these are two genuinely different LP models of one physical FIFO server.

* `FifoNodeFeasible` (Table 11.2) models **two token-bucket flows** `γ_{bᵢ,rᵢ}` with the
  per-flow FIFO coupling `Dᵢ(t₁) = Aᵢ(t₂)` and aggregate *service* — its optimum is the
  **tight** horizontal deviation `T + (b₁+b₂)/R` (already closed exactly upstream).
* The n=1 `FifoFeasible N M` here is the §11.1.2 **aggregate single-flow** tandem LP (one
  token-bucket `(r, b)`, rate-latency *strict* service) augmented with the Boolean ordering —
  its optimum is the **SFA/residual** value `(R·T + b)/(R − r)` (`fifoTandem_programOptimum_one`).

For positive arrival rate `r > 0` these differ: `(R·T + b)/(R − r) > T + b/R` (the SFA-vs-exact
gap, present already at one server).  The lemma below makes the non-equality a citable fact, so
the n=1 tandem-LP optimum is **not** to be conflated with the Table 11.2 tight value. -/

/-- **The n=1 tandem-LP FIFO objective is strictly above the tight Table 11.2 value** (the
SFA-vs-exact gap at one server): the §11.1.2 aggregate objective `(R·T + b)/(R − r)` exceeds the
tight single-FIFO-node worst case `T + b/R` whenever the arrival rate is positive (`0 < r < R`),
the latency nonnegative (`0 ≤ T`), and the burst positive (`0 < b`).  Hence the n=1 tandem-LP
FIFO MILP optimum (`fifoTandem_programOptimum_one`) is **not** the closed-form `T + (b₁+b₂)/R` of
`WorstCaseLPFifoNode.fifoNode_programOptimum` — they are distinct LP models of one server. -/
theorem objectiveValue_one_gt_tight {R T b r : ℝ} (hR : 0 < R) (hT : 0 ≤ T) (hr : 0 < r)
    (hrR : r < R) (hb : 0 < b) : T + b / R < (R * T + b) / (R - r) := by
  rw [lt_div_iff₀ (by linarith : (0:ℝ) < R - r)]
  have hTR : (T + b / R) * R = R * T + b := by field_simp
  nlinarith [hTR, mul_pos hr (div_pos hb hR), mul_nonneg hT hr.le]

/-! ## Scoping: general-`n` FIFO MILP optimum = worst case beyond this file

The theorems above close "MILP optimum = worst case" (Theorem 11.2) for the **homogeneous-rate
tandem** at the SFA objective `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`, for any big-M constant `M ≥ Δ` — and
in particular for the n=1 and n=2 example cases.  What the *general* FIFO MILP optimum needs
beyond this is two distinct gaps:

* **The heterogeneous-rate gap** (already an LP, before any FIFO/Boolean content).  When some
  server is strictly faster than the bottleneck (`Rₕ > Rmin` with `Tₕ > 0`), the SFA objective is
  *strictly above* the LP/MILP optimum (`TandemLP.objectiveValue_not_tight_heterogeneous`), so
  this witness — which routes the whole burst into one bottleneck-rate window — is infeasible and
  the optimum is **not** this closed form.  The exact heterogeneous optimum is the value the
  finite program *computes*; recovering it analytically goes through the PMOO / per-server residual
  operators, not a closed-form lemma.  This gap is inherited verbatim from the arbitrary-mux LP
  (`TandemLinearProgramWitness`'s `## NON-ATTAINMENT`) and is orthogonal to FIFO.

* **The Boolean-ordering reconstruction gap** (the genuinely FIFO/MILP-specific content).  On the
  homogeneous worst-case vertex the date ordering is monotone, so the worst-case Boolean
  assignment is the single all-zero `z = 0` and attainment is a *finite computation* (no
  enumeration).  The full Theorem 11.2 claim "the MILP optimum equals the worst case" for an
  *arbitrary* tandem is, by contrast, an **extremal/existence** statement over the exponentially
  many `2^?` Boolean orderings: it requires the §11.2.2 trajectory-from-solution reconstruction —
  *every* MILP-optimal Boolean assignment `z ∈ {0,1}^?` must extrapolate to an admissible FIFO
  trajectory of the network realizing that delay (the converse of `FifoFeasible.feasible`'s
  soundness restriction).  This is **not** a finite case-split that closes for general `n`: the
  number of Boolean orderings grows as `2^?` (the book's binary-tree variable layout
  `t₁,…,t_{2^{n+1}-1}` doubles the dates at each server going backwards), and the reconstruction is
  a genuinely new existence argument (build a real cumulative-function trajectory whose sampled
  dates realize the optimal ordering), not an instance of the homogeneous witness here.  Concretely:
  the homogeneous witness collapses the orderings to one; the general claim must show *no* ordering
  does better, which needs the existence half, not the soundness half.  It is therefore `[infra]`
  (the binary-tree multi-flow representation layer) / `[research]` (the extremal reconstruction):
  a solver enumerates the orderings; no Lean lemma states the general optimum in closed form
  (contrast the single FIFO node `WorstCaseLPFifoNode`, whose optimum *is* closed form). -/

/-! ## Restatements (the theorems say what Theorem 11.2 says) -/

-- The FIFO MILP witness is FIFO-feasible on a homogeneous 3-server tandem (M = the date bound).
example (N : TandemLP.Tandem 3) {Rmin : ℝ} (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0)
    (hrate : ∀ h : Fin 3, N.rate h = Rmin) (hlat : ∀ h : Fin 3, 0 ≤ N.lat h)
    (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin) :
    FifoFeasible N (∑ k : Fin 3, TandemLP.witnessWindow N Rmin k) (fifoTandemWitness N Rmin) :=
  fifoFeasible_fifoTandemWitness N hRmin hrate0 hrate hlat hb hstab (le_refl _)

-- The optimum of the n-server homogeneous FIFO tandem delay MILP is the closed-form worst case.
example (N : TandemLP.Tandem 5) {Rmin M : ℝ} (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0)
    (hrate : ∀ h : Fin 5, N.rate h = Rmin) (hlat : ∀ h : Fin 5, 0 ≤ N.lat h)
    (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin)
    (hM : (∑ k : Fin 5, TandemLP.witnessWindow N Rmin k) ≤ M) :
    programOptimum (FifoFeasible N M) (fun v => ((fifoDelay v : ℝ) : EReal))
      = (((∑ h : Fin 5, N.rate h * N.lat h + N.burst) / (Rmin - N.rate0) : ℝ) : EReal) :=
  fifoTandem_programOptimum_homogeneous N hRmin hrate0 hrate hlat hb hstab hM

end TandemFifo

end DeepWiki
