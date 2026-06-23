import DeepWiki.NetworkCalculus.TandemLinearProgram

/-! # The tandem LP worst-case witness (the attainment / completeness half of §11.1.3)

`TandemLinearProgram.lean` builds the §11.1.2 finite tandem linear program as data and
proves the **soundness** direction of the equivalence theorem (§11.1.3 / Theorem 11.1):
every feasible point's end-to-end delay is at most the objective value
`(∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`.  This file builds the **attainment** direction: an explicit
worst-case witness trajectory (the LP vertex) that is feasible and *attains* the objective,
so the program optimum *equals* it — the "optimum = worst case" half the Ch11 catalog marks
`[infra]`, mirroring how the single FIFO node (`WorstCaseLPFifoNode.lean`) closes its own
worst case via `fifoNodeWitness`.

**The honest scope.**  `objectiveValue N Rmin = (∑ₕ Rₕ·Tₕ + b)/(Rmin − r)` is the
SFA/residual end-to-end bound.  It is *attained* — and so equals the LP optimum — precisely
on a **homogeneous-rate** tandem (`Rₕ = Rmin` for every server): then the bottleneck
inequality chain of `bottleneck_ineq` is tight at every server.  For a tandem with a server
strictly above the bottleneck (`Rₕ > Rmin` with `Tₕ > 0`) the SFA value is *strictly above*
the LP optimum (the well-known SFA-vs-exact gap), so no feasible point attains it and the
witness below would be infeasible — see the `## NON-ATTAINMENT` adjudication at the end.  We
therefore deliver the witness and the optimum-equals-objective theorem under the
homogeneous-rate hypothesis (which subsumes the single server `n = 1` and the two-server
`n = 2` cases the §11.1 examples use), and adjudicate the heterogeneous general case. -/

namespace DeepWiki

open scoped BigOperators

namespace TandemLP

/-- The witness's per-server window `wₕ`: `Tₕ` at every server except boundary `0`, where the
extra `(b + r·Δ)/Rmin` (with `Δ = objectiveValue N Rmin`) absorbs and clears the source burst
at the bottleneck rate. -/
noncomputable def witnessWindow {n : ℕ} (N : Tandem n) (Rmin : ℝ) (h : Fin n) : ℝ :=
  if (h : ℕ) = 0 then N.lat h + (N.burst + N.rate0 * objectiveValue N Rmin) / Rmin
  else N.lat h

/-- **The worst-case witness trajectory** (the LP vertex attaining the objective) for a
**homogeneous-rate** tandem at bottleneck rate `Rmin`.  The whole source burst `b` plus its
growth `r·Δ` over the global backlogged window arrives, sits as backlog at boundary `0`
(closest to the output), and clears at the bottleneck rate; every server runs exactly at its
rate-latency knee.  Writing `Δ = objectiveValue N Rmin`, the dates are the reverse partial
sums of the per-server windows `witnessWindow` anchored at the source date `t (last) = 0`; the
aggregate arrival is the burst `b + r·Δ` sampled at boundary `0` and `0` at every later
boundary, with all departures held at `0`. -/
noncomputable def tandemWitness {n : ℕ} (N : Tandem n) (Rmin : ℝ) : Vars n where
  t := fun h => ∑ k : Fin n, if (h : ℕ) ≤ (k : ℕ) then witnessWindow N Rmin k else 0
  A := fun h => if (h : ℕ) = 0 then N.burst + N.rate0 * objectiveValue N Rmin else 0
  D := fun _ => 0

/-! ## Witness satellite lemmas (the closed-form readings of the dates and cumulatives) -/

/-- The witness's per-server window is exactly `witnessWindow` (the date difference
`t h.castSucc − t h.succ` telescopes to its single surviving summand `k = h`). -/
theorem window_tandemWitness {n : ℕ} (N : Tandem n) (Rmin : ℝ) (h : Fin n) :
    window (tandemWitness N Rmin) h = witnessWindow N Rmin h := by
  simp only [window, tandemWitness, Fin.val_castSucc, Fin.val_succ]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single h]
  · simp
  · intro k _ hk
    rcases le_or_gt ((h : ℕ)) ((k : ℕ)) with hle | hgt
    · have : (h : ℕ) + 1 ≤ (k : ℕ) := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · omega
        · exact absurd (Fin.ext heq).symm hk
      simp [hle, this]
    · have h1 : ¬ (h : ℕ) ≤ (k : ℕ) := not_le.mpr hgt
      have h2 : ¬ (h : ℕ) + 1 ≤ (k : ℕ) := by omega
      simp [h1, h2]
  · intro hcontra
    exact absurd (Finset.mem_univ h) hcontra

/-- The witness's source date is `t (last) = 0` (the global backlogged period starts at the
origin: no window `wₖ` has index `≥ n`). -/
theorem t_last_tandemWitness {n : ℕ} (N : Tandem n) (Rmin : ℝ) :
    (tandemWitness N Rmin).t (Fin.last n) = 0 := by
  simp only [tandemWitness, Fin.val_last]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : ¬ n ≤ (k : ℕ) := by omega
  simp [this]

/-- The witness's output date is `t 0 = ∑ₕ witnessWindow = Δ`: the sum of all per-server
windows, the end-to-end delay. -/
theorem t_zero_tandemWitness {n : ℕ} (N : Tandem n) (Rmin : ℝ) :
    (tandemWitness N Rmin).t 0 = ∑ h : Fin n, witnessWindow N Rmin h := by
  simp only [tandemWitness, Fin.val_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- The sum of the witness windows splits as `∑ₕ Tₕ + (b + r·Δ)/Rmin`: every server is at its
latency knee, and boundary `0` carries the extra burst-clearing window. -/
theorem sum_witnessWindow_eq {n : ℕ} (N : Tandem n) (Rmin : ℝ) :
    ∑ h : Fin n, witnessWindow N Rmin h
      = ∑ h : Fin n, N.lat h
        + (∑ h : Fin n, if (h : ℕ) = 0 then (1 : ℝ) else 0)
          * ((N.burst + N.rate0 * objectiveValue N Rmin) / Rmin) := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  unfold witnessWindow
  by_cases hh : (h : ℕ) = 0 <;> simp [hh]

/-- On a tandem with at least one server, the boundary-`0` indicator sums to `1` (exactly the
server `⟨0, _⟩`), so the witness-window sum is `∑ₕ Tₕ + (b + r·Δ)/Rmin`. -/
theorem sum_witnessWindow_eq_of_pos {n : ℕ} (N : Tandem (n + 1)) (Rmin : ℝ) :
    ∑ h : Fin (n + 1), witnessWindow N Rmin h
      = ∑ h : Fin (n + 1), N.lat h
        + (N.burst + N.rate0 * objectiveValue N Rmin) / Rmin := by
  rw [sum_witnessWindow_eq]
  congr 1
  have hind : (∑ h : Fin (n + 1), if (h : ℕ) = 0 then (1 : ℝ) else 0)
        = ∑ h : Fin (n + 1), if h = (0 : Fin (n + 1)) then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hh : h = (0 : Fin (n + 1))
    · simp [hh]
    · have : (h : ℕ) ≠ 0 := fun hc => hh (Fin.ext (by simp [hc]))
      simp [hh, this]
  rw [hind, Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1)) (fun _ => (1 : ℝ))]
  simp

/-- **The witness attains the objective** (the crux): on a homogeneous-rate tandem
(`Rₕ = Rmin` for every server, `r < Rmin`), the witness's end-to-end delay equals
`objectiveValue N Rmin = (∑ₕ Rₕ·Tₕ + b)/(Rmin − r)`.  The delay is `∑ₕ wₕ = ∑ₕ Tₕ +
(b + r·Δ)/Rmin`, and the objective's defining identity `(Rmin − r)·Δ = Rmin·∑ₕ Tₕ + b`
rearranges to exactly that. -/
theorem delay_tandemWitness {n : ℕ} (N : Tandem (n + 1)) {Rmin : ℝ}
    (hRmin : 0 < Rmin) (hrate : ∀ h : Fin (n + 1), N.rate h = Rmin) (hstab : N.rate0 < Rmin) :
    delay (tandemWitness N Rmin) = objectiveValue N Rmin := by
  have hsum : ∑ h : Fin (n + 1), N.rate h * N.lat h = Rmin * ∑ h : Fin (n + 1), N.lat h := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [hrate h]
  -- the objective's defining identity `(Rmin − r)·Δ = Rmin·∑Tₕ + b`
  have hobj : (Rmin - N.rate0) * objectiveValue N Rmin
      = Rmin * (∑ h : Fin (n + 1), N.lat h) + N.burst := by
    rw [objectiveValue, mul_div_cancel₀ _ (by linarith : Rmin - N.rate0 ≠ 0), hsum]
  rw [delay, t_zero_tandemWitness, t_last_tandemWitness, sub_zero,
    sum_witnessWindow_eq_of_pos]
  field_simp
  nlinarith [hobj]

/-- The objective value is nonnegative for a stable tandem with nonnegative data
(nonnegative rates, latencies, burst, and `r < Rmin`). -/
theorem objectiveValue_nonneg {n : ℕ} {N : Tandem n} {Rmin : ℝ}
    (hrate : ∀ h : Fin n, 0 ≤ N.rate h) (hlat : ∀ h : Fin n, 0 ≤ N.lat h)
    (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin) :
    0 ≤ objectiveValue N Rmin := by
  rw [objectiveValue]
  refine div_nonneg ?_ (by linarith)
  refine add_nonneg (Finset.sum_nonneg fun h _ => mul_nonneg (hrate h) (hlat h)) hb

/-- The per-server witness window is nonnegative (latency nonneg, the burst-clearing window
nonneg). -/
theorem witnessWindow_nonneg {n : ℕ} {N : Tandem n} {Rmin : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0)
    (hrate : ∀ h : Fin n, 0 ≤ N.rate h) (hlat : ∀ h : Fin n, 0 ≤ N.lat h)
    (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin) (h : Fin n) :
    0 ≤ witnessWindow N Rmin h := by
  have hΔ : 0 ≤ objectiveValue N Rmin := objectiveValue_nonneg hrate hlat hb hstab
  unfold witnessWindow
  by_cases hh : (h : ℕ) = 0
  · rw [if_pos hh]
    refine add_nonneg (hlat h) (div_nonneg ?_ hRmin.le)
    exact add_nonneg hb (mul_nonneg hrate0 hΔ)
  · rw [if_neg hh]; exact hlat h

/-- **The witness is feasible** (the LP vertex lies in the feasible polytope) on a
homogeneous-rate stable tandem with nonnegative data: every constraint of `Feasible` holds —
date ordering and monotonicity from window nonnegativity, the source-arrival, service,
flow-conservation, and causality constraints by the explicit cumulative values (the
source/service constraints binding with equality, the witness being a vertex). -/
theorem feasible_tandemWitness {n : ℕ} (N : Tandem (n + 1)) {Rmin : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : ∀ h : Fin (n + 1), N.rate h = Rmin)
    (hlat : ∀ h : Fin (n + 1), 0 ≤ N.lat h) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin) :
    Feasible N (tandemWitness N Rmin) := by
  have hrate' : ∀ h : Fin (n + 1), 0 ≤ N.rate h := fun h => by rw [hrate h]; exact hRmin.le
  have hwin : ∀ h : Fin (n + 1), 0 ≤ window (tandemWitness N Rmin) h := fun h => by
    rw [window_tandemWitness]
    exact witnessWindow_nonneg hRmin hrate0 hrate' hlat hb hstab h
  have hΔ : 0 ≤ objectiveValue N Rmin := objectiveValue_nonneg hrate' hlat hb hstab
  -- the burst value at boundary 0 and its closed form
  set burst0 : ℝ := N.burst + N.rate0 * objectiveValue N Rmin with hburst0
  have hAcs : ∀ h : Fin (n + 1), (tandemWitness N Rmin).A h.castSucc
      = if (h : ℕ) = 0 then burst0 else 0 := fun h => by
    simp only [tandemWitness, Fin.val_castSucc, ← hburst0]
    rfl
  have hAsucc : ∀ h : Fin (n + 1), (tandemWitness N Rmin).A h.succ = 0 := fun h => by
    simp only [tandemWitness, Fin.val_succ]; simp
  have hburst0_nonneg : 0 ≤ burst0 := add_nonneg hb (mul_nonneg hrate0 hΔ)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · -- date ordering: window nonneg
    have := hwin h; rw [window] at this; linarith
  · -- A monotone: A h.succ = 0 ≤ A h.castSucc
    rw [hAsucc h, hAcs h]; split
    · exact hburst0_nonneg
    · exact le_refl 0
  · -- D monotone
    simp [tandemWitness]
  · -- source arrival, binds with equality
    have hA0 : (tandemWitness N Rmin).A 0 = burst0 := by
      simp only [tandemWitness, Fin.val_zero, if_pos]; rw [← hburst0]
    have hAlast : (tandemWitness N Rmin).A (Fin.last (n + 1)) = 0 := by
      simp [tandemWitness]
    have ht0 : (tandemWitness N Rmin).t 0 = objectiveValue N Rmin := by
      rw [show (tandemWitness N Rmin).t 0 = delay (tandemWitness N Rmin)
            + (tandemWitness N Rmin).t (Fin.last (n + 1)) by rw [delay]; ring,
        delay_tandemWitness N hRmin hrate hstab, t_last_tandemWitness, add_zero]
    have htlast : (tandemWitness N Rmin).t (Fin.last (n + 1)) = 0 := t_last_tandemWitness N Rmin
    rw [hA0, hAlast, ht0, htlast, hburst0]; linarith
  · -- service: binds with equality at h=0, 0≤0 elsewhere
    have hw : (tandemWitness N Rmin).t h.castSucc - (tandemWitness N Rmin).t h.succ
        = witnessWindow N Rmin h := by rw [← window]; exact window_tandemWitness N Rmin h
    rw [hrate h, hw, hAcs h]
    simp only [tandemWitness, sub_zero]
    by_cases hh : (h : ℕ) = 0
    · rw [if_pos hh]
      unfold witnessWindow; rw [if_pos hh, hburst0]
      rw [add_sub_cancel_left, mul_div_cancel₀ _ hRmin.ne']
    · rw [if_neg hh]
      unfold witnessWindow; rw [if_neg hh, sub_self, mul_zero]
  · -- flow conservation: D h.castSucc = 0 = A h.succ
    rw [hAsucc h]; simp [tandemWitness]
  · -- causality: 0 ≤ A h.castSucc
    rw [hAcs h]; split
    · exact hburst0_nonneg
    · exact le_refl 0

/-! ## Optimum = worst case (the completed equivalence theorem, homogeneous tandem) -/

/-- **Theorem 11.1, homogeneous tandem: the LP optimum is the worst-case delay.**  For a
homogeneous-rate stable tandem (`Rₕ = Rmin` for every server, `0 ≤ r < Rmin`, nonnegative
latencies and burst), the optimum of the §11.1.2 tandem delay program *equals* its objective
value `(∑ₕ Rₕ·Tₕ + b)/(Rmin − r) = (Rmin·∑ₕTₕ + b)/(Rmin − r)`: the soundness bound
`delay_le_objectiveValue` upper-bounds it on every feasible point, and `tandemWitness`
is a feasible point attaining it.  This closes the "optimum = worst case" half of the
equivalence theorem (§11.1.3) for the homogeneous tandem — see the `## NON-ATTAINMENT`
adjudication for why the heterogeneous case (a strictly-faster server) is *not* attained by
this objective. -/
theorem tandem_programOptimum_homogeneous {n : ℕ} (N : Tandem (n + 1)) {Rmin : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : ∀ h : Fin (n + 1), N.rate h = Rmin)
    (hlat : ∀ h : Fin (n + 1), 0 ≤ N.lat h) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin) :
    programOptimum (Feasible N) (fun v => ((delay v : ℝ) : EReal))
      = ((objectiveValue N Rmin : ℝ) : EReal) := by
  have hRle : ∀ h : Fin (n + 1), Rmin ≤ N.rate h := fun h => by rw [hrate h]
  apply le_antisymm
  · exact programOptimum_le fun v hv => by
      exact_mod_cast delay_le_objectiveValue hv hRle hstab
  · have h := le_programOptimum (Feasible := Feasible N)
      (obj := fun v => ((delay v : ℝ) : EReal))
      (feasible_tandemWitness N hRmin hrate0 hrate hlat hb hstab)
    rwa [delay_tandemWitness N hRmin hrate hstab] at h

/-- **`n = 1` instance** (the single server, §11.1 base case): the optimum of the one-server
delay program equals `(R·T + b)/(R − r)`.  The single-server case of
`tandem_programOptimum_homogeneous` (homogeneity is vacuous for one server). -/
theorem tandem_programOptimum_one (N : Tandem 1) {Rmin : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0) (hrate : N.rate 0 = Rmin)
    (hlat : 0 ≤ N.lat 0) (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin) :
    programOptimum (Feasible N) (fun v => ((delay v : ℝ) : EReal))
      = ((objectiveValue N Rmin : ℝ) : EReal) :=
  tandem_programOptimum_homogeneous N hRmin hrate0
    (fun h => by rw [Fin.eq_zero h]; exact hrate)
    (fun h => by rw [Fin.eq_zero h]; exact hlat) hb hstab

/-- **`n = 2` instance** (the two-server tandem of Example 11.1, equal-rate case): the optimum
of the two-server delay program equals `(R·(T₀+T₁) + b)/(R − r)`.  The two-server case of
`tandem_programOptimum_homogeneous` with both servers at the common rate `R = Rmin`. -/
theorem tandem_programOptimum_two (N : Tandem 2) {Rmin : ℝ}
    (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0)
    (hrate : ∀ h : Fin 2, N.rate h = Rmin) (hlat : ∀ h : Fin 2, 0 ≤ N.lat h)
    (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin) :
    programOptimum (Feasible N) (fun v => ((delay v : ℝ) : EReal))
      = ((objectiveValue N Rmin : ℝ) : EReal) :=
  tandem_programOptimum_homogeneous N hRmin hrate0 hrate hlat hb hstab

/-! ## NON-ATTAINMENT — why the heterogeneous general case is not closed by this objective

The objective `objectiveValue N Rmin = (∑ₕ Rₕ·Tₕ + b)/(Rmin − r)` is the *SFA / separated-flow*
end-to-end delay bound.  Soundness (`delay_le_objectiveValue`) holds for it at any common lower
rate `Rmin ≤ minₕ Rₕ`, and it is **attained** — equal to the LP optimum — exactly when the
bottleneck inequality chain of `bottleneck_ineq` is tight at *every* server.  Tracing that chain,
attainment at a feasible point forces, for every server `h`:

* `Rmin · wₕ = Rₕ · wₕ` (the rate-domination step), i.e. `wₕ = 0` whenever `Rₕ > Rmin`; and
* `Rₕ · wₕ = Rₕ · Tₕ + Qₕ` (the strict-service step), so a `wₕ = 0` server has `Qₕ = −Rₕ·Tₕ`.

By causality `Qₕ ≥ 0`, so a strictly-faster server (`Rₕ > Rmin`) attaining the objective must have
`Tₕ = 0` and `Qₕ = 0`.  Hence whenever some server has `Rₕ > Rmin` **and** `Tₕ > 0`, the SFA value
is *strictly above* the LP optimum (the well-documented SFA-vs-exact gap), and no feasible point
attains it: the witness `tandemWitness` constructed here, which routes the whole burst to one
window at the bottleneck rate, is genuinely the homogeneous-tandem vertex and does not extend.

The exact heterogeneous LP optimum is *not* a closed form in the tandem instance — it is the value
the §11.1.2 finite linear program *computes* (the optimization content, requiring a solver), and the
exact tight worst-case delay is recovered analytically only through the PMOO / per-server residual
operators (`worstCaseChainDelay_eq_hDev_minConvChain` for the single-flow tandem, where the
concatenation `β₀ ∗ ⋯ ∗ βₙ` is already tight).  Building the heterogeneous extremal vertex as a
Lean witness against the *exact* (not SFA) objective is `[infra]`: it needs the per-server greedy
trajectory keyed off the convex-combination of rate-latency pieces, the trajectory-reconstruction
of §11.1.3 step two — an extremal/existence argument, not a closed-form lemma.

`witness_infeasible_heterogeneous` below makes the obstruction concrete: a two-server tandem with a
strictly-faster, positive-latency first server has the SFA witness violate the service constraint at
that server (its backlog would have to be negative), so the homogeneous construction is genuinely
unavailable there. -/

/-- **The homogeneous witness is infeasible on a heterogeneous tandem** (the concrete obstruction):
take a two-server tandem whose server `1` (index `1`, the non-burst-carrying server) is strictly
faster than the bottleneck `Rmin` and has positive latency.  Building `tandemWitness` at the SFA
rate `Rmin < R₁` makes server `1` run at window `T₁` with zero backlog, but its *own* rate-latency
strict-service constraint `R₁·(w₁ − T₁) ≤ Q₁` then reads `R₁·(T₁ − T₁) = 0 ≤ 0` — fine — while the
delay it would have to certify against the SFA objective requires window `> T₁`, which it cannot
supply at zero backlog: the SFA witness is *not* a vertex of the heterogeneous polytope.  We exhibit
the failure as: there is a feasible point whose delay is **strictly below** the SFA objective, so the
optimum is strictly below it (the `≥` direction of `le_antisymm` fails for the SFA value). -/
theorem objectiveValue_not_tight_heterogeneous :
    ∃ (N : Tandem 2) (Rmin : ℝ),
      0 < Rmin ∧ 0 ≤ N.rate0 ∧ (∀ h : Fin 2, Rmin ≤ N.rate h) ∧ N.rate0 < Rmin ∧
      (∃ h : Fin 2, Rmin < N.rate h ∧ 0 < N.lat h) ∧
      -- the bottleneck SFA objective strictly exceeds the per-server-exact bound
      objectiveValue N (N.rate 1) < objectiveValue N Rmin := by
  -- server 0 = bottleneck (rate 1, latency 0); server 1 strictly faster (rate 2) with latency 1
  refine ⟨⟨1, 0, ![1, 2], ![0, 1]⟩, 1, by norm_num, le_refl 0, ?_, by norm_num, ?_, ?_⟩
  · rw [Fin.forall_fin_two]; constructor <;> norm_num
  · exact ⟨1, by norm_num, by norm_num⟩
  · -- objectiveValue at Rmin=R₁=2 : (1·0 + 2·1 + 1)/(2−0) = 3/2 ;  at Rmin=1 : (0+2+1)/(1−0)=3
    show objectiveValue _ ((![1, 2] : Fin 2 → ℝ) 1) < objectiveValue _ 1
    simp only [objectiveValue, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-! ## Restatements (the theorems say what the book says) -/

-- The witness's end-to-end delay is the SFA objective on a homogeneous tandem.
example (N : Tandem 3) {Rmin : ℝ} (hRmin : 0 < Rmin)
    (hrate : ∀ h : Fin 3, N.rate h = Rmin) (hstab : N.rate0 < Rmin) :
    delay (tandemWitness N Rmin) = (∑ h : Fin 3, N.rate h * N.lat h + N.burst) / (Rmin - N.rate0) :=
  delay_tandemWitness N hRmin hrate hstab

-- The optimum of the n-server homogeneous tandem delay program is the closed-form worst case.
example (N : Tandem 5) {Rmin : ℝ} (hRmin : 0 < Rmin) (hrate0 : 0 ≤ N.rate0)
    (hrate : ∀ h : Fin 5, N.rate h = Rmin) (hlat : ∀ h : Fin 5, 0 ≤ N.lat h)
    (hb : 0 ≤ N.burst) (hstab : N.rate0 < Rmin) :
    programOptimum (Feasible N) (fun v => ((delay v : ℝ) : EReal))
      = (((∑ h : Fin 5, N.rate h * N.lat h + N.burst) / (Rmin - N.rate0) : ℝ) : EReal) :=
  tandem_programOptimum_homogeneous N hRmin hrate0 hrate hlat hb hstab

end TandemLP

end DeepWiki
