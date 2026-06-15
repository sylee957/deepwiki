import DeepWiki.NetworkCalculus.WorstCaseLP

/-! # Worst-case backlog of a single server (Theorem 11.1, backlog form)
The backlog companion of `worstCaseServerDelay_eq_hDev`. The worst-case backlog
over all `α`-arrival-constrained, `β`-served trajectories is the closed-form
vertical deviation `vDev(α, β)`: the bound `b ≤ vDev` holds on every feasible
trajectory, and the greedy pair `(α, α ∗ β)` attains it. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The worst-case backlog of a single server: the supremum of the realized
backlog over every feasible (`α`-arrival-constrained, `β`-served) trajectory —
the optimum of the single-node worst-case backlog program. -/
noncomputable def worstCaseServerBacklog (α : ℝ≥0 → ℝ≥0) (β : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) // ServerFeasible α β p.1 p.2},
    Deviation.backlog p.1.1 p.1.2

/-- **Single-server worst-case backlog = vertical deviation** (the backlog form of
Theorem 11.1): for monotone sub-additive `α ∈ ℱ₀` and `β` null at the origin,
`worstCaseServerBacklog α β = vDev(α, β)`. The bound `b ≤ vDev` holds on every
feasible trajectory, and the greedy pair `(α, α ∗ β)` is feasible and attains it. -/
theorem worstCaseServerBacklog_eq_vDev {α : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : IsNullAtOrigin α) (hαsub : IsSubadditive α)
    (hβ0 : β 0 = 0) :
    worstCaseServerBacklog α β = (vDev (Deviation.liftENN α) β : ℝ≥0∞) := by
  apply le_antisymm
  · -- every feasible trajectory's backlog is below the bound
    refine iSup_le fun p => ?_
    obtain ⟨_, harr, hserv⟩ := p.2
    exact Deviation.backlog_le_vDev harr hserv
  · -- the greedy pair `(α, α ∗ β)` is feasible and attains the bound
    have hle : ∀ t, minConv (Deviation.liftENN α) β t ≤ (α t : ℝ≥0∞) := fun t => by
      have h := minConv_le_add (Deviation.liftENN α) β (add_zero t)
      rwa [hβ0, add_zero] at h
    have hne : ∀ t, minConv (Deviation.liftENN α) β t ≠ ⊤ := fun t =>
      ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := α t)) (hle t)
    set D : ℝ≥0 → ℝ≥0 := fun t => (minConv (Deviation.liftENN α) β t).toNNReal with hDdef
    have hD : ∀ t, (D t : ℝ≥0∞) = minConv (Deviation.liftENN α) β t := fun t =>
      ENNReal.coe_toNNReal (hne t)
    have harr : IsMaximalArrivalBound (Deviation.liftENN α) (Deviation.liftENN α) :=
      isMaximalArrivalBound_self_of_subadditive hαsub.liftENN
    have hfeas : ServerFeasible α β α D := ⟨hαmono, harr, fun t => (hD t).ge⟩
    have hbacklog : Deviation.backlog α D = (vDev (Deviation.liftENN α) β : ℝ≥0∞) :=
      Deviation.backlog_eq_vDev_of_minConv_eq hα0 hαsub hD
    rw [← hbacklog]
    exact le_iSup
      (fun p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) // ServerFeasible α β p.1 p.2} =>
        Deviation.backlog p.1.1 p.1.2) ⟨(α, D), hfeas⟩

end DeepWiki
