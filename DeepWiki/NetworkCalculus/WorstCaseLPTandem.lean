import DeepWiki.NetworkCalculus.WorstCaseLP
import DeepWiki.NetworkCalculus.Additivity

/-! # Tight worst-case delay through a two-server tandem
The two-server instance of the worst-case-equals-optimum equivalence
(Theorem 11.1) for a single flow under tandem service. A feasible tandem
trajectory `(A₀, A₁, A₂)` has `A₀` arrival-constrained and is served by `β₁`
into `A₁`, then by `β₂` into `A₂`; the service constraints collapse — by `minConv`
associativity — to `A₀` served by the concatenation `β₁ ∗ β₂` into `A₂`. So the
worst-case end-to-end delay `worstCaseTandemDelay` is exactly the closed form
`hDev(α, β₁ ∗ β₂)`: the concatenation bound holds on every feasible trajectory,
and the greedy trajectory `(α, α ∗ β₁, α ∗ (β₁ ∗ β₂))` attains it. This is the
two-hop generalization of `worstCaseServerDelay_eq_hDev`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- A feasible 2-server tandem trajectory for a flow with arrival curve `α`:
`A₀` is monotone and `α`-arrival-constrained, server 1 (`β₁`) serves `(A₀, A₁)`
and server 2 (`β₂`) serves `(A₁, A₂)` (in the `ℝ≥0∞` reading). -/
def TandemFeasible (α : ℝ≥0 → ℝ≥0) (β₁ β₂ : ℝ≥0 → ℝ≥0∞) (A₀ A₁ A₂ : ℝ≥0 → ℝ≥0) : Prop :=
  Monotone A₀ ∧ IsMaximalArrivalBound (Deviation.liftENN A₀) (Deviation.liftENN α) ∧
    (∀ t, minConv (Deviation.liftENN A₀) β₁ t ≤ (A₁ t : ℝ≥0∞)) ∧
    (∀ t, minConv (Deviation.liftENN A₁) β₂ t ≤ (A₂ t : ℝ≥0∞))

/-- **End-to-end collapse**: a feasible tandem trajectory has `A₀` served by the
concatenation `β₁ ∗ β₂` into `A₂` — `minConv` associativity rewrites
`(A₀ ∗ β₁) ∗ β₂` as `A₀ ∗ (β₁ ∗ β₂)`, and monotonicity carries the per-hop
inequalities through. -/
theorem minConv_minConv_le_of_tandemFeasible {α : ℝ≥0 → ℝ≥0} {β₁ β₂ : ℝ≥0 → ℝ≥0∞}
    {A₀ A₁ A₂ : ℝ≥0 → ℝ≥0} (hfeas : TandemFeasible α β₁ β₂ A₀ A₁ A₂) (t : ℝ≥0) :
    minConv (Deviation.liftENN A₀) (minConv β₁ β₂) t ≤ (A₂ t : ℝ≥0∞) := by
  obtain ⟨_, _, hserv1, hserv2⟩ := hfeas
  calc minConv (Deviation.liftENN A₀) (minConv β₁ β₂) t
      = minConv (minConv (Deviation.liftENN A₀) β₁) β₂ t := by rw [minConv_assoc_enn]
    _ ≤ minConv (Deviation.liftENN A₁) β₂ t := minConv_le_minConv hserv1 (fun _ => le_rfl) t
    _ ≤ (A₂ t : ℝ≥0∞) := hserv2 t

/-- The worst-case end-to-end delay of a two-server tandem: the supremum of the
realized delay `d(A₀, A₂)` over every feasible tandem trajectory — the optimum of
the tandem worst-case program. -/
noncomputable def worstCaseTandemDelay (α : ℝ≥0 → ℝ≥0) (β₁ β₂ : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) //
      TandemFeasible α β₁ β₂ p.1 p.2.1 p.2.2}, Deviation.delay p.1.1 p.1.2.2

/-- **Two-server tandem worst-case delay = `hDev(α, β₁ ∗ β₂)`** (the two-hop
instance of Theorem 11.1): for a monotone sub-additive `α ∈ ℱ₀` and monotone
`β₁, β₂ ∈ ℱ₀`, the worst-case end-to-end delay equals the horizontal deviation
against the concatenated service curve. The bound holds on every feasible
trajectory (`minConv_minConv_le_of_tandemFeasible` + `delay_le_hDev`); the greedy
trajectory `(α, α ∗ β₁, α ∗ (β₁ ∗ β₂))` is feasible and attains it. -/
theorem worstCaseTandemDelay_eq_hDev_conv {α : ℝ≥0 → ℝ≥0} {β₁ β₂ : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : IsNullAtOrigin α) (hαsub : IsSubadditive α)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂) (hβ₁0 : β₁ 0 = 0) (hβ₂0 : β₂ 0 = 0) :
    worstCaseTandemDelay α β₁ β₂ = (hDev (Deviation.liftENN α) (minConv β₁ β₂) : ℝ≥0∞) := by
  have hβmono : Monotone (minConv β₁ β₂) := monotone_minConv hβ₁mono hβ₂mono
  have hβ0 : minConv β₁ β₂ 0 = 0 :=
    le_antisymm (le_of_le_of_eq (minConv_le_left β₁ hβ₂0 0) hβ₁0) bot_le
  apply le_antisymm
  · -- every feasible trajectory's delay is below the concatenation bound
    refine iSup_le fun p => ?_
    obtain ⟨hA0, harr, _, _⟩ := p.2
    exact Deviation.delay_le_hDev hA0 hβmono harr (minConv_minConv_le_of_tandemFeasible p.2)
  · -- the greedy tandem trajectory `(α, α ∗ β₁, α ∗ (β₁ ∗ β₂))` attains the bound
    set A₁ : ℝ≥0 → ℝ≥0 := fun t => (minConv (Deviation.liftENN α) β₁ t).toNNReal with hA1def
    set A₂ : ℝ≥0 → ℝ≥0 := fun t => (minConv (Deviation.liftENN α) (minConv β₁ β₂) t).toNNReal
      with hA2def
    have hA1 : ∀ t, (A₁ t : ℝ≥0∞) = minConv (Deviation.liftENN α) β₁ t := fun t =>
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := α t))
        (minConv_le_left (Deviation.liftENN α) hβ₁0 t))
    have hA2 : ∀ t, (A₂ t : ℝ≥0∞) = minConv (Deviation.liftENN α) (minConv β₁ β₂) t := fun t =>
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := α t))
        (minConv_le_left (Deviation.liftENN α) hβ0 t))
    have hA1f : Deviation.liftENN A₁ = minConv (Deviation.liftENN α) β₁ := funext hA1
    have harr : IsMaximalArrivalBound (Deviation.liftENN α) (Deviation.liftENN α) :=
      isMaximalArrivalBound_self_of_subadditive hαsub.liftENN
    have hfeas : TandemFeasible α β₁ β₂ α A₁ A₂ := by
      refine ⟨hαmono, harr, fun t => (hA1 t).ge, fun t => ?_⟩
      rw [hA1f, minConv_assoc_enn, hA2 t]
    have hdelay : Deviation.delay α A₂ = (hDev (Deviation.liftENN α) (minConv β₁ β₂) : ℝ≥0∞) :=
      Deviation.delay_eq_hDev_of_minConv_eq hαmono hα0 hαsub hβmono hA2
    rw [← hdelay]
    exact le_iSup (fun p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) //
        TandemFeasible α β₁ β₂ p.1 p.2.1 p.2.2} => Deviation.delay p.1.1 p.1.2.2)
      ⟨(α, A₁, A₂), hfeas⟩

end DeepWiki
