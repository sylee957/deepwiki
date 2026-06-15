import DeepWiki.NetworkCalculus.WorstCaseLPTandemChain
import DeepWiki.NetworkCalculus.WorstCaseLPBacklog

/-! # Worst-case end-to-end backlog through a tandem (Theorem 11.1, backlog form)
The backlog companion of `worstCaseChainDelay_eq_hDev_minConvChain`. The worst-case
end-to-end backlog `b(A_in, A_out)` (total in-flight data) of a single flow served
by a tandem `β₀ :: βs` equals the vertical deviation against the chain convolution,
`vDev(α, β₀ ∗ β₁ ∗ ⋯)`: the chain collapse bounds it on every feasible trajectory,
and the greedy chain attains it. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The worst-case end-to-end backlog of a tandem (`β₀ :: βs`): the supremum of the
realized backlog `b(A_in, A_out)` over every feasible chain trajectory. -/
noncomputable def worstCaseChainBacklog (α : ℝ≥0 → ℝ≥0) (β₀ : ℝ≥0 → ℝ≥0∞)
    (βs : List (ℝ≥0 → ℝ≥0∞)) : ℝ≥0∞ :=
  ⨆ p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) // Monotone p.1 ∧
      IsMaximalArrivalBound (Deviation.liftENN p.1) (Deviation.liftENN α) ∧
      ChainServed β₀ βs p.1 p.2}, Deviation.backlog p.1.1 p.1.2

/-- **n-server tandem worst-case backlog = `vDev(α, β₀ ∗ β₁ ∗ ⋯)`** (the backlog
form of Theorem 11.1): for monotone sub-additive `α ∈ ℱ₀` and servers null at the
origin, the worst-case end-to-end backlog through the tandem `β₀ :: βs` equals the
vertical deviation against the chain convolution. The bound holds on every feasible
trajectory (the chain collapse + `backlog_le_vDev`), and the greedy chain attains
it. -/
theorem worstCaseChainBacklog_eq_vDev_minConvChain {α : ℝ≥0 → ℝ≥0} {β₀ : ℝ≥0 → ℝ≥0∞}
    {βs : List (ℝ≥0 → ℝ≥0∞)} (hαmono : Monotone α) (hα0 : IsNullAtOrigin α)
    (hαsub : IsSubadditive α) (hβ₀0 : β₀ 0 = 0) (hβs0 : ∀ γ ∈ βs, γ 0 = 0) :
    worstCaseChainBacklog α β₀ βs
      = (vDev (Deviation.liftENN α) (minConvChain β₀ βs) : ℝ≥0∞) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨_, harr, hserv⟩ := p.2
    exact Deviation.backlog_le_vDev harr
      (fun t => minConv_minConvChain_le_of_chainServed β₀ βs p.1.1 p.1.2 t hserv)
  · obtain ⟨A_out, hserv, hAout⟩ := exists_chainServed_greedy β₀ βs hβ₀0 hβs0 α
    have harr : IsMaximalArrivalBound (Deviation.liftENN α) (Deviation.liftENN α) :=
      isMaximalArrivalBound_self_of_subadditive hαsub.liftENN
    have hbacklog : Deviation.backlog α A_out
        = (vDev (Deviation.liftENN α) (minConvChain β₀ βs) : ℝ≥0∞) :=
      Deviation.backlog_eq_vDev_of_minConv_eq hα0 hαsub hAout
    rw [← hbacklog]
    exact le_iSup (fun p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) // Monotone p.1 ∧
        IsMaximalArrivalBound (Deviation.liftENN p.1) (Deviation.liftENN α) ∧
        ChainServed β₀ βs p.1 p.2} => Deviation.backlog p.1.1 p.1.2)
      ⟨(α, A_out), hαmono, harr, hserv⟩

end DeepWiki
