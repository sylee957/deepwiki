import DeepWiki.NetworkCalculus.WorstCaseLPTandem
import DeepWiki.NetworkCalculus.DeviationsCompositionChain

/-! # Tight worst-case delay through an n-server tandem
The arbitrary-length single-flow generalization of `worstCaseTandemDelay_eq_hDev_conv`.
A flow served by a chain of servers `β₀ :: βs` from input `A_in` to output `A_out`
(`ChainServed`, with the per-hop intermediates existentially quantified) has its
per-hop service constraints collapse — by `minConv` associativity, inductively — to
`A_in` served by the full chain convolution `minConvChain β₀ βs`. So the worst-case
end-to-end delay `worstCaseChainDelay` is the closed form `hDev(α, β₀ ∗ β₁ ∗ ⋯)`: the
bound holds on every feasible trajectory, and the greedy chain (each hop convolved
exactly) attains it. Recovers the single-server (`βs = []`) and two-server cases. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- A flow input `A_in` is **served by the server chain** `β₀ :: βs` into output
`A_out`: server `β₀` serves `A_in` into an intermediate, recursively served by the
rest of the chain into `A_out` (the intermediate cumulative functions are
existentially quantified). -/
def ChainServed (β₀ : ℝ≥0 → ℝ≥0∞) :
    List (ℝ≥0 → ℝ≥0∞) → (ℝ≥0 → ℝ≥0) → (ℝ≥0 → ℝ≥0) → Prop
  | [], A_in, A_out => ∀ t, minConv (Deviation.liftENN A_in) β₀ t ≤ (A_out t : ℝ≥0∞)
  | γ :: rest, A_in, A_out =>
      ∃ B : ℝ≥0 → ℝ≥0, (∀ t, minConv (Deviation.liftENN A_in) β₀ t ≤ (B t : ℝ≥0∞)) ∧
        ChainServed γ rest B A_out

/-- **End-to-end chain collapse**: a flow served by the chain `β₀ :: βs` is served
by the chain convolution `minConvChain β₀ βs` — `minConv` associativity and
monotonicity, inductively over the chain. -/
theorem minConv_minConvChain_le_of_chainServed (β₀ : ℝ≥0 → ℝ≥0∞)
    (βs : List (ℝ≥0 → ℝ≥0∞)) (A_in A_out : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    ChainServed β₀ βs A_in A_out →
      minConv (Deviation.liftENN A_in) (minConvChain β₀ βs) t ≤ (A_out t : ℝ≥0∞) := by
  induction βs generalizing β₀ A_in A_out with
  | nil => intro hserv; rw [minConvChain_nil]; exact hserv t
  | cons γ rest ih =>
    intro hserv
    obtain ⟨B, hB, hrest⟩ := hserv
    rw [minConvChain_cons]
    calc minConv (Deviation.liftENN A_in) (minConv β₀ (minConvChain γ rest)) t
        = minConv (minConv (Deviation.liftENN A_in) β₀) (minConvChain γ rest) t := by
          rw [minConv_assoc_enn]
      _ ≤ minConv (Deviation.liftENN B) (minConvChain γ rest) t :=
          minConv_le_minConv hB (fun _ => le_rfl) t
      _ ≤ (A_out t : ℝ≥0∞) := ih γ B A_out hrest

/-- **The greedy chain trajectory exists and realizes the chain convolution
exactly**: for any input `A_in`, convolving exactly at each hop yields an output
served by the chain with `A_out = A_in ∗ (minConvChain β₀ βs)`. Needs each server
null at the origin (`β 0 = 0`) for the per-hop convolutions to stay finite. -/
theorem exists_chainServed_greedy (β₀ : ℝ≥0 → ℝ≥0∞) (βs : List (ℝ≥0 → ℝ≥0∞))
    (hβ₀0 : β₀ 0 = 0) (hβs0 : ∀ γ ∈ βs, γ 0 = 0) (A_in : ℝ≥0 → ℝ≥0) :
    ∃ A_out : ℝ≥0 → ℝ≥0, ChainServed β₀ βs A_in A_out ∧
      ∀ t, (A_out t : ℝ≥0∞) = minConv (Deviation.liftENN A_in) (minConvChain β₀ βs) t := by
  induction βs generalizing β₀ A_in with
  | nil =>
    refine ⟨fun t => (minConv (Deviation.liftENN A_in) β₀ t).toNNReal, ?_, ?_⟩
    · intro t
      exact (ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := A_in t))
        (minConv_le_left (Deviation.liftENN A_in) hβ₀0 t))).ge
    · intro t
      rw [minConvChain_nil]
      exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := A_in t))
        (minConv_le_left (Deviation.liftENN A_in) hβ₀0 t))
  | cons γ rest ih =>
    set B : ℝ≥0 → ℝ≥0 := fun t => (minConv (Deviation.liftENN A_in) β₀ t).toNNReal with hBdef
    have hB : ∀ t, (B t : ℝ≥0∞) = minConv (Deviation.liftENN A_in) β₀ t := fun t =>
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := A_in t))
        (minConv_le_left (Deviation.liftENN A_in) hβ₀0 t))
    have hBf : Deviation.liftENN B = minConv (Deviation.liftENN A_in) β₀ := funext hB
    obtain ⟨A_out, hserv, hAout⟩ :=
      ih γ (hβs0 γ (List.mem_cons_self ..)) (fun δ hδ => hβs0 δ (List.mem_cons_of_mem _ hδ)) B
    refine ⟨A_out, ⟨B, fun t => (hB t).ge, hserv⟩, fun t => ?_⟩
    rw [hAout t, hBf, minConvChain_cons, minConv_assoc_enn]

/-- The worst-case end-to-end delay of an n-server tandem (`β₀ :: βs`): the
supremum of the realized delay `d(A_in, A_out)` over every monotone,
`α`-arrival-constrained input served by the chain — the optimum of the chain
worst-case program. -/
noncomputable def worstCaseChainDelay (α : ℝ≥0 → ℝ≥0) (β₀ : ℝ≥0 → ℝ≥0∞)
    (βs : List (ℝ≥0 → ℝ≥0∞)) : ℝ≥0∞ :=
  ⨆ p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) // Monotone p.1 ∧
      IsMaximalArrivalBound (Deviation.liftENN p.1) (Deviation.liftENN α) ∧
      ChainServed β₀ βs p.1 p.2}, Deviation.delay p.1.1 p.1.2

/-- **n-server tandem worst-case delay = `hDev(α, β₀ ∗ β₁ ∗ ⋯)`** (the
arbitrary-length single-flow instance of Theorem 11.1): for monotone sub-additive
`α ∈ ℱ₀` and monotone servers `∈ ℱ₀`, the worst-case end-to-end delay through the
tandem `β₀ :: βs` equals the horizontal deviation against the chain convolution.
The bound holds on every feasible trajectory (the chain collapse +
`delay_le_hDev`), and the greedy chain attains it. Generalizes
`worstCaseTandemDelay_eq_hDev_conv`. -/
theorem worstCaseChainDelay_eq_hDev_minConvChain {α : ℝ≥0 → ℝ≥0} {β₀ : ℝ≥0 → ℝ≥0∞}
    {βs : List (ℝ≥0 → ℝ≥0∞)} (hαmono : Monotone α) (hα0 : IsNullAtOrigin α)
    (hαsub : IsSubadditive α) (hβ₀mono : Monotone β₀) (hβsmono : ∀ γ ∈ βs, Monotone γ)
    (hβ₀0 : β₀ 0 = 0) (hβs0 : ∀ γ ∈ βs, γ 0 = 0) :
    worstCaseChainDelay α β₀ βs
      = (hDev (Deviation.liftENN α) (minConvChain β₀ βs) : ℝ≥0∞) := by
  have hchainmono : Monotone (minConvChain β₀ βs) := monotone_minConvChain hβ₀mono hβsmono
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨hA, harr, hserv⟩ := p.2
    exact Deviation.delay_le_hDev hA hchainmono harr
      (fun t => minConv_minConvChain_le_of_chainServed β₀ βs p.1.1 p.1.2 t hserv)
  · obtain ⟨A_out, hserv, hAout⟩ := exists_chainServed_greedy β₀ βs hβ₀0 hβs0 α
    have harr : IsMaximalArrivalBound (Deviation.liftENN α) (Deviation.liftENN α) :=
      isMaximalArrivalBound_self_of_subadditive hαsub.liftENN
    have hdelay : Deviation.delay α A_out
        = (hDev (Deviation.liftENN α) (minConvChain β₀ βs) : ℝ≥0∞) :=
      Deviation.delay_eq_hDev_of_minConv_eq hαmono hα0 hαsub hchainmono hAout
    rw [← hdelay]
    exact le_iSup (fun p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) // Monotone p.1 ∧
        IsMaximalArrivalBound (Deviation.liftENN p.1) (Deviation.liftENN α) ∧
        ChainServed β₀ βs p.1 p.2} => Deviation.delay p.1.1 p.1.2)
      ⟨(α, A_out), hαmono, harr, hserv⟩

end DeepWiki
