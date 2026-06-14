import Book.ServersConcatenation
import Book.ServersConcatenationStrict
import Book.ServiceCurveStrictTandem
import Book.ServersControlTandem
import Book.ServersControlFeedback
import Book.ServersControlFeedbackWindow
import Book.ServersJitter
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 6: Single Flow Crossing Several Servers
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-- **Definition 6.1** (§6.1.1, p.130): Concatenation of servers: S₂ ∘ S₁ = {(A,C) | ∃B, (A,B)∈S₁ ∧ (B,C)∈S₂}; with S⁰ = {(A,A)} and Sⁿ⁺¹ = S ∘ Sⁿ. -/
abbrev def_6_1 := @compPow

/-- **Proposition 6.1** (§6.1.1, p.130): If S₁ and S₂ are two servers, then so is the concatenation S₂ ∘ S₁. -/
alias prop_6_1 := IsServer.comp

/-! **Theorem 6.1** (§6.1.1, p.131): Concatenation of servers in a convolution: a flow crossing two servers offering β₁, β₂ is offered β₁ ∗ β₂ — Smp(β₂)∘Smp(β₁) ⊆ Smp(β₁∗β₂), and likewise for maximal curves Smax(β₂)∘Smax(β₁) ⊆ Smax(β₁∗β₂). Library: comp_minimalServiceRel_le, comp_maximalServiceRel_le. -/

/-- **Remark 6.1** (§6.1.1, p.132): The convolution is commutative but the composition is not, so the inclusion of Theorem 6.1 can be strict: Smp(β₂)∘Smp(β₁) ⊊ Smp(β₁∗β₂) (Figure 6.3, with β₁=δ₃, β₂=λ₁). -/
alias remark_6_1_strict := comp_minimalServiceRel_lt_delay_rate

/-- **Proposition 6.2** (§6.1.3, p.134): Strict service curves do not compose in general: if β₁, β₂ vanish at positive T₁, T₂, there is β>0 with Sstrict(β₂)∘Sstrict(β₁) ⊄ Sstrict(β) — relation form: the only β with the composition ⊆ Sstrict(β) is β=0. -/
alias prop_6_2 := eq_zero_of_comp_strictServiceRel_le

/-! **Proposition 6.3** (§6.2.1, p.136): Tandem control: the smallest controller β_c with β_c ∗ β ≥ β_ref is the deconvolution β̂_c = ⋀{β_c | β_c∗β ≥ β_ref} = β_ref ⊘ β. Library: isLeast_tandemControlSet, sInf_tandemControlSet. -/

/-! **Proposition 6.4** (§6.2.1, p.136): Delay requirement: if α ≤ (β ⊘ δ_τ)⋆ then hDev(α,β) ≤ τ; moreover (β ⊘ δ_τ)⋆ is the largest sub-additive function with this property. Library: hDev_le_of_le_subadditiveClosureENN_minDeconv, le_subadditiveClosureENN_minDeconv_of_isSubadditive, subadditiveClosureENN_subadditive. -/

/-! **Proposition 6.5** (§6.2.1, p.137): Backlog requirement: if α ≤ (β + b)⋆ then vDev(α,β) ≤ b; moreover (β + b)⋆ is the largest sub-additive function with this property. Library: vDev_le_of_le_subadditiveClosureENN_add, le_subadditiveClosureENN_add_of_isSubadditive, subadditiveClosureENN_subadditive. -/

/-- **Proposition 6.6** (§6.2.2, p.138): Feedback control: the smallest controller β_c with β ∗ (β_c∗β)⋆ ≥ β_ref must satisfy ∀n∈ℕ, β_cⁿ ≥ β_ref ⊘ βⁿ⁺¹ (residuation + associativity of convolution). -/
alias prop_6_6 := mem_feedbackControlSet_iff

/-- **Proposition 6.7** (§6.2.2, p.138): Window flow control: the controlled network of Figure 6.8 has minimal min-plus service curve β_wfc = β ∗ (ω_w ∗ β)⋆. -/
alias prop_6_7 := windowFlowControl_minConv_le

/-! **Proposition 6.8** (§6.2.2, p.139): If w ≥ (β ⊘ β²)(0), then β_wfc ≥ β (and hence β_wfc = β, since the closure vanishes at the origin). Library: window_mem_feedbackControlSet_self, minConv_subadditiveClosureENN_window_eq. -/

/-- **Lemma 6.1** (§6.2.2, p.139): If β_c ≥ β ⊘ β², then for all n∈ℕ, β_cⁿ ≥ β ⊘ βⁿ⁺¹ (so β_c is admissible for the reference β itself). -/
alias lemma_6_1 := mem_feedbackControlSet_self_of_minDeconv_le

/-! **Proposition 6.9** (§6.2.2, p.140): Window flow control with acknowledgments: if w ≥ ((β⊘β) ⊘ (β_ack∗β))(0), then β_wfc-ack = β ∗ (ω_w∗β_ack∗β)⋆ ≥ β. Library: windowAck_mem_feedbackControlSet_self, minConv_subadditiveClosureENN_windowAck_eq. -/

/-! **Theorem 6.2** (§6.3.1.2, p.143): Server as a jitter: if every bit's delay lies between dᵐ and dᴹ, the server offers maximal service curve δ_dᵐ (infₜ d≥dᵐ ⟹ D ≤ A∗δ_dᵐ) and min-plus service curve δ_dᴹ (d≤dᴹ ⟹ A∗δ_dᴹ ≤ D, for left-continuous A). Library: Deviation.le_apply_tsub_of_le_delayAt, Deviation.apply_tsub_le_of_delay_le, Deviation.apply_tsub_le_of_delay_le_of_leftCont. -/

/-! **Corollary 6.1** (§6.3.1.2, p.143): Service curve for a jitter: a server offering min-plus service curve β to an α-constrained arrival also offers the pure-delay min-plus curve δ_{dM} for any dM ≥ hDev(α,β). Library: Deviation.apply_tsub_le_of_hDev_lt, Deviation.apply_tsub_le_of_hDev_le_of_leftCont. -/

end DeepWiki.Dnc
