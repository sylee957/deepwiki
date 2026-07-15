import DeepWiki.NetworkCalculus.ArrivalCurves
import DeepWiki.NetworkCalculus.ArrivalCurvesCombined
import DeepWiki.NetworkCalculus.ArrivalCurvesMaximal
import DeepWiki.NetworkCalculus.ArrivalCurvesMinimal
import DeepWiki.NetworkCalculus.ArrivalCurvesOutput
import DeepWiki.NetworkCalculus.ArrivalCurvesShaper
import DeepWiki.NetworkCalculus.ArrivalCurvesShaperGreedy
import DeepWiki.NetworkCalculus.Deviations
import DeepWiki.NetworkCalculus.DeviationsBounds
import DeepWiki.NetworkCalculus.DeviationsBoundsServer
import DeepWiki.NetworkCalculus.DeviationsBoundsTight
import DeepWiki.NetworkCalculus.DeviationsContinuity
import DeepWiki.NetworkCalculus.DeviationsPseudoInverse
import DeepWiki.NetworkCalculus.DeviationsRestricted
import DeepWiki.NetworkCalculus.ServersBacklog
import DeepWiki.NetworkCalculus.ServiceCurveMaximal
import DeepWiki.NetworkCalculus.ServiceCurveMinimal
import DeepWiki.NetworkCalculus.ServiceCurveStrict
import DeepWiki.NetworkCalculus.ServiceCurveStrictMinimal
import DeepWiki.NetworkCalculus.ServiceCurveWeaklyStrict
import Sources.Doi_10_1002_9781119440284.Source

/-! # DNC catalog — Chapter 5: Network Calculus Basics: a Server Crossed by a Single Flow
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-! **Definition 5.0** (§5.1, p.100): Vertical/horizontal deviation and backlog/delay of two cumulative functions: vDev(f,g,t)=f(t)-g(t), hDev(f,g,t)=inf{d|f(t)≤g(t+d)}, b(A,D)=vDev(A,D), d(A,D)=hDev(A,D). -/
/-- **Definition 5.0** (linked: `vDev`). -/
noncomputable def def_5_0_1 := @vDev
/-- **Definition 5.0** (linked: `hDev`). -/
noncomputable def def_5_0_2 := @hDev
/-- **Definition 5.0** (linked: `Deviation.backlog`). -/
noncomputable def def_5_0_3 := @Deviation.backlog
/-- **Definition 5.0** (linked: `Deviation.delay`). -/
noncomputable def def_5_0_4 := @Deviation.delay

/-- **Definition 5.1** (§5.1, p.100): Maximal (upper) arrival curve α∈ℱ↑ for cumulative function A: A ≤ A ∗ α. -/
noncomputable def def_5_1 := @IsMaximalArrivalCurve

/-- **Definition 5.2** (§5.1, p.101): Minimal (lower) arrival curve α'∈ℱ↑ for A: A ⊼ α' ≤ A (max-plus convolution). -/
noncomputable def def_5_2 := @IsMinimalArrivalCurve

/-- **Proposition 5.1** (§5.1, p.102): Equivalent definition of an arrival curve: A ≤ A ∗ α iff A(t+d)-A(t) ≤ α(d) for all t,d (and the dual increment form for the minimal curve). -/
alias prop_5_1 := isMaximalArrivalBound_iff_increment

/-! **Proposition 5.2** (§5.1, p.102): Properties of maximal arrival curves: α* and its sub-additive closure are maximal arrival curves, any α'≥α maximal is maximal, A⊘A is a (least) maximal arrival curve, and the left-continuous extension is one too. -/
/-- **Proposition 5.2** (linked: `isMaximalArrivalBound_minDeconv_self`). -/
alias prop_5_2_1 := isMaximalArrivalBound_minDeconv_self
/-- **Proposition 5.2** (linked: `minDeconv_self_le_of_isMaximalArrivalBound`). -/
alias prop_5_2_2 := minDeconv_self_le_of_isMaximalArrivalBound
/-- **Proposition 5.2** (linked: `IsMaximalArrivalBound.mono`). -/
alias prop_5_2_3 := IsMaximalArrivalBound.mono
/-- **Proposition 5.2** (linked: `IsMaximalArrivalCurve.subadditiveClosureENN`). -/
alias prop_5_2_4 := IsMaximalArrivalCurve.subadditiveClosureENN
/-- **Proposition 5.2** (linked: `IsMaximalArrivalBound.subadditiveClosureMin`). -/
alias prop_5_2_5 := IsMaximalArrivalBound.subadditiveClosureMin
/-- **Proposition 5.2** (linked: `isMaximalArrivalBound_leftLim_of_isLeftContinuous`). -/
alias prop_5_2_6 := isMaximalArrivalBound_leftLim_of_isLeftContinuous
/-- **Proposition 5.2** (the infimum facet, §5.1, p.102; cited by the proof of Corollary 7.2):
the pointwise infimum of a family of maximal arrival curves for one process is again a maximal
arrival curve. Linked: `isMaximalArrivalBound_iInf`. -/
alias prop_5_2_7 := isMaximalArrivalBound_iInf

/-! **Corollary 5.1** (§5.1, p.103): If A admits a maximal (resp. minimal) arrival curve it admits a non-decreasing left- (resp. right-) continuous one: the left/right-limit extension is again an arrival curve. -/
/-- **Corollary 5.1** (linked: `isMaximalArrivalBound_leftLim_of_isLeftContinuous`). -/
alias cor_5_1_1 := isMaximalArrivalBound_leftLim_of_isLeftContinuous
/-- **Corollary 5.1** (linked: `isMaximalArrivalBound_leftLim_of_isRightContinuous`). -/
alias cor_5_1_2 := isMaximalArrivalBound_leftLim_of_isRightContinuous
/-- **Corollary 5.1** (linked: `isMinimalArrivalBound_rightLim_of_isRightContinuous`). -/
alias cor_5_1_3 := isMinimalArrivalBound_rightLim_of_isRightContinuous
/-- **Corollary 5.1** (linked: `isMinimalArrivalBound_rightLim_of_isLeftContinuous`). -/
alias cor_5_1_4 := isMinimalArrivalBound_rightLim_of_isLeftContinuous

/-! **Proposition 5.3** (§5.1, p.104): Properties of minimal arrival curves (dual of Prop 5.2): α'* and the super-additive closure are minimal arrival curves, any α''≤α' is minimal, A⊘̄A is a (greatest) minimal arrival curve, and the right-continuous extension is one too. -/
/-- **Proposition 5.3** (linked: `isMinimalArrivalBound_maxDeconv_self`). -/
alias prop_5_3_1 := isMinimalArrivalBound_maxDeconv_self
/-- **Proposition 5.3** (linked: `le_maxDeconv_self_of_isMinimalArrivalBound`). -/
alias prop_5_3_2 := le_maxDeconv_self_of_isMinimalArrivalBound
/-- **Proposition 5.3** (linked: `IsMinimalArrivalBound.mono`). -/
alias prop_5_3_3 := IsMinimalArrivalBound.mono
/-- **Proposition 5.3** (linked: `IsMinimalArrivalBound.superadditiveClosureMax`). -/
alias prop_5_3_4 := IsMinimalArrivalBound.superadditiveClosureMax
/-- **Proposition 5.3** (linked: `isMinimalArrivalBound_rightLim_of_isRightContinuous`). -/
alias prop_5_3_5 := isMinimalArrivalBound_rightLim_of_isRightContinuous

/-! **Theorem 5.1** (§5.1, p.105): Combining a minimal αˡ and maximal αᵘ arrival curve: ηᵘ=αᵘ⊘̄αˡ refines the maximal and ηˡ=αˡ⊘αᵘ the minimal curve; under sub- /super-additivity with vanishing at 0 the refinement fixes in one step and the sub- /super-additive closures are again arrival curves. -/
/-- **Theorem 5.1** (linked: `isMaximalArrivalBound_etaMax`). -/
alias thm_5_1_1 := isMaximalArrivalBound_etaMax
/-- **Theorem 5.1** (linked: `isMinimalArrivalBound_etaMin`). -/
alias thm_5_1_2 := isMinimalArrivalBound_etaMin
/-- **Theorem 5.1** (linked: `etaMax_fixpoint`). -/
alias thm_5_1_3 := etaMax_fixpoint
/-- **Theorem 5.1** (linked: `etaMin_fixpoint`). -/
alias thm_5_1_4 := etaMin_fixpoint
/-- **Theorem 5.1** (linked: `isSubadditive_etaMax`). -/
alias thm_5_1_5 := isSubadditive_etaMax
/-- **Theorem 5.1** (linked: `isSuperadditive_etaMin`). -/
alias thm_5_1_6 := isSuperadditive_etaMin
/-- **Theorem 5.1** (linked: `refineStep_eta_fixpoint`). -/
alias thm_5_1_7 := refineStep_eta_fixpoint

/-- **Definition 5.3** (§5.2.1, p.106): Min-plus minimal service curve β: S offers β if D ≥ A ∗ β for every pair; the largest such server is S_minp(β)={(A,D)∈C×C | A≥D≥A∗β}. -/
noncomputable def def_5_3 := @IsMinimalServiceCurve

/-- **Proposition 5.4** (§5.2.1, p.107): Monotony of min-plus minimal service curve: if β≥β' and S offers β then S offers β' (S_minp(β)⊆S_minp(β')). -/
alias prop_5_4 := IsMinimalServiceCurve.mono

/-- **Definition 5.4** (§5.2.2, p.107): Backlogged period: an interval I where D(t)-A(t)>0 for all t∈I. -/
abbrev def_5_4 := @IsBacklogged

/-- **Definition 5.0** (§5.2.2, p.108): Start of the backlogged period of time t: Start_{A,D}(t)=sup{u≤t | D(u)=A(u)} (eq 5.10). -/
noncomputable def def_start_5_0 := @start

/-! **Proposition 5.5** (§5.2.2, p.108): Backlogged-period properties: any subinterval of a backlogged period is backlogged; (Start(t),t] is backlogged; A(Start(t))=D(Start(t)); and Start is constant on a backlogged period. -/
/-- **Proposition 5.5** (linked: `IsBacklogged.subset`). -/
alias prop_5_5_1 := IsBacklogged.subset
/-- **Proposition 5.5** (linked: `isBacklogged_Ioc_start`). -/
alias prop_5_5_2 := isBacklogged_Ioc_start
/-- **Proposition 5.5** (linked: `apply_start_eq`). -/
alias prop_5_5_3 := apply_start_eq
/-- **Proposition 5.5** (linked: `start_const_of_backlogged`). -/
alias prop_5_5_4 := start_const_of_backlogged

/-- **Definition 5.5** (§5.2.2, p.108): Strict minimal service curve β: D(t)-D(s) ≥ β(t-s) for every backlogged period (s,t] (eq 5.11); largest such server S_strict(β) (eq 5.12). -/
noncomputable def def_5_5 := @IsStrictMinimalServiceCurve

/-! **Proposition 5.6** (§5.2.2, p.109): Properties of strict service curves: if S offers strict β then it offers any strict β'≤β; if it offers β₁ and β₂ it offers β₁∨β₂; and S_strict(β)=S_strict(β↗)=S_strict(β*) (non-decreasing and super-additive closures). -/
/-- **Proposition 5.6** (linked: `IsStrictMinimalServiceCurve.mono`). -/
alias prop_5_6_1 := IsStrictMinimalServiceCurve.mono
/-- **Proposition 5.6** (linked: `IsStrictMinimalServiceCurve.sup`). -/
alias prop_5_6_2 := IsStrictMinimalServiceCurve.sup
/-- **Proposition 5.6** (linked: `isStrictMinimalServiceCurve_closures_iff`). -/
alias prop_5_6_3 := isStrictMinimalServiceCurve_closures_iff

/-- **Proposition 5.7** (§5.2.2, p.110): Any server offering strict service curve β offers min-plus minimal service curve β: S_strict(β)⊆S_minp(β) (eq 5.14). -/
alias prop_5_7 := IsStrictMinimalServiceCurve.isMinimalServiceCurve

/-- **Definition 5.6** (§5.2.4, p.113): Maximal service curve βᴹ: S offers βᴹ if D ≤ A ∗ βᴹ for every pair; largest such server S_maxp(βᴹ) (eq 5.16). -/
noncomputable def def_5_6 := @IsMaximalServiceCurve

/-- **Proposition 5.8** (§5.2.4, p.113): Monotony of maximal service curve: if β≤β' and S offers β then S offers β' (S_maxp(β)⊆S_maxp(β')). -/
alias prop_5_8 := IsMaximalServiceCurve.mono

/-- **Definition 5.7** (§5.2.4, p.113): Shaper σ: a server where the output is σ-upper-constrained, S_sh(σ)={(A,D) | D=A∗σ ... } i.e. the output allows σ as maximal arrival curve (eq 5.18). -/
noncomputable def def_5_7 := @IsShaper

/-- **Proposition 5.9** (§5.2.4, p.113): A σ-shaper offers σ as a maximal service curve. -/
alias prop_5_9 := IsShaper.isMaximalServiceCurve

/-- **Proposition 5.10** (§5.2.4, p.114): A σ-shaper is a maximal-service-curve server: S_sh(σ)⊆S_maxp(σ). -/
alias prop_5_10 := shaperRel_le_maximalServiceRel

/-- **Definition 5.8** (§5.2.4, p.114): Greedy shaper for sub-additive left-continuous σ∈ℱ₀: D=A∗σ, S_grsh(σ)={(A,D)∈C×C | D=A∗σ} (eq 5.19/5.20). -/
noncomputable def def_5_8 := @IsGreedyShaper

/-! **Proposition 5.11** (§5.2.4, p.114): A σ-greedy shaper is a σ-shaper and offers σ as both minimal and maximal min-plus service curve: S_grsh(σ)⊆S_minp(σ)∩S_sh(σ). -/
/-- **Proposition 5.11** (linked: `greedyShaperRel_eq_minimalServiceRel_inf_shaperRel`). -/
alias prop_5_11_1 := greedyShaperRel_eq_minimalServiceRel_inf_shaperRel
/-- **Proposition 5.11** (linked: `greedyShaperRel_le_shaperRel`). -/
alias prop_5_11_2 := greedyShaperRel_le_shaperRel
/-- **Proposition 5.11** (linked: `IsGreedyShaper.isMinimalServiceCurve`). -/
alias prop_5_11_3 := IsGreedyShaper.isMinimalServiceCurve
/-- **Proposition 5.11** (linked: `IsGreedyShaper.isMaximalServiceCurve`). -/
alias prop_5_11_4 := IsGreedyShaper.isMaximalServiceCurve
/-- **Proposition 5.11** (linked: `IsGreedyShaper.isShaper`). -/
alias prop_5_11_5 := IsGreedyShaper.isShaper

/-! **Theorem 5.2** (§5.3.1, p.115): Backlog and delay bounds: with α a maximal arrival curve for A and S offering min-plus minimal service β, d(A,D)≤hDev(α,β) and b(A,D)≤vDev(α,β); if α sub-additive and β left-continuous the bounds are tight (eq 5.21-5.23). -/
/-- **Theorem 5.2** (linked: `delay_le_hDev_of_isMinimalServiceCurve`). -/
alias thm_5_2_1 := Deviation.delay_le_hDev_of_isMinimalServiceCurve
/-- **Theorem 5.2** (linked: `backlog_le_vDev_of_isMinimalServiceCurve`). -/
alias thm_5_2_2 := Deviation.backlog_le_vDev_of_isMinimalServiceCurve
/-- **Theorem 5.2** (linked: `delay_eq_hDev_of_minConv_eq`). -/
alias thm_5_2_3 := Deviation.delay_eq_hDev_of_minConv_eq
/-- **Theorem 5.2** (linked: `backlog_eq_vDev_of_minConv_eq`). -/
alias thm_5_2_4 := Deviation.backlog_eq_vDev_of_minConv_eq
/-- **Theorem 5.2** (linked: `exists_delay_eq_hDev_backlog_eq_vDev`). -/
alias thm_5_2_5 := Deviation.exists_delay_eq_hDev_backlog_eq_vDev

/-! **Proposition 5.12** (§5.3.1, p.115): Monotony of deviations: for f≤f', g≥g', vDev(f,g)≥vDev(f',g') and hDev(f,g)≥hDev(f',g'). -/
/-- **Proposition 5.12** (linked: `vDev_mono`). -/
alias prop_5_12_1 := vDev_mono
/-- **Proposition 5.12** (linked: `hDev_mono`). -/
alias prop_5_12_2 := hDev_mono
/-- **Proposition 5.12** (linked: `vDevAt_mono`). -/
alias prop_5_12_3 := vDevAt_mono
/-- **Proposition 5.12** (linked: `hDevAt_mono`). -/
alias prop_5_12_4 := hDevAt_mono

/-- **Lemma 5.1** (§5.3.1, p.116): Sup-based definition of horizontal deviation: hDev(f,g)=sup_t inf{d∈ℝ⁺ | f(t)≤g(t+d)} (eq 5.24) — the sup-of-inf form that is the library's definition of hDev. -/
noncomputable def lemma_5_1 := @DeepWiki.hDevAt

/-! **Corollary 5.2** (§5.3.2, p.118): Tighter constraints give better bounds: if α'≤α and β'≥β then hDev(α',β')≤hDev(α,β) and vDev(α',β')≤vDev(α,β). -/
/-- **Corollary 5.2** (linked: `hDev_mono`). -/
alias cor_5_2_1 := hDev_mono
/-- **Corollary 5.2** (linked: `vDev_mono`). -/
alias cor_5_2_2 := vDev_mono

/-! **Theorem 5.3** (§5.3.2, p.118): Output arrival curves: with min/max service βᵐ,βᴹ, shaper σ, and αᵘ,αˡ arrival curves for A, D has maximal arrival curve ηᵘ=((αᵘ∗βᴹ)⊘βᵐ)∧σ (eq 5.26) and minimal ηˡ=αˡ∗(βᵐ⊘̄βᴹ) (eq 5.27). -/
/-- **Theorem 5.3** (linked: `isMaximalArrivalBound_output`). -/
alias thm_5_3_1 := isMaximalArrivalBound_output
/-- **Theorem 5.3** (linked: `isMinimalArrivalBound_output`). -/
alias thm_5_3_2 := isMinimalArrivalBound_output
/-- **Theorem 5.3** (linked: `isMaximalArrivalCurve_output`). -/
alias thm_5_3_3 := isMaximalArrivalCurve_output
/-- **Theorem 5.3** (linked: `isMinimalArrivalCurve_output`). -/
alias thm_5_3_4 := isMinimalArrivalCurve_output

/-- **Corollary 5.3** (§5.3.2, p.119): With βᴹ=δ₀ (a maximal service curve of every server) a maximal arrival curve A⊘A and a max service βᵐ give D the maximal arrival curve αᵘ⊘βᵐ. -/
alias cor_5_3 := isMaximalArrivalCurve_output_of_isMinimalServiceCurve

/-! **Corollary 5.4** (§5.3.2, p.119): Output arrival curves for a σ-greedy shaper (σ sub-additive): D has maximal arrival curve αᵘ∗σ and minimal arrival curve αˡ∗(σ⊘̄σ). -/
/-- **Corollary 5.4** (linked: `isMaximalArrivalBound_output_of_isGreedyShaper`). -/
alias cor_5_4_1 := isMaximalArrivalBound_output_of_isGreedyShaper
/-- **Corollary 5.4** (linked: `isMinimalArrivalBound_output_of_isGreedyShaper`). -/
alias cor_5_4_2 := isMinimalArrivalBound_output_of_isGreedyShaper
/-- **Corollary 5.4** (linked: `isMaximalArrivalCurve_output_of_isGreedyShaper`). -/
alias cor_5_4_3 := isMaximalArrivalCurve_output_of_isGreedyShaper
/-- **Corollary 5.4** (linked: `isMinimalArrivalCurve_output_of_isGreedyShaper`). -/
alias cor_5_4_4 := isMinimalArrivalCurve_output_of_isGreedyShaper

/-- **Theorem 5.4** (§5.3.2, p.119): Output arrival curve from the backlog bound: with min service β and sub-additive maximal arrival curve α, D has maximal arrival curve α+vDev(α,β) (improved to α+vDev(α,β)-α(0+) when α-α(0+) is sub-additive). -/
alias thm_5_4 := DeepWiki.isMaximalArrivalBound_output_add_vDev

/-! **Proposition 5.13** (§5.3.3.1, p.120): Restricting the deviation domain to a finite interval: with maximal arrival curve α and strict service β, b(A,D)≤sup over [0,ℓmax] vDev(α,β,t) and d(A,D)≤sup over [0,ℓmax] hDev(α,β,t), ℓmax=inf{t>0|α(t)≤β(t)} (book prints inf, proof gives sup). -/
/-- **Proposition 5.13** (linked: `backlog_le_biSup_vDevAt_sInf_of_isMinimalServiceCurve`). -/
alias prop_5_13_1 := Deviation.backlog_le_biSup_vDevAt_sInf_of_isMinimalServiceCurve
/-- **Proposition 5.13** (linked: `delay_le_biSup_hDevAt_sInf_of_isMinimalServiceCurve`). -/
alias prop_5_13_2 := Deviation.delay_le_biSup_hDevAt_sInf_of_isMinimalServiceCurve

/-! **Theorem 5.5** (§5.3.3.1, p.122): Maximal length of a backlogged period: with A maximal arrival curve α and S strict service β, every backlogged period has length ℓmax=inf{d>0|α(d)≤β(d)} (eq 5.28). -/
/-- **Theorem 5.5** (linked: `length_le_firstCrossing_of_isBacklogged`). -/
alias thm_5_5_1 := length_le_firstCrossing_of_isBacklogged
/-- **Theorem 5.5** (linked: `maxBackloggedLength_le_firstCrossing`). -/
alias thm_5_5_2 := maxBackloggedLength_le_firstCrossing

/-- **Lemma 5.2** (§5.3.3.2, p.122): Horizontal deviation from pseudo-inverse: for f,g∈ℱ↑, if f(t)>g(t) then hDev(f,g,t)=g⁻¹(f(t))-t (eq 5.29). -/
alias lemma_5_2 := hDevAt_eq_pseudoInv_sub_of_lt

/-! **Proposition 5.14** (§5.3.3.2, p.123): Deviations are deconvolutions: vDev(f,g)=(f⊘g)(0) (eq 5.30) and hDev(f,g)=((g⁻¹∘f)⊘λ₁)(0) (eq 5.31). -/
/-- **Proposition 5.14** (linked: `vDev_eq_deconv_zero`). -/
alias prop_5_14_1 := vDev_eq_deconv_zero
/-- **Proposition 5.14** (linked: `hDev_eq_deconv_pseudoInv_zero`). -/
alias prop_5_14_2 := hDev_eq_deconv_pseudoInv_zero

/-! **Theorem 5.6** (§5.3.3.3, p.123): Performance operators are continuity insensitive: for monotone left- /right-continuous f,g, hDev(fℓ,gℓ)=hDev(fᵣ,gᵣ) and vDev(fℓ,gℓ)=vDev(fᵣ,gᵣ). -/
/-- **Theorem 5.6** (linked: `hDev_leftLim_eq_hDev_rightLim`). -/
alias thm_5_6_1 := hDev_leftLim_eq_hDev_rightLim
/-- **Theorem 5.6** (linked: `vDev_leftLim_eq_vDev_rightLim`). -/
alias thm_5_6_2 := vDev_leftLim_eq_vDev_rightLim

/-- **Lemma 5.3** (§5.3.3.3, p.124): Variation of horizontal deviation: for f,g∈ℱ↑ and s>0, hDev(f,g,t+s) ≥ hDev(f,g,t)-s. -/
alias lemma_5_3 := hDevAt_le_add_hDevAt

/-! **Lemma 5.4** (§5.3.3.3, p.124): Horizontal deviation insensitive to left/right closure of g: hDev(f,g,t)=hDev(f,gℓ,t)=hDev(f,gᵣ,t) (eq 5.32). -/
/-- **Lemma 5.4** (linked: `hDevAt_leftLim_eq_hDevAt`). -/
alias lemma_5_4_1 := hDevAt_leftLim_eq_hDevAt
/-- **Lemma 5.4** (linked: `hDevAt_rightLim_eq_hDevAt`). -/
alias lemma_5_4_2 := hDevAt_rightLim_eq_hDevAt

/-- **Lemma 5.5** (§5.3.3.3, p.124): For non-decreasing f, the left-closure of f does not increase the horizontal deviation: hDev(fℓ,g,t) ≤ hDev(f,g,t). -/
alias lemma_5_5 := hDevAt_leftLim_le_hDevAt_rightLim

end DeepWiki.Dnc
