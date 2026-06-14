import Book.ArrivalCurves
import Book.ArrivalCurvesMaximal
import Book.ArrivalCurvesMinimal
import Book.ArrivalCurvesCombined
import Book.ArrivalCurvesShaper
import Book.ArrivalCurvesShaperGreedy
import Book.ArrivalCurvesOutput
import Book.ServiceCurveMinimal
import Book.ServiceCurveStrict
import Book.ServiceCurveStrictMinimal
import Book.ServiceCurveMaximal
import Book.ServersBacklog
import Book.Deviations
import Book.DeviationsBounds
import Book.DeviationsBoundsServer
import Book.DeviationsBoundsTight
import Book.DeviationsRestricted
import Book.DeviationsPseudoInverse
import Book.DeviationsContinuity
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 5: Network Calculus Basics: a Server Crossed by a Single Flow
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-! **Definition 5.0** (§5.1, p.100): Vertical/horizontal deviation and backlog/delay of two cumulative functions: vDev(f,g,t)=f(t)-g(t), hDev(f,g,t)=inf{d|f(t)≤g(t+d)}, b(A,D)=vDev(A,D), d(A,D)=hDev(A,D). Library: vDev, hDev, backlog, delay. -/

/-- **Definition 5.1** (§5.1, p.100): Maximal (upper) arrival curve α∈ℱ↑ for cumulative function A: A ≤ A ∗ α. -/
noncomputable def def_5_1 := @IsMaximalArrivalCurve

/-- **Definition 5.2** (§5.1, p.101): Minimal (lower) arrival curve α'∈ℱ↑ for A: A ⊼ α' ≤ A (max-plus convolution). -/
noncomputable def def_5_2 := @IsMinimalArrivalCurve

/-- **Proposition 5.1** (§5.1, p.102): Equivalent definition of an arrival curve: A ≤ A ∗ α iff A(t+d)-A(t) ≤ α(d) for all t,d (and the dual increment form for the minimal curve). -/
alias prop_5_1 := isMaximalArrivalBound_iff_increment

/-! **Proposition 5.2** (§5.1, p.102): Properties of maximal arrival curves: α* and its sub-additive closure are maximal arrival curves, any α'≥α maximal is maximal, A⊘A is a (least) maximal arrival curve, and the left-continuous extension is one too. Library: IsMaximalArrivalBound.subadditiveClosureENN, IsMaximalArrivalBound.mono, isMaximalArrivalBound_minDeconv_self, isMaximalArrivalBound_leftLim_of_isLeftContinuous. -/

/-! **Corollary 5.1** (§5.1, p.103): If A admits a maximal (resp. minimal) arrival curve it admits a non-decreasing left- (resp. right-) continuous one: the left/right-limit extension is again an arrival curve. Library: isMaximalArrivalBound_leftLim_of_isLeftContinuous, isMinimalArrivalBound_rightLim_of_isRightContinuous. -/

/-! **Proposition 5.3** (§5.1, p.104): Properties of minimal arrival curves (dual of Prop 5.2): α'* and the super-additive closure are minimal arrival curves, any α''≤α' is minimal, A⊘̄A is a (greatest) minimal arrival curve, and the right-continuous extension is one too. Library: IsMinimalArrivalBound.superadditiveClosureMax, IsMinimalArrivalBound.mono, isMinimalArrivalBound_maxDeconv_self, isMinimalArrivalBound_rightLim_of_isRightContinuous. -/

/-! **Theorem 5.1** (§5.1, p.105): Combining a minimal αˡ and maximal αᵘ arrival curve: ηᵘ=αᵘ⊘̄αˡ refines the maximal and ηˡ=αˡ⊘αᵘ the minimal curve; under sub- /super-additivity with vanishing at 0 the refinement fixes in one step and the sub- /super-additive closures are again arrival curves. Library: isMaximalArrivalBound_etaMax, isMinimalArrivalBound_etaMin, etaMax_fixpoint, etaMin_fixpoint, isSubadditive_etaMax, isSuperadditive_etaMin. -/

/-- **Definition 5.3** (§5.2.1, p.106): Min-plus minimal service curve β: S offers β if D ≥ A ∗ β for every pair; the largest such server is S_minp(β)={(A,D)∈C×C | A≥D≥A∗β}. -/
noncomputable def def_5_3 := @IsMinimalServiceCurve

/-- **Proposition 5.4** (§5.2.1, p.107): Monotony of min-plus minimal service curve: if β≥β' and S offers β then S offers β' (S_minp(β)⊆S_minp(β')). -/
alias prop_5_4 := IsMinimalServiceCurve.mono

/-- **Definition 5.4** (§5.2.2, p.107): Backlogged period: an interval I where D(t)-A(t)>0 for all t∈I. -/
abbrev def_5_4 := @IsBacklogged

/-- **Definition 5.0** (§5.2.2, p.108): Start of the backlogged period of time t: Start_{A,D}(t)=sup{u≤t | D(u)=A(u)} (eq 5.10). -/
noncomputable def def_start_5_0 := @start

/-! **Proposition 5.5** (§5.2.2, p.108): Backlogged-period properties: any subinterval of a backlogged period is backlogged; (Start(t),t] is backlogged; A(Start(t))=D(Start(t)); and Start is constant on a backlogged period. Library: IsBacklogged.subset, isBacklogged_Ioc_start, apply_start_eq, start_const_of_backlogged. -/

/-- **Definition 5.5** (§5.2.2, p.108): Strict minimal service curve β: D(t)-D(s) ≥ β(t-s) for every backlogged period (s,t] (eq 5.11); largest such server S_strict(β) (eq 5.12). -/
noncomputable def def_5_5 := @IsStrictMinimalServiceCurve

/-! **Proposition 5.6** (§5.2.2, p.109): Properties of strict service curves: if S offers strict β then it offers any strict β'≤β; if it offers β₁ and β₂ it offers β₁∨β₂; and S_strict(β)=S_strict(β↗)=S_strict(β*) (non-decreasing and super-additive closures). Library: IsStrictMinimalServiceCurve.mono, IsStrictMinimalServiceCurve.sup, isStrictMinimalServiceCurve_closures_iff. -/

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

/-! **Proposition 5.11** (§5.2.4, p.114): A σ-greedy shaper is a σ-shaper and offers σ as both minimal and maximal min-plus service curve: S_grsh(σ)⊆S_minp(σ)∩S_sh(σ). Library: IsGreedyShaper.isMinimalServiceCurve, IsGreedyShaper.isMaximalServiceCurve, IsGreedyShaper.isShaper. -/

/-! **Theorem 5.2** (§5.3.1, p.115): Backlog and delay bounds: with α a maximal arrival curve for A and S offering min-plus minimal service β, d(A,D)≤hDev(α,β) and b(A,D)≤vDev(α,β); if α sub-additive and β left-continuous the bounds are tight (eq 5.21-5.23). Library: delay_le_hDev_of_isMinimalServiceCurve, backlog_le_vDev_of_isMinimalServiceCurve, exists_minimalServiceRel_delay_eq_hDev_backlog_eq_vDev. -/

/-! **Proposition 5.12** (§5.3.1, p.115): Monotony of deviations: for f≤f', g≥g', vDev(f,g)≥vDev(f',g') and hDev(f,g)≥hDev(f',g'). Library: vDev_mono, hDev_mono. -/

/-! **Lemma 5.1** (§5.3.1, p.116): Sup-based definition of horizontal deviation: hDev(f,g)=sup_t inf{d∈ℝ⁺ | f(t)≤g(t+d)} (eq 5.24) — the sup-of-inf form that is the library's definition of hDev. Library: hDev, hDevAt, hDevAt_le_hDev, hDev_le. -/

/-! **Corollary 5.2** (§5.3.2, p.118): Tighter constraints give better bounds: if α'≤α and β'≥β then hDev(α',β')≤hDev(α,β) and vDev(α',β')≤vDev(α,β). Library: hDev_mono, vDev_mono. -/

/-! **Theorem 5.3** (§5.3.2, p.118): Output arrival curves: with min/max service βᵐ,βᴹ, shaper σ, and αᵘ,αˡ arrival curves for A, D has maximal arrival curve ηᵘ=((αᵘ∗βᴹ)⊘βᵐ)∧σ (eq 5.26) and minimal ηˡ=αˡ∗(βᵐ⊘̄βᴹ) (eq 5.27). Library: isMaximalArrivalCurve_output, isMinimalArrivalBound_output. -/

/-- **Corollary 5.3** (§5.3.2, p.119): With βᴹ=δ₀ (a maximal service curve of every server) a maximal arrival curve A⊘A and a max service βᵐ give D the maximal arrival curve αᵘ⊘βᵐ. -/
alias cor_5_3 := isMaximalArrivalCurve_output_of_isMinimalServiceCurve

/-! **Corollary 5.4** (§5.3.2, p.119): Output arrival curves for a σ-greedy shaper (σ sub-additive): D has maximal arrival curve αᵘ∗σ and minimal arrival curve αˡ∗(σ⊘̄σ). Library: isMaximalArrivalCurve_output_of_isGreedyShaper, isMinimalArrivalCurve_output_of_isGreedyShaper. -/

/-! **Theorem 5.4** (§5.3.2, p.119): Output arrival curve from the backlog bound: with min service β and sub-additive maximal arrival curve α, D has maximal arrival curve α+vDev(α,β) (improved to α+vDev(α,β)-α(0+) when α-α(0+) is sub-additive). Library: isMaximalArrivalBound_output_add_vDev, isMaximalArrivalBound_output_add_vDev_tsub. -/

/-! **Proposition 5.13** (§5.3.3.1, p.120): Restricting the deviation domain to a finite interval: with maximal arrival curve α and strict service β, b(A,D)≤sup over [0,ℓmax] vDev(α,β,t) and d(A,D)≤sup over [0,ℓmax] hDev(α,β,t), ℓmax=inf{t>0|α(t)≤β(t)} (book prints inf, proof gives sup). Library: backlog_le_biSup_vDevAt_sInf_of_isMinimalServiceCurve, delay_le_biSup_hDevAt_sInf_of_isMinimalServiceCurve. -/

/-! **Theorem 5.5** (§5.3.3.1, p.122): Maximal length of a backlogged period: with A maximal arrival curve α and S strict service β, every backlogged period has length ℓmax=inf{d>0|α(d)≤β(d)} (eq 5.28). Library: maxBackloggedLength_le_firstCrossing, length_le_firstCrossing_of_isBacklogged. -/

/-- **Lemma 5.2** (§5.3.3.2, p.122): Horizontal deviation from pseudo-inverse: for f,g∈ℱ↑, if f(t)>g(t) then hDev(f,g,t)=g⁻¹(f(t))-t (eq 5.29). -/
alias lemma_5_2 := hDevAt_eq_pseudoInv_sub_of_lt

/-! **Proposition 5.14** (§5.3.3.2, p.123): Deviations are deconvolutions: vDev(f,g)=(f⊘g)(0) (eq 5.30) and hDev(f,g)=((g⁻¹∘f)⊘λ₁)(0) (eq 5.31). Library: vDev_eq_deconv_zero, hDev_eq_deconv_pseudoInv_zero. -/

/-! **Theorem 5.6** (§5.3.3.3, p.123): Performance operators are continuity insensitive: for monotone left- /right-continuous f,g, hDev(fℓ,gℓ)=hDev(fᵣ,gᵣ) and vDev(fℓ,gℓ)=vDev(fᵣ,gᵣ). Library: hDev_leftLim_eq_hDev_rightLim, vDev_leftLim_eq_vDev_rightLim. -/

/-- **Lemma 5.3** (§5.3.3.3, p.124): Variation of horizontal deviation: for f,g∈ℱ↑ and s>0, hDev(f,g,t+s) ≥ hDev(f,g,t)-s. -/
alias lemma_5_3 := hDevAt_le_add_hDevAt

/-! **Lemma 5.4** (§5.3.3.3, p.124): Horizontal deviation insensitive to left/right closure of g: hDev(f,g,t)=hDev(f,gℓ,t)=hDev(f,gᵣ,t) (eq 5.32). Library: hDevAt_leftLim_eq_hDevAt, hDevAt_rightLim_eq_hDevAt. -/

/-- **Lemma 5.5** (§5.3.3.3, p.124): For non-decreasing f, the left-closure of f does not increase the horizontal deviation: hDev(fℓ,g,t) ≤ hDev(f,g,t). -/
alias lemma_5_5 := hDevAt_leftLim_le_hDevAt_rightLim

end DeepWiki.Dnc
