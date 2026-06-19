import DeepWiki.NetworkCalculus.ServersResidual
import DeepWiki.NetworkCalculus.ServersResidualWeaklyStrict
import DeepWiki.NetworkCalculus.ServiceCurveAdaptive
import DeepWiki.NetworkCalculus.ServiceCurveFamilies
import DeepWiki.NetworkCalculus.ServiceCurveFamiliesMinimal
import DeepWiki.NetworkCalculus.ServiceCurveMinimal
import DeepWiki.NetworkCalculus.ServiceCurveMonotony
import DeepWiki.NetworkCalculus.ServiceCurveStrict
import DeepWiki.NetworkCalculus.ServiceCurveStrictTandemDilution
import DeepWiki.NetworkCalculus.ServiceCurveVariableCapacity
import DeepWiki.NetworkCalculus.ServiceCurveVariableCapacityFamilies
import DeepWiki.NetworkCalculus.ServiceCurveVariableCapacityFamiliesStrict
import DeepWiki.NetworkCalculus.ServiceCurveVariableCapacityStrict
import DeepWiki.NetworkCalculus.ServiceCurveVariableCapacityMonotonyExt
import DeepWiki.NetworkCalculus.ServiceCurveVariableCapacityStart
import DeepWiki.NetworkCalculus.ServiceCurveWeaklyStrict
import DeepWiki.NetworkCalculus.ServiceCurveWeaklyStrictStrictness
import DeepWiki.NetworkCalculus.RealTimeCalculus
import DeepWiki.NetworkCalculus.ServiceCurveSufficientlyStrict
import Sources.Doi_10_1002_9781119440284.Source

/-! # DNC catalog — Chapter 9: A Hierarchy of Service Curves
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-- **Definition 9** (§9.1, p.210): S_mp(β) = {(A,D) | A ≥ D, ∀t, D ≥ A ∗ β}: the min-plus (minimal) service-curve trajectory set. -/
noncomputable def def_9_types_mp := @minimalServiceRel

/-- **Definition 9** (§9.1, p.210): S_wstrict(β) = {(A,D) | A ≥ D, ∀t, D(t) ≥ D(Start(t)) + β(t−Start(t))}: weakly strict service curve. -/
noncomputable def def_9_types_wstrict := @weaklyStrictServiceRel

/-- **Definition 9** (§9.1, p.210): S_strict(β) = {(A,D) | A ≥ D, ∀ backlogged (s,t], D(t) ≥ D(s) + β(t−s)}: strict service curve. -/
noncomputable def def_9_types_strict := @strictServiceRel

/-- **Definition 9** (§9.1, p.210): S_vcn(β) = {(A,D) | ∃C, ∀t D(t)=inf_{s≤t}(A(s)+C(t)−C(s)), β(t−s)≤C(t)−C(s)}: variable capacity node. -/
noncomputable def def_9_types_vcn := @variableCapacityRel

/-- **Definition 9** (§9.1, p.210): S_asc(β,β̃) = {(A,D) | A ≥ D, ∀ s≤t either D(t)≥D(s)+β̃(t−s) or ∃u∈[s,t] D(t)≥A(u)+β(t−u)}: adaptive service curve. -/
noncomputable def def_9_types_asc := @adaptiveServiceRel

/-! **Definition 9** (§9.1, p.210): Real-time-calculus greedy processor: a service-curve type defined via RTC bivariate functions (§9.1.3). The bivariate Chasles framework underlying it is `DeepWiki.IsChasles` / `ofUnivariate` (see def_9_1, lemma_9_2); the greedy-processor service-curve type itself (from equations [9.4]-[9.6]) is not separately formalized. -/

/-- **Definition 9** / §9.3.2, p.227: the sufficiently-strict (s3c) service
curve — `(A,D)` is s3c for `β` with dwell period `dw` when `D ≤ A` and
`A (t − dw t) + β (dw t) ≤ D t`. The library's `IsSufficientlyStrict` (for a
fixed dwell; the book quantifies over a family of dwells). -/
def def_9_types_s3c := @IsSufficientlyStrict

/-- **Proposition 9.1** (§9.1.1, p.211): Blind multiplexing from a weakly strict curve: an n-server with weakly strict β and arrival curves αᵢ offers flow j the minimal min-plus residual βⱼ = [β − ∑_{i≠j} αᵢ]⁺↑. -/
alias prop_9_1 := isMinimalServiceCurve_residualServer_of_wstrict

/-- **Theorem 9.1** (§9.1.1, p.211): Blind multiplexing from a weakly strict curve, weakly strict residual: a two-server with weakly strict β crossed by α₁,α₂ offers flow 1 the weakly strict β₁ = [[β−α₂]⁺↑ ⊘̄ α₁]⁺↑ (formalized for n flows with cross-traffic summed). -/
alias thm_9_1 := isWeaklyStrictMinimalServiceCurve_residualServer_of_wstrict

/-- **Lemma 9.1** (§9.1.2, p.212): Alternative definition of a variable capacity node: with C ∈ C, the output D(t)=inf_{0≤s≤t}(A(s)+C(t)−C(s)) anchors at the start, D(t)=A(Start(t))+C(t)−C(Start(t)) (formalized under jump domination, where the closed form is repaired). -/
alias lemma_9_1 := variableCapacityOutput_start_eq

/-- **Lemma 9.2**, departure coherence (§9.1.3, p.215): in the RTC
greedy-processor equations, if the arrival `A` is Chasles then the departure
`D` (satisfying the backlog relation `D s t = A s t − (b t − b s)`, eq [9.6])
is Chasles too — the library's `isChasles_departure`. (The analogous coherence
of the remaining capacity `C'` is not separately formalized.) -/
alias lemma_9_2 := isChasles_departure

/-- **Theorem 9.2** (§9.1.3, p.216): Equivalence RTC-NC. For Chasles bivariate `A,C,D,C'` with `b 0 = 0` and the residual sets `{C[0,u]−A[0,u] : u≤t}` bounded above, the RTC greedy-processor equations [9.4]-[9.6] (`DeepWiki.IsRtcGreedy`, on `0≤s≤t`) hold iff the univariate readings satisfy the variable-capacity node equations [9.7]-[9.9] (`DeepWiki.IsVarCapacityEqns`). The library's `isRtcGreedy_iff_isVarCapacityEqns`; directions `isVarCapacityEqns_of_isRtcGreedy` (RTC→NC, output [9.7] via `real_sub_ciSup`) / `isRtcGreedy_of_isVarCapacityEqns` (NC→RTC, residual [9.5] via the `[0,t]=[0,s]∪[s,t]` sup-split). Lemma 9.2 coherence = `isChasles_departure`. -/
alias thm_9_2 := isRtcGreedy_iff_isVarCapacityEqns

/-- **Theorem 9.2** (RTC→NC direction): `DeepWiki.isVarCapacityEqns_of_isRtcGreedy`. -/
alias thm_9_2_forward := isVarCapacityEqns_of_isRtcGreedy

/-- **Theorem 9.2** (NC→RTC direction): `DeepWiki.isRtcGreedy_of_isVarCapacityEqns`. -/
alias thm_9_2_reverse := isRtcGreedy_of_isVarCapacityEqns

/-- **Definition 9.1** (§9.1.3, p.217): the RTC↔NC conversion underlying the RTC
arrival/service curves — a univariate cumulative `g` induces the Chasles
bivariate `(s,t) ↦ g t − g s` (`ofUnivariate`, `isChasles_ofUnivariate`), and a
Chasles bivariate reads back as `f s t = f 0 t − f 0 s` (`IsChasles`,
`IsChasles.eq_univariate_sub`). The min/max RTC curves `αⁱᵘ,αᵘ,βᵐ,βᴹ` extracted
from these bounds are not separately formalized. -/
def def_9_1 := @ofUnivariate

/-- **Lemma 9.3** (§9.1.4, p.218): If β ≤ β̃ then S_asc(β,β̃) ⊆ S_mp(β): an adaptive server with β ≤ β̃ is a min-plus server for β. -/
alias lemma_9_3 := adaptiveServiceRel_le_minimalServiceRel

/-- **Lemma 9.4** (§9.1.4, p.218): If β ∈ F₀↑ is piecewise linear convex then ∀A∈C, (A,A∗β) ∈ S_asc(β,β); the convolution output meets the adaptive pair (β,β) (formalized for super-additive continuous β). -/
alias lemma_9_4 := isAdaptiveServiceBound_minConvProj

/-! **Proposition 9.2** (§9.2.1, p.219): Monotony: for any type T ∈ {mp,strict,wstrict,vcn} and β ≤ β' left-continuous, S_T(β) ⊇ S_T(β'). -/
/-- **Proposition 9.2** (linked: `minimalServiceRel_mono`). -/
alias prop_9_2_1 := minimalServiceRel_mono
/-- **Proposition 9.2** (linked: `weaklyStrictServiceRel_mono`). -/
alias prop_9_2_2 := weaklyStrictServiceRel_mono
/-- **Proposition 9.2** (linked: `strictServiceRel_mono`). -/
alias prop_9_2_3 := strictServiceRel_mono
/-- **Proposition 9.2** (linked: `variableCapacityRel_mono`). -/
alias prop_9_2_4 := variableCapacityRel_mono

/-! **Proposition 9.3** (§9.2.1, p.219): Closure invariance: S_strict(β)=S_strict(β*̄), S_wstrict(β)=S_wstrict(β↑), S_vcn(β)=S_vcn(β*̄) — a curve may be replaced by its (sub- /super-additive, non-decreasing) closure. -/
/-- **Proposition 9.3** (linked: `strictServiceRel_superadditiveClosureMax`). -/
alias prop_9_3_1 := strictServiceRel_superadditiveClosureMax
/-- **Proposition 9.3** (linked: `weaklyStrictServiceRel_closure`). -/
alias prop_9_3_2 := weaklyStrictServiceRel_closure
/-- **Proposition 9.3** (linked: `variableCapacityRel_superadditiveClosureMax`). -/
alias prop_9_3_3 := variableCapacityRel_superadditiveClosureMax
/-- **Proposition 9.3** (linked: `variableCapacityRel_closure`). -/
alias prop_9_3_4 := variableCapacityRel_closure

/-! **Theorem 9.3** (§9.2.1, p.220): Monotony refined (8 parts): S_mp(β)⊇S_mp(β') ⇔ β↑≤β'↑ (and likewise wstrict, strict via super-additive closures (β↑)*̄≤(β'↑)*̄, vcn) — relation inclusion is exactly pointwise/closure domination. -/
/-- **Theorem 9.3** (linked: `minimalServiceRel_le_iff`). -/
alias thm_9_3_1 := minimalServiceRel_le_iff
/-- **Theorem 9.3** (linked: `weaklyStrictServiceRel_le_iff`). -/
alias thm_9_3_2 := weaklyStrictServiceRel_le_iff
/-- **Theorem 9.3** (linked: `strictServiceRel_le_iff_of_superadditive`). -/
alias thm_9_3_3 := strictServiceRel_le_iff_of_superadditive
/-- **Theorem 9.3** (linked: `variableCapacityRelExt_le_iff_superadditiveClosureMaxNN_ndClosure_le`). -/
alias thm_9_3_4 := variableCapacityRelExt_le_iff_superadditiveClosureMaxNN_ndClosure_le

/-! **Theorem 9.4** (§9.2.2, p.221): Families of service curves (4 parts): ⋂ᵢS_mp(βᵢ)=⋂ⱼS_mp(β'ⱼ) iff same downward closure; ⋂ᵢS_wstrict(βᵢ)=S_wstrict((supᵢβᵢ)↑); ⋂ᵢS_strict(βᵢ)=S_strict((supᵢβᵢ)*̄); ⋂ᵢS_vcn(βᵢ)=S_vcn((supᵢβᵢ)*̄). -/
/-- **Theorem 9.4** (linked: `minimalServiceRel_iInter_eq_iff_mutually_dominated`). -/
alias thm_9_4_1 := minimalServiceRel_iInter_eq_iff_mutually_dominated
/-- **Theorem 9.4** (linked: `weaklyStrictServiceRel_iSup`). -/
alias thm_9_4_2 := weaklyStrictServiceRel_iSup
/-- **Theorem 9.4** (linked: `strictServiceRel_iSup`). -/
alias thm_9_4_3 := strictServiceRel_iSup
/-- **Theorem 9.4** (linked: `variableCapacityJumpFamilyRel_le_variableCapacityRel_iSup`). -/
alias thm_9_4_4 := variableCapacityJumpFamilyRel_le_variableCapacityRel_iSup

/-! **Theorem 9.5** (§9.2.3, p.222): Hierarchy: for β∈F, S_vcn(β) ⊆ S_strict(β) ⊆ S_wstrict(β) ⊆ S_mp(β); with equalities S_vcn=S_strict iff β⊘β only has finite values, S_strict=S_wstrict iff β↑=δ_T, S_wstrict=S_mp iff β↑=δ₀ or 0. -/
/-- **Theorem 9.5** (linked: `variableCapacityRel_le_minimalServiceRel`). -/
alias thm_9_5_1 := variableCapacityRel_le_minimalServiceRel
/-- **Theorem 9.5** (linked: `variableCapacityJumpRel_le_strictServiceRel`). -/
alias thm_9_5_2 := variableCapacityJumpRel_le_strictServiceRel
/-- **Theorem 9.5** (linked: `strictServiceRel_le_weaklyStrictServiceRel`). -/
alias thm_9_5_3 := strictServiceRel_le_weaklyStrictServiceRel
/-- **Theorem 9.5** (linked: `weaklyStrictServiceRel_le_minimalServiceRel`). -/
alias thm_9_5_4 := weaklyStrictServiceRel_le_minimalServiceRel
/-- **Theorem 9.5** (linked: `not_forall_variableCapacityRel_le_strictServiceRel`). -/
alias thm_9_5_5 := not_forall_variableCapacityRel_le_strictServiceRel
/-- **Theorem 9.5** (linked: `not_forall_weaklyStrictServiceRel_le_strictServiceRel`). -/
alias thm_9_5_6 := not_forall_weaklyStrictServiceRel_le_strictServiceRel
/-- **Theorem 9.5** (linked: `not_forall_minimalServiceRel_le_weaklyStrictServiceRel`). -/
alias thm_9_5_7 := not_forall_minimalServiceRel_le_weaklyStrictServiceRel

/-! **Theorem 9.6** (§9.2.3, p.225): No translation with families: for two different types T,T' among vcn,wstrict,strict,mp and a family (βᵢ) of type T, there is no family (β'ⱼ) of type T' with ⋂ᵢS_T(βᵢ)=⋂ⱼS_T'(β'ⱼ), except in the equality cases of Thm 9.5. -/
/-- **Theorem 9.6** (linked: `not_forall_weaklyStrictServiceRel_le_strictServiceRel`). -/
alias thm_9_6_1 := not_forall_weaklyStrictServiceRel_le_strictServiceRel
/-- **Theorem 9.6** (linked: `not_forall_variableCapacityRel_le_strictServiceRel`). -/
alias thm_9_6_2 := not_forall_variableCapacityRel_le_strictServiceRel
/-- **Theorem 9.6** (linked: `not_forall_variableCapacityRel_le_weaklyStrictServiceRel`). -/
alias thm_9_6_3 := not_forall_variableCapacityRel_le_weaklyStrictServiceRel
/-- **Theorem 9.6** (linked: `not_forall_iInf_variableCapacityRel_le_iSup`). -/
alias thm_9_6_4 := not_forall_iInf_variableCapacityRel_le_iSup

/-- **Lemma 9.5** (§9.3.1, p.226): For T ∈ ℝ₊, the closure of the union of n-fold strict-δ_{T/n} tandems equals the min-plus pure-delay server: S̄(⋃ₙ (S_strict(δ_{T/n}))ⁿ) = S_mp(δ_T). -/
alias lemma_9_5 := systemClosure_delayTandemUnion_eq

/-! **Theorem 9.7** (§9.3.1, p.227): for each convex piecewise-linear β there is a system S of
strict-service servers with `S_strict(β) ⊆ S̄ ⊆ S_mp(β)` — "no good intermediate type of service
curve exists". The book does not prove the general theorem; only its δ_T special case is formalized,
as `lemma_9_5` (`systemClosure_delayTandemUnion_eq`). The general Theorem 9.7 is not formalized. -/

/-- **Theorem 9.8** (§9.3.2, p.228): s3c composition — `S_s3c(β₂,Dw₂) ∘ S_s3c(β₁,Dw₁) ⊆ S_s3c(β₁∗β₂,Dw')` with the composed dwell `Dw'(t) = Dw₂(t) + Dw₁(t − Dw₂(t))`. The library's `DeepWiki.IsSufficientlyStrict.comp` (cumulative-pair form: tandem s3c servers `(A,M)`/`(M,D)` compose to an s3c server `(A,D)` for `β₁ ∗ β₂` at the composed dwell). The s3c relation is `IsSufficientlyStrict` (def_9_types_s3c). The book's dwell-family wrapper `S_s3c(β,Dw)` (Dw a set of possible dwells) and the FIFO-multiplexing `(β−α₂)⁺` residual build on this. -/
alias thm_9_8 := IsSufficientlyStrict.comp

end DeepWiki.Dnc
