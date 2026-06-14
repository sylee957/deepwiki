import Book.RealCurves
import Book.RealCurvesConv
import Book.RealCurvesDeconv
import Book.RealCurvesAdditivity
import Book.RealCurvesDeviations
import Book.PseudoInverse
import Book.PseudoInverseCatalog
import Book.ClosuresNd
import Book.ConvolutionMinimum
import Book.ConvolutionContinuity
import Book.Concave
import Book.ConcaveProps
import Book.ConcaveDioid
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 3: Sub-classes of Functions
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-! **Definition 3.1** (§3.1, p.38): Classes of usual functions: pure delay δ_d (0 for t≤d, +∞ after), guaranteed rate λ_R: t↦Rt, rate-latency β_{R,T}: t↦R[t−T]⁺, token-bucket γ_{r,b}: t↦(rt+b)∧δ_0(t), staircase ν_{P,h,J}, and test function 1_{>T}. Library: delay, rate, rateLatency, rateLatencyNN, tokenBucket, tokenBucketNN, staircase, unitStep. -/

/-! **Proposition 3.1** (§3.1, p.39): Sub/super-additivity of the usual functions: δ_d sub-additive, λ_R sub- and super-additive, β_{R,T} super-additive, γ_{r,b} sub-additive, ν_{P,h,J} sub-additive (super-additive for J<−P), each its own sub- /super-additive closure; the test function 1_{>T} is neither. Library: rateNN_subadditive, rateNN_superadditive, delayNN_superadditive, rateLatencyNN_superadditive, tokenBucketNN_subadditive, staircase_subadditive, staircase_superadditive, unitStep_zero_subadditive, not_isSubadditive_delayNN, tokenBucketNN_closure, staircase_closure, delayNN_closure, rateNN_closure, rateLatencyNN_closure, staircase_closure_super. -/

/-! **Proposition 3.2** (§3.1, p.40): Convolution and deconvolution by pure delays are time-shifts: f∗δ_d = t↦f([t−d]⁺) and f⊘δ_d = t↦f(t+d) for non-decreasing f. Library: conv_delayNN, conv_delayNN_posPart, minDeconv_delayNN. -/

/-! **Proposition 3.3** (§3.1, p.40): For sub-additive f, (f⊘δ_d)* = δ_0∗(f⊘δ_d). Library: minDeconv_delayNN_subadd, minDeconv_delayNN_closure. -/

/-! **Proposition 3.4** (§3.1.1, p.41): Catalog of convolutions: δ_d∗δ_{d'}=δ_{d+d'}; β_{R,T}=δ_T∗λ_R; λ_R∗λ_{R'}=λ_{R∧R'}; β_{R,T}∗β_{R',T'}=β_{(R∧R'),(T+T')}; γ_{r,b}∗γ_{r',b'}=γ_{r,b}∧γ_{r',b'}. Library: conv_delayNN_delayNN, rateLatencyNN_eq_conv, conv_rateNN_rateNN, conv_rateLatencyNN_rateLatencyNN, conv_tokenBucketNN_tokenBucketNN. -/

/-! **Proposition 3.5** (§3.1.1, p.41): Catalog of deconvolutions: δ_d⊘δ_{d'}=δ_{d−d'} (d≥d'); λ_R⊘δ_d=γ̂_{R,Rd}; γ_{r,b}⊘δ_d=γ̂_{r,b+rd}; λ_R⊘λ_{R'}=λ_R (R≤R') else ∞; γ_{r,b}⊘λ_R=γ̂_{r,b} (R≥r) else ∞; γ_{r,b}⊘β_{R,T}=γ̂_{r,b+rT} (R≥r) else ∞. Library: minDeconv_delayNN_delayNN, minDeconv_rateNN_delayNN, minDeconv_tokenBucketNN_delay, minDeconv_rateNN_rateNN, minDeconv_rateNN_rateNN_top, minDeconv_tokenBucketNN_rateNN, minDeconv_tokenBucketNN_rateNN_top, minDeconv_tokenBucketNN_rateLatencyNN, minDeconv_tokenBucketNN_rateLatencyNN_top. -/

/-! **Proposition 3.6** (§3.1.2, p.42): Horizontal deviation and pure delay: hDev(f,δ_d) ≤ d, with equality hDev(f,δ_d)=d when f(0⁺)>0. Library: hDevENN_delay_le, hDevENN_delay_eq_of_rightLimit_pos. -/

/-! **Proposition 3.7** (§3.1.2, p.43): Catalog of deviations: hDev(γ_{r,b},δ_d)=d; hDev(γ_{r,b},β_{R,T})=T+b/R (r≤R) else ∞; vDev(γ_{r,b},δ_d)=rd+b; vDev(γ_{r,b},β_{R,T})=rT+b (r≤R) else ∞. Library: hDevENN_tokenBucketNN_delay, hDevENN_tokenBucketNN_rateLatencyNN, hDevENN_tokenBucketNN_rateLatencyNN_top, vDev_tokenBucketNN_delay, vDev_tokenBucketNN_rateLatencyNN, vDev_tokenBucketNN_rateLatencyNN_top. -/

/-- **Definition 3.2** (§3.2, p.45): Non-negative closure [f]⁺(t)=f(t)∨0 and non-decreasing closure f↑(t)=⨆_{s≤t}f(s) (and their composite [f]⁺↑), the closure operators keeping curves in ℱ↑. -/
noncomputable def def_3_2 := @ndClosure

/-- **Lemma 3.1** (§3.2, p.45): For non-decreasing g greater than f, the non-decreasing closure f↑ is below g (least monotone majorant). -/
alias lemma_3_1 := ndClosure_le

/-- **Definition 3.3** (§3.2.1, p.46): Pseudo-inverse of a non-negative non-decreasing f: f⁻¹(x)=inf{t | f(t)≥x}. -/
noncomputable def def_3_3 := @pseudoInv

/-- **Lemma 3.2** (§3.2.1, p.46): Alternative pseudo-inverse formula for non-decreasing f: f⁻¹(x)=sup{t | f(t)<x}. -/
alias lemma_3_2 := pseudoInv_eq_sSup_lt

/-! **Proposition 3.8** (§3.2.1, p.47): Pseudo-inverse properties: f⁻¹∈ℱ₀⁺; the inversion relations t>f⁻¹(x)⇒f(t)≥x, f(t)≥x⇒t≥f⁻¹(x), t<f⁻¹(x)⇒f(t)<x, f(t)<x⇒t≤f⁻¹(x); and f⁻¹ is left-continuous. Library: pseudoInv_bot, pseudoInv_mono, le_apply_of_pseudoInv_lt, pseudoInv_le_of_le_apply, apply_lt_of_lt_pseudoInv, le_pseudoInv_of_apply_lt, continuousWithinAt_Iio_pseudoInv. -/

/-! **Proposition 3.9** (§3.2.1, p.48): Catalog of pseudo-inverses: (γ_{r,b})⁻¹=δ_{b/r} (r>0) else δ_b; (δ_d)⁻¹=γ_{0,d}; (λ_R)⁻¹=λ_{1/R}; (β_{R,T})⁻¹=γ_{1/R,T} (R>0). Library: pseudoInv_tokenBucketENN, pseudoInv_delayENN_eq_tokenBucketENN, pseudoInv_rateENN, pseudoInv_rateLatencyENN. -/

/-- **Proposition 3.10** (§3.2.2, p.48): The convolution infimum is attained as a minimum: for non-decreasing left-continuous f,g there is u₀∈[0,t] with (f∗g)(t)=f(u₀)+g(t−u₀). -/
alias prop_3_10 := exists_minConv_eq_split_of_curves

/-- **Proposition 3.11** (§3.2.2, p.49): Continuity of the convolution: if f,g are non-decreasing and left-continuous, then f∗g is left-continuous. -/
alias prop_3_11 := isLeftContinuous_minConv_ennreal

/-- **Definition 3.4** (§3.3.1, p.50): Concave function: f∈ℱ is concave iff ∀s,t,∀p∈[0,1], p·f(s)+(1−p)·f(t) ≤ f(ps+(1−p)t). -/
abbrev def_3_4 := @IsConcaveEReal

/-! **Proposition 3.12** (§3.3.1, p.50): Properties of concave functions f,g: f+g concave; f∧g concave; if f(0)≥0 then f sub-additive; f∗g=(f−f(0)∧g−g(0))+(f(0)+g(0)) (so f∗g=f∧g when f(0)=g(0)=0); if f(0)≥0 then f*=e∧f. Library: IsConcaveEReal.add, IsConcaveEReal.inf, IsConcaveEReal.isSubadditive, minConv_eq_inf_sub_add, minConv_eq_inf_of_null, subadditiveClosureEReal_eq_self_of_isConcaveEReal. -/

/-! **Definition 3.5** (§3.3.2, p.51): Convex function: f∈ℱ is convex iff ∀s,t,∀p∈[0,1], p·f(s)+(1−p)·f(t) ≥ f(ps+(1−p)t). Not formalized in the library. -/

/-! **Proposition 3.13** (§3.3.2, p.51): Properties of convex functions f,g: f+g convex; f∨g convex; f∗g convex. Not formalized in the library. -/

/-! **Definition 3.6** (§3.3.2, p.53): Legendre–Fenchel transform on R̄min^{R⁺}: 𝓛(f)(t)=sup_{u≥0}{t·u−f(u)}. Not formalized in the library. -/

/-! **Proposition 3.14** (§3.3.2, p.53): Examples of Legendre–Fenchel transforms: 𝓛(λ_R)=δ_R; 𝓛(δ_d)=λ_d; 𝓛(β_{R,T})=λ_T∨δ_R. Not formalized in the library. -/

/-! **Proposition 3.15** (§3.3.2, p.54): Properties of the Legendre–Fenchel transform: 𝓛(f) convex non-decreasing; 𝓛(f∧g)=𝓛(f)∨𝓛(g); 𝓛(f∗g)=𝓛(f)+𝓛(g); if f convex non-decreasing then 𝓛(𝓛(f))=f (involution). Not formalized in the library. -/

end DeepWiki.Dnc
