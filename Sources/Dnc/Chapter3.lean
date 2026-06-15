import DeepWiki.NetworkCalculus.ClosuresNd
import DeepWiki.NetworkCalculus.Concave
import DeepWiki.NetworkCalculus.ConcaveDioid
import DeepWiki.NetworkCalculus.ConcaveProps
import DeepWiki.NetworkCalculus.Convex
import DeepWiki.NetworkCalculus.LegendreFenchel
import DeepWiki.NetworkCalculus.LegendreFenchelExamples
import DeepWiki.NetworkCalculus.ConvolutionContinuity
import DeepWiki.NetworkCalculus.ConvolutionMinimum
import DeepWiki.NetworkCalculus.PseudoInverse
import DeepWiki.NetworkCalculus.PseudoInverseCatalog
import DeepWiki.NetworkCalculus.RealCurves
import DeepWiki.NetworkCalculus.RealCurvesAdditivity
import DeepWiki.NetworkCalculus.RealCurvesConv
import DeepWiki.NetworkCalculus.RealCurvesDeconv
import DeepWiki.NetworkCalculus.RealCurvesDeviations
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 3: Sub-classes of Functions
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-! ## §3.1 The usual functions, their catalog of operations and deviations -/

/-- **Definition 3.1** (§3.1, p.38), pure delay `δ_d`. -/
noncomputable def def_3_1_delay := @delay
/-- **Definition 3.1**, guaranteed rate `λ_R`. -/
noncomputable def def_3_1_rate := @rate
/-- **Definition 3.1**, rate-latency `β_{R,T}`. -/
noncomputable def def_3_1_rateLatency := @rateLatency
/-- **Definition 3.1**, token-bucket `γ_{r,b}`. -/
noncomputable def def_3_1_tokenBucket := @tokenBucket
/-- **Definition 3.1**, staircase `ν_{P,h,J}`. -/
noncomputable def def_3_1_staircase := @staircase
/-- **Definition 3.1**, cumulative staircase. -/
noncomputable def def_3_1_staircaseFun := @staircaseFun
/-- **Definition 3.1**, test function `1_{>T}`. -/
noncomputable def def_3_1_unitStep := @unitStep
/-- **Definition 3.1**, window function. -/
noncomputable def def_3_1_window := @window

/-- **Proposition 3.1** (§3.1, p.39), `δ_d` super-additive. -/
alias prop_3_1_delay_super := delayNN_superadditive
/-- **Proposition 3.1**, `δ_d` not sub-additive (faithful min-plus reading). -/
alias prop_3_1_delay_not_sub := not_isSubadditive_delayNN
/-- **Proposition 3.1**, `λ_R` sub-additive. -/
alias prop_3_1_rate_sub := rateNN_subadditive
/-- **Proposition 3.1**, `λ_R` super-additive. -/
alias prop_3_1_rate_super := rateNN_superadditive
/-- **Proposition 3.1**, `β_{R,T}` super-additive. -/
alias prop_3_1_rateLatency_super := rateLatencyNN_superadditive
/-- **Proposition 3.1**, `γ_{r,b}` sub-additive. -/
alias prop_3_1_tokenBucket_sub := tokenBucketNN_subadditive
/-- **Proposition 3.1**, `ν_{P,h,J}` sub-additive. -/
alias prop_3_1_staircase_sub := staircase_subadditive
/-- **Proposition 3.1**, `ν_{P,h,J}` super-additive (for `J < −P`). -/
alias prop_3_1_staircase_super := staircase_superadditive
/-- **Proposition 3.1**, the test function is sub-additive at the origin. -/
alias prop_3_1_unitStep_sub := unitStep_zero_subadditive
/-- **Proposition 3.1**, `γ_{r,b}` is its own sub-additive closure. -/
alias prop_3_1_tokenBucket_closure := tokenBucketNN_closure
/-- **Proposition 3.1**, `ν_{P,h,J}` is its own sub-additive closure. -/
alias prop_3_1_staircase_closure := staircase_closure
/-- **Proposition 3.1**, `δ_d` is its own sub-additive closure. -/
alias prop_3_1_delay_closure := delayNN_closure
/-- **Proposition 3.1**, `λ_R` is its own sub-additive closure. -/
alias prop_3_1_rate_closure := rateNN_closure
/-- **Proposition 3.1**, `β_{R,T}` is its own sub-additive closure. -/
alias prop_3_1_rateLatency_closure := rateLatencyNN_closure
/-- **Proposition 3.1**, `ν_{P,h,J}` super-additive closure. -/
alias prop_3_1_staircase_closure_super := staircase_closure_super

/-- **Proposition 3.2** (§3.1, p.40), convolution by a pure delay is a
right time-shift `f ∗ δ_d = t ↦ f([t−d]⁺)`. -/
alias prop_3_2_conv := conv_delayNN
/-- **Proposition 3.2**, deconvolution by a pure delay is a left time-shift
`f ⊘ δ_d = t ↦ f(t+d)`. -/
alias prop_3_2_deconv := minDeconv_delayNN

/-- **Proposition 3.3** (§3.1, p.40), `(f ⊘ δ_d)* = δ_0 ∗ (f ⊘ δ_d)` for
sub-additive `f`. -/
alias prop_3_3_closure := minDeconv_delayNN_closure
/-- **Proposition 3.3**, the sub-additive closure of a sub-additive curve is
`δ_0 ⊓ ·`. -/
alias prop_3_3_inf_delay0 := subadditiveClosureENN_eq_inf_delay0

/-- **Proposition 3.4** (§3.1.1, p.41), `δ_d ∗ δ_{d'} = δ_{d+d'}`. -/
alias prop_3_4_delay_delay := conv_delayNN_delayNN
/-- **Proposition 3.4**, `β_{R,T} = δ_T ∗ λ_R`. -/
alias prop_3_4_rateLatency := rateLatencyNN_eq_conv
/-- **Proposition 3.4**, `λ_R ∗ λ_{R'} = λ_{R∧R'}`. -/
alias prop_3_4_rate_rate := conv_rateNN_rateNN
/-- **Proposition 3.4**, `β_{R,T} ∗ β_{R',T'} = β_{R∧R',T+T'}`. -/
alias prop_3_4_rateLatency_rateLatency := conv_rateLatencyNN_rateLatencyNN
/-- **Proposition 3.4**, `γ_{r,b} ∗ γ_{r',b'} = γ ⊓ γ'`. -/
alias prop_3_4_tokenBucket := conv_tokenBucketNN_tokenBucketNN

/-- **Proposition 3.5** (§3.1.1, p.41), `δ_d ⊘ δ_{d'} = δ_{d−d'}`. -/
alias prop_3_5_delay_delay := minDeconv_delayNN_delayNN
/-- **Proposition 3.5**, `λ_R ⊘ δ_d` is an affine curve. -/
alias prop_3_5_rate_delay := minDeconv_rateNN_delayNN
/-- **Proposition 3.5**, `γ_{r,b} ⊘ δ_d` is an affine curve. -/
alias prop_3_5_tokenBucket_delay := minDeconv_tokenBucketNN_delay
/-- **Proposition 3.5**, `λ_R ⊘ λ_{R'} = λ_R` for `R ≤ R'`. -/
alias prop_3_5_rate_rate := minDeconv_rateNN_rateNN
/-- **Proposition 3.5**, `λ_R ⊘ λ_{R'} = ∞` for `R > R'`. -/
alias prop_3_5_rate_rate_top := minDeconv_rateNN_rateNN_top
/-- **Proposition 3.5**, `γ_{r,b} ⊘ λ_R` is affine for `R ≥ r`. -/
alias prop_3_5_tokenBucket_rate := minDeconv_tokenBucketNN_rateNN
/-- **Proposition 3.5**, `γ_{r,b} ⊘ λ_R = ∞` for `R < r`. -/
alias prop_3_5_tokenBucket_rate_inf := minDeconv_tokenBucketNN_rateNN_inf
/-- **Proposition 3.5**, `γ_{r,b} ⊘ β_{R,T}` is affine for `R ≥ r`. -/
alias prop_3_5_tokenBucket_rateLatency := minDeconv_tokenBucketNN_rateLatencyNN
/-- **Proposition 3.5**, `γ_{r,b} ⊘ β_{R,T} = ∞` for `R < r`. -/
alias prop_3_5_tokenBucket_rateLatency_inf := minDeconv_tokenBucketNN_rateLatencyNN_inf

/-- **Proposition 3.6** (§3.1.2, p.42), `hDev(f, δ_d) ≤ d`. -/
alias prop_3_6_le := hDevENN_delay_le
/-- **Proposition 3.6**, `hDev(f, δ_d) = d` when `f(0⁺) > 0`. -/
alias prop_3_6_eq := hDevENN_delay_eq_of_rightLimit_pos

/-- **Proposition 3.7** (§3.1.2, p.43), `hDev(γ_{r,b}, δ_d) = d`. -/
alias prop_3_7_hDev_delay := hDevENN_tokenBucketNN_delay
/-- **Proposition 3.7**, `hDev(γ_{r,b}, β_{R,T}) = T + b/R` for `r ≤ R`. -/
alias prop_3_7_hDev_rateLatency := hDevENN_tokenBucketNN_rateLatencyNN
/-- **Proposition 3.7**, `hDev(γ_{r,b}, β_{R,T}) = ∞` for `r > R`. -/
alias prop_3_7_hDev_rateLatency_top := hDevENN_tokenBucketNN_rateLatencyNN_top
/-- **Proposition 3.7**, `vDev(γ_{r,b}, δ_d) = rd + b`. -/
alias prop_3_7_vDev_delay := vDev_tokenBucketNN_delay
/-- **Proposition 3.7**, `vDev(γ_{r,b}, β_{R,T}) = rT + b` for `r ≤ R`. -/
alias prop_3_7_vDev_rateLatency := vDev_tokenBucketNN_rateLatencyNN
/-- **Proposition 3.7**, `vDev(γ_{r,b}, β_{R,T}) = ∞` for `r > R`. -/
alias prop_3_7_vDev_rateLatency_top := vDev_tokenBucketNN_rateLatencyNN_top

/-- **Definition 3.2** (§3.2, p.45): Non-negative closure [f]⁺(t)=f(t)∨0 and non-decreasing closure f↑(t)=⨆_{s≤t}f(s) (and their composite [f]⁺↑), the closure operators keeping curves in ℱ↑. -/
noncomputable def def_3_2 := @ndClosure

/-- **Lemma 3.1** (§3.2, p.45): For non-decreasing g greater than f, the non-decreasing closure f↑ is below g (least monotone majorant). -/
alias lemma_3_1 := ndClosure_le

/-- **Definition 3.3** (§3.2.1, p.46): Pseudo-inverse of a non-negative non-decreasing f: f⁻¹(x)=inf{t | f(t)≥x}. -/
noncomputable def def_3_3 := @pseudoInv

/-- **Lemma 3.2** (§3.2.1, p.46): Alternative pseudo-inverse formula for non-decreasing f: f⁻¹(x)=sup{t | f(t)<x}. -/
alias lemma_3_2 := pseudoInv_eq_sSup_lt

/-! **Proposition 3.8** (§3.2.1, p.47): Pseudo-inverse properties: f⁻¹∈ℱ₀⁺; the inversion relations t>f⁻¹(x)⇒f(t)≥x, f(t)≥x⇒t≥f⁻¹(x), t<f⁻¹(x)⇒f(t)<x, f(t)<x⇒t≤f⁻¹(x); and f⁻¹ is left-continuous. Library: DeepWiki.pseudoInv_mono, DeepWiki.pseudoInv_bot, DeepWiki.le_apply_of_pseudoInv_lt, DeepWiki.pseudoInv_le_of_le_apply, DeepWiki.apply_lt_of_lt_pseudoInv, DeepWiki.le_pseudoInv_of_apply_lt, DeepWiki.continuousWithinAt_Iio_pseudoInv, DeepWiki.leftLim_pseudoInv. -/

/-! **Proposition 3.9** (§3.2.1, p.48): Catalog of pseudo-inverses: (γ_{r,b})⁻¹=δ_{b/r} (r>0) else δ_b; (δ_d)⁻¹=γ_{0,d}; (λ_R)⁻¹=λ_{1/R}; (β_{R,T})⁻¹=γ_{1/R,T} (R>0). Library: DeepWiki.pseudoInv_tokenBucketENN, DeepWiki.pseudoInv_tokenBucketENN_zero_rate, DeepWiki.pseudoInv_delayENN_eq_tokenBucketENN, DeepWiki.pseudoInv_rateENN, DeepWiki.pseudoInv_rateLatencyENN. -/

/-- **Proposition 3.10** (§3.2.2, p.48): The convolution infimum is attained as a minimum: for non-decreasing left-continuous f,g there is u₀∈[0,t] with (f∗g)(t)=f(u₀)+g(t−u₀). -/
alias prop_3_10 := exists_minConv_eq_split_of_curves

/-- **Proposition 3.11** (§3.2.2, p.49): Continuity of the convolution: if f,g are non-decreasing and left-continuous, then f∗g is left-continuous. -/
alias prop_3_11 := isLeftContinuous_minConv_ennreal

/-- **Definition 3.4** (§3.3.1, p.50): Concave function: f∈ℱ is concave iff ∀s,t,∀p∈[0,1], p·f(s)+(1−p)·f(t) ≤ f(ps+(1−p)t). -/
abbrev def_3_4 := @IsConcaveEReal

/-! **Proposition 3.12** (§3.3.1, p.50): Properties of concave functions f,g: f+g concave; f∧g concave; if f(0)≥0 then f sub-additive; f∗g=(f−f(0)∧g−g(0))+(f(0)+g(0)) (so f∗g=f∧g when f(0)=g(0)=0); if f(0)≥0 then f*=e∧f. Library: DeepWiki.IsConcaveEReal.add, DeepWiki.IsConcaveEReal.inf, DeepWiki.IsConcaveEReal.isSubadditive, DeepWiki.minConv_eq_inf_sub_add, DeepWiki.minConv_eq_inf_of_null, DeepWiki.subadditiveClosureEReal_eq_self_of_isConcaveEReal. -/

/-- **Definition 3.5** (§3.3.2, p.51): Convex function: `f∈ℱ` is convex iff
`f(ps+(1−p)t) ≤ p·f(s)+(1−p)·f(t)` for `p∈[0,1]`. The library's
`IsConvexEReal` (the order-dual of `IsConcaveEReal`). -/
abbrev def_3_5 := @IsConvexEReal

/-- **Proposition 3.13**, sum (§3.3.2, p.51): `f+g` is convex when `f,g` are. -/
alias prop_3_13_add := IsConvexEReal.add

/-- **Proposition 3.13**, max (§3.3.2, p.51): `f∨g` is convex when `f,g` are.
(The convolution part `f∗g` convex is not separately formalized — the infimal
convolution of convex curves, needing an attained-or-ε split argument.) -/
alias prop_3_13_sup := IsConvexEReal.sup

/-- **Definition 3.6** (§3.3.2, p.53): the Legendre–Fenchel transform
`𝓛(f)(t)=⨆_{u≥0}(t·u−f(u))`. The library's `legendre`. -/
noncomputable def def_3_6 := @legendre

/-- **Proposition 3.14** (§3.3.2, p.53): the three Legendre–Fenchel transforms
of the catalog curves — `𝓛(δ_d) = λ_d` (`legendre_delayEReal`),
`𝓛(λ_R) = δ_R` (`legendre_rateEReal`), and `𝓛(β_{R,T}) = λ_T ∨ δ_R`
(`legendre_rateLatencyEReal`). The first two are the burst-delay/rate duality. -/
theorem prop_3_14_delay (d : ℝ≥0) : legendre (delayEReal d) = rateEReal d :=
  legendre_delayEReal d

/-- **Proposition 3.14** (§3.3.2, p.53), rate direction: `𝓛(λ_R) = δ_R` — the
rate curve's transform is the burst-delay. The library's `legendre_rateEReal`. -/
theorem prop_3_14_rate (R : ℝ≥0) : legendre (rateEReal R) = delayEReal R :=
  legendre_rateEReal R

/-- **Proposition 3.14** (§3.3.2, p.53), rate-latency: `𝓛(β_{R,T}) = λ_T ∨ δ_R`
— the rate-latency curve's transform is the max of the rate curve `λ_T` and the
burst-delay `δ_R`. The library's `legendre_rateLatencyEReal`. -/
theorem prop_3_14_rateLatency (R T : ℝ≥0) :
    legendre (rateLatencyEReal R T) = rateEReal T ⊔ delayEReal R :=
  legendre_rateLatencyEReal R T

/-- **Fenchel–Moreau involution on the catalog curves** (a corollary of the
Prop 3.14 duality): the biconjugate recovers the curve, `𝓛(𝓛(δ_d)) = δ_d` and
`𝓛(𝓛(λ_R)) = λ_R`. The library's `legendre_legendre_delayEReal` /
`legendre_legendre_rateEReal`. (The general involution for convex non-decreasing
curves is not formalized; here it is verified on the base curves.) -/
theorem prop_3_14_involution (d : ℝ≥0) :
    legendre (legendre (delayEReal d)) = delayEReal d ∧
      legendre (legendre (rateEReal d)) = rateEReal d :=
  ⟨legendre_legendre_delayEReal d, legendre_legendre_rateEReal d⟩

/-- **Proposition 3.15**, non-decreasing (§3.3.2, p.54): `𝓛(f)` is
non-decreasing (`monotone_legendre`); also antitone in `f`
(`legendre_antitone`). -/
theorem prop_3_15_mono (f : ℝ≥0 → EReal) : Monotone (legendre f) :=
  monotone_legendre f

/-- **Proposition 3.15**, min-to-max (§3.3.2, p.54): `𝓛(f∧g)=𝓛(f)∨𝓛(g)`.
The library's `legendre_inf`. -/
theorem prop_3_15_inf (f g : ℝ≥0 → EReal) :
    legendre (f ⊓ g) = legendre f ⊔ legendre g :=
  legendre_inf f g

/-- **Proposition 3.15**, convex (§3.3.2, p.54): `𝓛(f)` is convex for a proper
curve `f` (never `⊥`) — a supremum of affine slices. The library's
`legendre_convex`. -/
theorem prop_3_15_convex {f : ℝ≥0 → EReal} (hf : ∀ u, f u ≠ ⊥) :
    IsConvexEReal (legendre f) :=
  legendre_convex hf

/-- **Proposition 3.15**, biconjugate below (§3.3.2, p.54): `𝓛(𝓛 f) ≤ f`
pointwise — the always-true half of the Fenchel–Moreau involution. The library's
`legendre_legendre_le`. (The reverse `f ≤ 𝓛(𝓛 f)`, giving `𝓛(𝓛 f) = f` for
convex non-decreasing `f`, and `𝓛(f∗g) = 𝓛(f)+𝓛(g)` are not yet formalized.) -/
theorem prop_3_15_biconjugate_le (f : ℝ≥0 → EReal) (u : ℝ≥0) :
    legendre (legendre f) u ≤ f u :=
  legendre_legendre_le f u

end DeepWiki.Dnc
