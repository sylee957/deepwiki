import DeepWiki.TimeSeries.ArmaProcesses
import DeepWiki.TimeSeries.LinearProcess
import DeepWiki.TimeSeries.LinearProcessExamples
import DeepWiki.TimeSeries.LinearProcessArma
import DeepWiki.TimeSeries.ArmaPsiWeights
import DeepWiki.TimeSeries.CausalPolyDisk
import DeepWiki.TimeSeries.CausalArmaAcvf
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 3: Stationary ARMA Processes
Each numbered item of the book's Chapter 3 is named by its book number: an
`abbrev` aliasing the library declaration for definitions, a `theorem` (discharged
by the `DeepWiki` library) for theorems/examples. The book numbering lives here in
the catalog; the citation is in each docstring, the DOI in
`Sources.Doi_10_1007_978_1_4419_0320_4.Source`. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries
open scoped Polynomial

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

/-! ## §3.1 Causal and Invertible ARMA Processes -/

/-- **§3.1** (p.78), the lag polynomial `p(B)` (eqs 3.1.5–3.1.8): a polynomial
(the AR/MA polynomial) evaluated at the backshift operator `B`. The library's
`lagPoly`. -/
noncomputable abbrev lagPoly := @DeepWiki.TimeSeries.lagPoly

/-- **Equation (3.1.8)** (§3.1, p.78), the backshift power rule `Bʲ Xₜ = X_{t−j}` — the backshift
operator raised to power `j` shifts the time index by `j` (so `B⁰ = id`). The library's
`lagPoly_X_pow_apply`. -/
alias eq_3_1_8 := DeepWiki.TimeSeries.lagPoly_X_pow_apply

/-- **§1.4 ↔ §3.1 bridge**: the difference operator `∇ = 1 − B` of §1.4 (trend elimination) is the
lag polynomial `1 − z` evaluated at the backshift — `(1 − z)(B) x = ∇ x` — placing `∇` inside the
ARMA lag-polynomial framework (§3.1, eqs 3.1.5–3.1.8). The library's `lagPoly_one_sub_X_apply`. -/
alias difference_eq_lagPoly := DeepWiki.TimeSeries.lagPoly_one_sub_X_apply

/-- **§1.4 ↔ §3.1 bridge**: the lag-`d` difference operator `∇_d = 1 − Bᵈ` (eq 1.4.19) is the lag
polynomial `1 − zᵈ` at the backshift — `(1 − zᵈ)(B) x = ∇_d x`. The library's
`lagPoly_one_sub_X_pow_apply`. -/
alias seasonalDifference_eq_lagPoly := DeepWiki.TimeSeries.lagPoly_one_sub_X_pow_apply

/-- **Definition 3.1.1** (§3.1, p.78), white noise `WN(0,σ²)`: a stationary process
with mean zero and autocovariance `γ(h) = σ²` if `h = 0` else `0`. The library's
`IsWhiteNoise`. -/
abbrev def_3_1_1 := @DeepWiki.TimeSeries.IsWhiteNoise

/-- **Definition 3.1.2** (§3.1, p.78), the ARMA(p,q) process: a stationary `X` with
`φ(B)X = θ(B)Z`, `Z ~ WN(0,σ²)`, where `φ(z) = 1 − φ₁z − ⋯ − φₚzᵖ` (3.1.6) and
`θ(z) = 1 + θ₁z + ⋯ + θ_qz^q` (3.1.7). The library's `IsARMA`. -/
abbrev def_3_1_2 := @DeepWiki.TimeSeries.IsARMA

/-- **Equation (3.1.4)** (§3.1, p.78), the ARMA difference equation written out:
`Xₜ − φ₁X_{t−1} − ⋯ − φₚX_{t−p} = Zₜ + θ₁Z_{t−1} + ⋯ + θ_q Z_{t−q}`, i.e.
`∑ⱼ φⱼ X_{t−j} = ∑ⱼ θⱼ Z_{t−j}`. The library's `IsARMA.diffEq_apply` — the explicit-lag-sum reading
of the operator form, via `lagPoly_apply`. -/
theorem eq_3_1_4 {φ θ : ℝ[X]} {Xp Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsARMA φ θ Xp Z μ σ2) (t : ℤ) :
    ∑ j ∈ Finset.range (φ.natDegree + 1), φ.coeff j • Xp (t - j)
      = ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j • Z (t - j) :=
  h.diffEq_apply t

/-- **Equation (3.1.5)** (§3.1, p.78), the compact ARMA difference equation
`φ(B)X = θ(B)Z`. The library's `IsARMA.diffEq`. -/
abbrev eq_3_1_5 := @DeepWiki.TimeSeries.IsARMA.diffEq

/-- **Example 3.1.1** (§3.1, p.78), the MA(q) process (the case `φ ≡ 1`): `X = θ(B)Z`.
The library's `IsMA`. -/
abbrev ex_3_1_1 := @DeepWiki.TimeSeries.IsMA

/-- **Example 3.1.1** (§3.1, p.78), the MA(q) defining equation in solved form
`X = θ(B)Z`. The library's `IsMA.eq`. -/
theorem ex_3_1_1_eq {θ : ℝ[X]} {Xp Z : ℤ → Ω → ℝ} {σ2 : ℝ}
    (h : IsMA θ Xp Z μ σ2) : Xp = lagPoly θ Z :=
  h.eq

/-- **Example 3.1.1** (§3.1, p.78), the MA(q) process written out:
`Xₜ = Zₜ + θ₁Z_{t−1} + ⋯ + θ_q Z_{t−q} = ∑_{j=0}^q θⱼ Z_{t−j}`. The library's `IsMA.eq_apply`. -/
theorem ex_3_1_1_eq_apply {θ : ℝ[X]} {Xp Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsMA θ Xp Z μ σ2) (t : ℤ) :
    Xp t = ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j • Z (t - j) :=
  h.eq_apply t

-- Book-faithful restatement (step 5): white noise is uncorrelated at nonzero lags.
example {Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsWhiteNoise Z μ σ2) {k : ℤ} (hk : k ≠ 0) :
    acvfStat Z μ k = 0 := by rw [h.acvf_eq]; simp [hk]

-- Book-faithful restatement: the AR(p) defining equation `φ(B)X = Z`.
example {φ : ℝ[X]} {Xp Z : ℤ → Ω → ℝ} {σ2 : ℝ} (h : IsAR φ Xp Z μ σ2) :
    lagPoly φ Xp = Z :=
  h.eq

/-! ### §3.1 causality and invertibility (pp.83–86)

The book's **Definition 3.1.3** (causal: `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` with `∑ⱼ |ψⱼ| < ∞`),
**Definition 3.1.4** (invertible: `Zₜ = ∑ⱼ πⱼ Xₜ₋ⱼ` with `∑ⱼ |πⱼ| < ∞`), **Theorem 3.1.1**
(causal `⟺ φ(z) ≠ 0` for `|z| ≤ 1`, with `ψ(z) = θ(z)/φ(z)`), **Theorem 3.1.2** (invertible
`⟺ θ(z) ≠ 0` for `|z| ≤ 1`, with `π(z) = φ(z)/θ(z)`), and **Propositions 3.1.1/3.1.2** (absolute /
mean-square convergence of `∑ⱼ ψⱼ Xₜ₋ⱼ` and stationarity of the filtered process). What is
formalized: the **root conditions** (the right-hand sides of Theorems 3.1.1/3.1.2) as predicates
(`thm_3_1_1`/`thm_3_1_2`), the concrete `AR(1)` causality criterion, and — now — the **analytic
summability** underlying both representations: `∑ⱼ |ψⱼ| < ∞` for the causal `MA(∞)` weights `ψ = θ/φ`
(`ex_3_2_3_summable`) and `∑ⱼ |πⱼ| < ∞` for the invertible `AR(∞)` weights `π = φ/θ`
(`def_3_1_4_summable`), each with its Cauchy-convolution reciprocal recursion (`eq_3_3_3_analytic` /
`arInv_weight_recursion`), proven from the polynomial being zero-free on a disk of radius `> 1`; and — now — the **forward
direction of both Theorems 3.1.1 and 3.1.2** (`thm_3_1_1_forward`/`thm_3_1_2_forward`): the causal
`MA(∞)` process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` *solves* `φ(B) X = θ(B) Z`, and dually the invertible `AR(∞)`
inversion `Wₜ = ∑ⱼ πⱼ Xₜ₋ⱼ` solves `θ(B) W = φ(B) X` — so each root condition `⟹` the corresponding
`MA(∞)`/`AR(∞)` representation exists; and the **converse of Theorem 3.1.1** (`thm_3_1_1_converse`),
closing its causal `⟺`: a coprime `φ, θ` with an `MA(∞)` representation (summable one-sided weights
satisfying eq 3.3.3) forces `φ(z) ≠ 0` on `|z| ≤ 1` (generating-function `φ(z) ψ̂(z) = θ(z)` + Bézout),
and its `φ ↔ θ` dual for Theorem 3.1.2 (`thm_3_1_2_converse`). So **both causal/invertible `⟺`
equivalences of Theorems 3.1.1/3.1.2 are now closed** (forward + converse). **Propositions 3.1.1 and 3.1.2** are
also formalized (`prop_3_1_1`/`prop_3_1_2`): the `L²` convergence of the filtered series and the
stationarity (lag-only autocovariance `∑ⱼ ∑ₖ ψⱼ ψₖ γ(h−j+k)`) of the filtered process for correlated
input. The one substantial remainder is the two-sided Laurent existence (Thm 3.1.3, `φ ≠ 0` only on
`|z| = 1` — needs annulus/Laurent infrastructure), plus the almost-sure mode of Prop 3.1.1. -/

/-- **Theorem 3.1.1** root condition (§3.1, p.85): the autoregressive polynomial `φ` has no
zero in the closed complex unit disk, `φ(z) ≠ 0` for `|z| ≤ 1`. The library's `IsCausalPoly`.
(The full equivalence "causal `⟺` this" — Theorem 3.1.1 — is infra-blocked; see the note.) -/
abbrev thm_3_1_1 := @DeepWiki.TimeSeries.IsCausalPoly

/-- **Theorem 3.1.1, forward direction** (§3.1, p.85): for a causal ARMA, the `L²` linear process
`Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` built from the genuine `MA(∞)` weights `ψ = θ/φ` *solves the ARMA equation*
`φ(B) X = θ(B) Z`, i.e. `∑_{k=0}^p φₖ X_{t−k} = ∑_{j=0}^q θⱼ Z_{t−j}`. So `φ(z) ≠ 0` on `|z| ≤ 1`
⟹ an `MA(∞)` solution exists (the existence half of the causal ⟺; the converse needs `L²`
uniqueness). The library's `causal_arma_linearProcessLp_arma_eq`. -/
alias thm_3_1_1_forward := DeepWiki.TimeSeries.causal_arma_linearProcessLp_arma_eq

/-- **Theorem 3.1.1, converse direction** (§3.1, p.85): if `φ, θ` are coprime and the `MA(∞)`
weights `ψ` exist (absolutely summable, one-sided, satisfying the recursion `∑_{i+j=m} φᵢ ψⱼ = θ_m`),
then `φ` is causal — `φ(z) ≠ 0` for `|z| ≤ 1`. By the generating-function identity `φ(z) ψ̂(z) = θ(z)`
on the closed disk: a root `φ(z₀) = 0` forces `θ(z₀) = 0`, contradicting coprimality. The other half
of the causal `⟺`; the library's `isCausalPoly_of_summable_recursion`. -/
alias thm_3_1_1_converse := DeepWiki.TimeSeries.isCausalPoly_of_summable_recursion

/-- **Theorem 3.1.2** root condition (§3.1, p.86): the moving-average polynomial `θ` has no
zero in the closed complex unit disk, `θ(z) ≠ 0` for `|z| ≤ 1`. The library's
`IsInvertiblePoly`. (The full equivalence "invertible `⟺` this" is infra-blocked.) -/
abbrev thm_3_1_2 := @DeepWiki.TimeSeries.IsInvertiblePoly

/-- **Definition 3.1.4 / Theorem 3.1.2 analytic content** (§3.1, p.86): for an invertible ARMA
(`θ(z) ≠ 0` on `|z| ≤ 1`), the `AR(∞)` weights `πⱼ` — the Taylor coefficients of `φ(z)/θ(z)` — are
absolutely summable, `∑ⱼ |πⱼ| < ∞`. The analytic content behind the `AR(∞)` representation
`Zₜ = ∑ⱼ πⱼ Xₜ₋ⱼ`; the invertibility dual of the causal `ex_3_2_3_summable` (same zero-free-disk
estimate, `φ, θ` swapped). The library's `summable_norm_cauchyPowerSeries_arInv`. -/
alias def_3_1_4_summable := DeepWiki.TimeSeries.summable_norm_cauchyPowerSeries_arInv

/-- **The `AR(∞)` weight recursion `∑_{i+j=m} θᵢ πⱼ = φ_m`** (§3.1): for an invertible ARMA, the
`AR(∞)` weights `π = φ/θ` reproduce `φ` under Cauchy convolution with `θ` — the invertibility dual of
the `MA(∞)` recursion `eq_3_3_3_analytic`. The library's `conv_coeff_arInv_eq_coeff`. -/
alias arInv_weight_recursion := DeepWiki.TimeSeries.conv_coeff_arInv_eq_coeff

/-- **Theorem 3.1.2, forward direction** (§3.1, p.86): for an invertible ARMA, the `AR(∞)` inversion
`Wₜ = ∑ⱼ πⱼ Xₜ₋ⱼ` (`π = φ/θ`) solves `θ(B) W = φ(B) X` — so `θ(z) ≠ 0` on `|z| ≤ 1` ⟹ an `AR(∞)`
representation exists, recovering the noise `Zₜ = ∑ⱼ πⱼ Xₜ₋ⱼ`. The `φ ↔ θ` dual of `thm_3_1_1_forward`.
The library's `invertible_arma_linearProcessLp_arInv_eq`. -/
alias thm_3_1_2_forward := DeepWiki.TimeSeries.invertible_arma_linearProcessLp_arInv_eq

/-- **Theorem 3.1.2, converse direction** (§3.1, p.86): if `φ, θ` are coprime and the `AR(∞)` weights
`π` exist (absolutely summable, one-sided, satisfying `∑_{i+j=m} θᵢ πⱼ = φ_m`), then `θ` is invertible
— `θ(z) ≠ 0` for `|z| ≤ 1`. The `φ ↔ θ` dual of `thm_3_1_1_converse`; closes the invertible `⟺`. The
library's `isInvertiblePoly_of_summable_recursion`. -/
alias thm_3_1_2_converse := DeepWiki.TimeSeries.isInvertiblePoly_of_summable_recursion

/-- **Proposition 3.1.1** (§3.1, p.83), the `L²` convergence half: if `∑ⱼ |ψⱼ| < ∞` and the input `X`
is `L²`-bounded, the filtered series `∑ⱼ ψⱼ Xₜ₋ⱼ` converges in `L²` (`HasSum` in `Lp ℝ 2 μ`). The
library's `hasSum_linearProcessLp` (the almost-sure/absolute mode is not formalized). -/
alias prop_3_1_1 := DeepWiki.TimeSeries.hasSum_linearProcessLp

/-- **Proposition 3.1.2** (§3.1, p.84), the filtered process is stationary: the linear filter
`Yₜ = ∑ⱼ ψⱼ Xₜ₋ⱼ` of a stationary `L²` process `X` (covariance `⟪Xₐ, X_b⟫ = γ(a−b)`) has
autocovariance `⟪Y_{t+h}, Yₜ⟫ = ∑ⱼ ∑ₖ ψⱼ ψₖ γ(h−j+k)`, depending only on the lag `h`. The library's
`linearProcessLp_inner_cov`. -/
alias prop_3_1_2 := DeepWiki.TimeSeries.linearProcessLp_inner_cov

/-- **§3.1** (AR(1) process, p.81): an `AR(1)` process with autoregressive polynomial
`φ(z) = 1 − φ₁z`, i.e. `(1 − φ₁B)X = Z`, satisfies the autoregressive recursion
`Xₜ − φ₁ Xₜ₋₁ = Zₜ` (equivalently `Xₜ = φ₁ Xₜ₋₁ + Zₜ`) — the expanded reading of the operator
difference equation. The library's `IsAR.ar1_apply`. -/
theorem ar1_difference_eq {φ₁ : ℝ} {Xp Z : ℤ → Ω → ℝ} {σ2 : ℝ}
    (h : IsAR (1 - Polynomial.C φ₁ * Polynomial.X) Xp Z μ σ2) (t : ℤ) :
    Xp t - φ₁ • Xp (t - 1) = Z t :=
  h.ar1_apply t

/-- **§3.1** (AR(1) causality, p.81): the `AR(1)` process `Xₜ = φ₁Xₜ₋₁ + Zₜ` is causal iff
`|φ₁| < 1` — its autoregressive polynomial `1 − φ₁z` has its only root `1/φ₁` outside the
closed unit disk. The library's `isCausalPoly_ar1`. -/
theorem ar1_causal_iff (φ₁ : ℝ) :
    IsCausalPoly (1 - Polynomial.C φ₁ * Polynomial.X) ↔ |φ₁| < 1 :=
  isCausalPoly_ar1 φ₁

/-! ## §3.2 Moving Average Processes of Infinite Order (MA(∞)), pp.89–91

The `L²` mean-square convergence of `∑ⱼ ψⱼ Zₜ₋ⱼ` and the resulting autocovariance — the analytic
layer formerly flagged infra-blocked — **are now formalized** in `DeepWiki.TimeSeries.LinearProcess`
(built over the complete space `Lp ℝ 2 μ`). The library's `linearProcessLp` is the *two-sided*
general linear process `∑_{j∈ℤ} ψⱼ Zₜ₋ⱼ`; Definition 3.2.1's one-sided `MA(∞)` is the special case
`ψⱼ = 0` for `j < 0`. -/

/-- **Definition 3.2.1** (§3.2, p.89, eq 3.2.1), the moving average process of infinite order
`MA(∞)`: `Xₜ = ∑_{j=0}^∞ ψⱼ Zₜ₋ⱼ` with `∑_{j=0}^∞ |ψⱼ| < ∞` and `Z ~ WN(0,σ²)`. The library's
`linearProcessLp` (the two-sided `L²` `tsum` `∑_{j∈ℤ} ψⱼ Zₜ₋ⱼ`; the `MA(∞)` is the causal case
`ψⱼ = 0` for `j < 0`). -/
noncomputable abbrev def_3_2_1 := @DeepWiki.TimeSeries.linearProcessLp

/-- **Definition 3.2.1 / Theorem 3.2.1** convergence (§3.2, pp.89–91): the defining series
`∑ⱼ ψⱼ Zₜ₋ⱼ` converges in mean square (`L²`) when `∑ⱼ |ψⱼ| < ∞` and `Z` is uniformly `L²`-bounded,
since `∑ⱼ ‖ψⱼ Zₜ₋ⱼ‖ ≤ C ∑ⱼ |ψⱼ| < ∞` and `Lp ℝ 2 μ` is complete. The library's
`hasSum_linearProcessLp`. -/
alias thm_3_2_1_conv := DeepWiki.TimeSeries.hasSum_linearProcessLp

/-- **Theorem 3.2.1** (§3.2, p.91, eq 3.2.4), the `MA(∞)` autocovariance: the linear process is
stationary with mean zero and `γ(k) = σ² ∑_{j=0}^∞ ψⱼ ψ_{j+|k|}`. The library's
`linearProcessLp_inner` proves the two-sided `L²` form `⟪X_{t+h}, Xₜ⟫ = σ² ∑_{k∈ℤ} ψₖ ψ_{k+h}` for
innovations orthogonal up to `σ²` (`⟪Zₐ,Z_b⟫ = σ²·[a=b]`); for a one-sided causal `ψ` this is
`σ² ∑_{k≥0} ψₖ ψ_{k+|h|}` (eq 3.2.4), as `γ(h) = γ(−h)`. -/
alias thm_3_2_1 := DeepWiki.TimeSeries.linearProcessLp_inner

/-- **§2.7 ↔ §3.2 bridge** (the `L²` geometry behind eq 3.2.4): for a mean-zero process embedded in
`L²`, the autocovariance is the inner product, `γ(h) = cov(X_{t+h}, Xₜ) = ⟪X_{t+h}, Xₜ⟫`. This
identifies the `linearProcessLp_inner` value `σ² ∑ₖ ψₖ ψ_{k+h}` with the autocovariance `γ(h)`, and
shows the orthogonality hypothesis `⟪Zₐ,Z_b⟫ = σ²·[a=b]` is exactly mean-zero white noise with
`cov(Zₐ,Z_b) = σ²·[a=b]`. The library's `inner_eq_covariance`. -/
alias innerProduct_eq_autocovariance := DeepWiki.TimeSeries.inner_eq_covariance

/-- **Theorem 3.2.1** (§3.2, p.91), the book-faithful endpoint: a linear process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ`
(`∑ⱼ |ψⱼ| < ∞`) driven by a genuine `WN(0,σ²)` (Definition 3.1.1, `IsWhiteNoise`) has autocovariance
`γ(h) = σ² ∑ₖ ψₖ ψ_{k+h}` — starting from the book's white-noise predicate, not an abstract
`L²`-orthogonality hypothesis. The library's `isWhiteNoise_linearProcess_acvf`. -/
alias thm_3_2_1_whiteNoise := DeepWiki.TimeSeries.isWhiteNoise_linearProcess_acvf

-- Book-faithful restatement (step 5): Theorem 3.2.1's autocovariance γ(k)=σ²∑ⱼψⱼψ_{j+|k|}
-- (eq 3.2.4), in the two-sided L² inner-product form at lag h.
example {ψ : ℤ → ℝ} (hψ : Summable ψ) {Z : ℤ → MeasureTheory.Lp ℝ 2 μ} {C σ2 : ℝ}
    (hZb : ∀ t, ‖Z t‖ ≤ C) (hZorth : ∀ a b, inner ℝ (Z a) (Z b) = if a = b then σ2 else 0)
    (t h : ℤ) :
    inner ℝ (linearProcessLp ψ Z (t + h)) (linearProcessLp ψ Z t) = σ2 * ∑' k, ψ k * ψ (k + h) :=
  linearProcessLp_inner hψ hZb hZorth t h

/-- **Example 3.2.1** (§3.2, p.89): the `MA(q)` process `Xₜ = ∑_{j=0}^q θⱼ Zₜ₋ⱼ` is an `MA(∞)` with
the finite filter `ψⱼ = θⱼ` — vacuously absolutely summable (finite support), so an `MA(∞)`
(Definition 3.2.1). The library's `summable_maqFilter` (the filter is `maqFilter`). -/
alias ex_3_2_1 := DeepWiki.TimeSeries.summable_maqFilter

/-- **Example 3.2.1** (§3.2, p.89): the `MA(∞)` linear process with the finite `MA(q)` filter is the
finite moving average `Xₜ = ∑_{j=0}^q θⱼ Zₜ₋ⱼ` (`= θ(B) Z`). The library's
`linearProcessLp_maqFilter_eq`. -/
alias ex_3_2_1_eq := DeepWiki.TimeSeries.linearProcessLp_maqFilter_eq

/-- **§3.2 (the `MA(q)` autocovariance has finite support)**: `∑ₖ ψₖ ψ_{k+h} = 0` for `|h| > q`, so by
Theorem 3.2.1 the `MA(q)` autocovariance `γ(h) = σ² ∑ₖ ψₖ ψ_{k+h}` vanishes at every lag beyond the
order `q = deg θ` — the characterizing property of an `MA(q)`. The library's
`maqFilter_tsum_mul_shift_eq_zero`. -/
alias maq_acvf_finite_support := DeepWiki.TimeSeries.maqFilter_tsum_mul_shift_eq_zero

/-- **Example 3.2.1 (faithful `MA(q)` ↔ `θ(B) Z`)** (§3.2, p.89): the `L²` linear process with the
finite `MA(q)` filter, over square-integrable noise embedded in `Lp`, agrees almost everywhere with
the book's `MA(q)` random-variable process `θ(B) Z` (`lagPoly θ Z`) — connecting the abstract `Lp`
`MA(∞)` construction to the process predicate `IsMA`. The library's
`coeFn_linearProcessLp_maqFilter`. -/
alias ex_3_2_1_rv := DeepWiki.TimeSeries.coeFn_linearProcessLp_maqFilter

/-- **Example 3.2.2** (§3.2, p.89): the causal `AR(1)` process `Xₜ = φXₜ₋₁ + Zₜ` with `|φ| < 1` is
an `MA(∞)` with weights `ψⱼ = φʲ` (`j ≥ 0`) — the filter `ar1Filter φ` is absolutely summable (a
geometric series `∑_{j≥0}|φ|ʲ < ∞`), so `Xₜ = ∑_{j≥0} φʲ Zₜ₋ⱼ` is a well-defined `MA(∞)` (Definition
3.2.1). The library's `summable_ar1Filter` (the weights are `ar1Filter`). -/
alias ex_3_2_2 := DeepWiki.TimeSeries.summable_ar1Filter

/-- **§3.3 (the AR(1) variance):** the causal `AR(1)` linear process of Example 3.2.2 (`|φ| < 1`,
innovations orthogonal up to `σ²`) has variance `γ(0) = ⟪Xₜ, Xₜ⟫ = σ²/(1 − φ²)` — `σ² ∑_{j≥0} φ^{2j}`
via the squared geometric weights. The library's `ar1_linearProcess_variance`. -/
alias ar1_variance := DeepWiki.TimeSeries.ar1_linearProcess_variance

/-- **§3.3 (the AR(1) autocovariance):** the causal `AR(1)` linear process of Example 3.2.2
(`|φ| < 1`) has autocovariance `γ(h) = σ² φʰ/(1 − φ²)` for `h ≥ 0` — hence `σ² φ^|h|/(1 − φ²)` by
evenness. The standard `AR(1)` ACVF. The library's `ar1_linearProcess_acvf`. -/
alias ar1_acvf := DeepWiki.TimeSeries.ar1_linearProcess_acvf

/-! ### §3.3 First Method: the `ψ`-weight recursion `ψ = θ/φ` -/

/-- **Equation (3.3.2)** (§3.3, p.91): the `ψ`-weight power series `ψ(z) = θ(z)/φ(z)` of an ARMA
process, as a formal power series (`PowerSeries ℝ`). The library's `armaPsi`. -/
noncomputable abbrev eq_3_3_2 := @DeepWiki.TimeSeries.armaPsi

/-- **Equation (3.3.3)** (§3.3, p.91): the `ψ`-weight recursion. When `φ(0) ≠ 0` (e.g. `φ(0) = 1`),
the coefficients of `ψ = θ/φ` satisfy `∑_{k=0}^j φₖ ψ_{j−k} = θⱼ` (the `zʲ`-coefficient of `φ ψ = θ`;
with `φ₀ = 1` this is the book's `ψⱼ − ∑_{0<k≤j} φ'ₖ ψ_{j−k} = θⱼ`). The library's
`armaPsi_coeff_recursion`. -/
alias eq_3_3_3 := DeepWiki.TimeSeries.armaPsi_coeff_recursion

/-- **Example 3.2.2 ↔ §3.3:** the `AR(1)` `ψ`-weights computed via the abstract reciprocal
`ψ = θ/φ` (`φ(z) = 1 − φ₁z`, `θ = 1`) are the geometric weights `ψⱼ = φ₁ʲ` — confirming `armaPsi`
agrees with the explicit `ar1Filter` of Example 3.2.2. The library's `coeff_armaPsi_ar1`. -/
alias ar1_psi_weights := DeepWiki.TimeSeries.coeff_armaPsi_ar1

/-- **§3.3 Second Method** (§3.3, p.92), the homogeneous difference equation for the autocovariance:
the causal-ARMA acvf `γ(m) = σ² ∑ⱼ ψⱼ ψ_{j+m}` satisfies `∑_{k=0}^p φₖ γ(h−k) = 0` once the
`φ`-convolution of the `ψ`-weights vanishes (`ψⱼ · ∑ₖ φₖ ψ_{j+(h−k)} = 0` for all `j`) — which the
recursion (`eq_3_3_3`, `∑ₖ φₖ ψ_{m−k} = θ_m = 0` for `m > deg θ`) supplies for `h > deg θ`. The
library's `acvf_homogeneous`. -/
alias acvf_secondMethod := DeepWiki.TimeSeries.acvf_homogeneous

/-- **§3.3 Second Method for a causal `ARMA(p,q)`** (§3.3, p.92): if the `ψ`-weights are summable
(the causal `∑ⱼ |ψⱼ| < ∞`), one-sided (`ψⱼ = 0`, `j < 0`), and satisfy the recursion-vanishing
`∑ₖ φₖ ψ_{m−k} = 0` for `m > deg θ` (eq 3.3.3 with `θ_m = 0`), then `∑_{k=0}^p φₖ γ(h−k) = 0` for all
`h > deg θ`. The summability is the analytic content causality would supply (a hypothesis, as that
estimate is out of scope). The library's `arma_acvf_homogeneous`. -/
alias arma_acvf_secondMethod := DeepWiki.TimeSeries.arma_acvf_homogeneous

/-- **Example 3.2.3 analytic content** (§3.2/§3.3, p.91): for a *causal* `ARMA(p,q)` — `φ(z) ≠ 0` on
the closed unit disk `|z| ≤ 1` (`IsCausalPoly`) — the `MA(∞)` weights `ψⱼ` (the Taylor coefficients
of `θ(z)/φ(z)` at `0`) are absolutely summable, `∑ⱼ |ψⱼ| < ∞`. This is the analytic decay
(`|ψⱼ| = O(rʲ)`, `r > 1`) that causality forces and that turns the algebraic `ψ = θ/φ` into a genuine
`L²` `MA(∞)`; proven from `φ` zero-free on a disk of radius `> 1` (compactness) + the Cauchy
power-series radius estimate. The library's `summable_norm_cauchyPowerSeries_div_aeval`. -/
alias ex_3_2_3_summable := DeepWiki.TimeSeries.summable_norm_cauchyPowerSeries_div_aeval

/-- **The analytic and formal `ψ`-weights coincide** (§3.2/§3.3, the eq 3.3.2 bridge): for a causal
ARMA, the Taylor coefficients of `θ(z)/φ(z)` (the analytic `MA(∞)` weights) are *exactly* the
coefficients of the formal power series `armaPsi φ θ = θ/φ` (`eq_3_3_2`), cast `ℝ → ℂ`. So the
analytic weights are real, and the formal reciprocal `ψ = θ/φ` is their genuine value — not merely a
formal stand-in. By uniqueness of `↑φ · ψ = ↑θ` in the domain `ℂ⟦X⟧`. The library's
`cauchyCoeff_div_aeval_eq_armaPsi`. -/
alias eq_3_3_2_analytic := DeepWiki.TimeSeries.cauchyCoeff_div_aeval_eq_armaPsi

/-- **Equation (3.3.3), analytic (Taylor-coefficient) form** (§3.3, p.91): for a causal ARMA, the
`MA(∞)` weights `ψⱼ` (Taylor coefficients of `θ/φ`) satisfy the Cauchy convolution
`∑_{i+j=m} φᵢ ψⱼ = θ_m` for every `m` — the coefficient-uniqueness identity for `φ(z)·(θ(z)/φ(z)) = θ(z)`,
the analytic realization of the formal recursion `eq_3_3_3`. The library's `conv_coeff_div_eq_coeff`. -/
alias eq_3_3_3_analytic := DeepWiki.TimeSeries.conv_coeff_div_eq_coeff

/-- **§3.3 Second Method for a causal `ARMA(p,q)`, summability discharged** (§3.3, p.92): for a causal
AR polynomial `φ` (`IsCausalPoly`), there exist real, summable, one-sided `MA(∞)` weights `ψ` such
that the autocovariance `γ(h) = σ² ∑ⱼ ψⱼ ψ_{j+h}` satisfies `∑_{k=0}^p φₖ γ(h−k) = 0` at every lag
`h > q = deg θ`. Unlike `arma_acvf_secondMethod`, the weight summability is *not* a hypothesis here —
it is the analytic `∑ⱼ |ψⱼ| < ∞` (`ex_3_2_3_summable`), and the recursion-vanishing is the real part
of `eq_3_3_3_analytic`. The closed causal-ARMA §3.3 result. The library's
`causal_arma_acvf_homogeneous`. -/
alias arma_acvf_secondMethod_causal := DeepWiki.TimeSeries.causal_arma_acvf_homogeneous

/-- **Example 3.2.3 (causal ARMA `MA(∞)`), `L²`-process form** (§3.2/§3.3, p.91): for a causal ARMA
over genuine white noise, the `L²` linear process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` (`linearProcessLp`) built from the
real, summable, one-sided `MA(∞)` weights `ψ = Re(θ/φ)` has the Theorem 3.2.1 autocovariance
`⟪X_{t+k}, Xₜ⟫ = σ² ∑ⱼ ψⱼ ψ_{j+k}`, and that autocovariance solves the §3.3 homogeneous AR recursion
`∑ₖ φₖ γ(h−k) = 0` for `h > q` — the full process-level realization, with weight summability
discharged from causality (`ex_3_2_3_summable`). The library's
`causal_arma_linearProcess_acvf_homogeneous`. -/
alias ex_3_2_3 := DeepWiki.TimeSeries.causal_arma_linearProcess_acvf_homogeneous

/-! ### §3.1 existence (Thm 3.1.3) and §3.3 ARMA-specific computation

**Theorem 3.1.3** (§3.1, p.88): when `φ(z) ≠ 0` for all `|z| = 1`, the ARMA equations have the
unique stationary solution `Xₜ = ∑_{j=-∞}^{∞} ψⱼ Zₜ₋ⱼ`, with `ψ` the Laurent expansion of `θ/φ`
on an annulus `r⁻¹ < |z| < r` (eq 3.1.21). The *solution form* `∑ⱼ ψⱼ Zₜ₋ⱼ` and its `L²`
convergence are now `linearProcessLp` / `hasSum_linearProcessLp`; what remains infra-blocked is the
**Laurent/power-series reciprocal** producing the `ψ`-weights from `θ, φ`.

**§3.2 remainder.** **Examples 3.2.1** (MA(q), `ψⱼ = θⱼ`) and **3.2.2** (causal AR(1), `ψⱼ = φʲ`) are
formalized (`ex_3_2_1`/`ex_3_2_2` above). **Example 3.2.3** (causal ARMA as `∑ψⱼzʲ = θ(z)/φ(z)`): the
`MA(∞)` weights exist algebraically as the formal power series `θ/φ` (`PowerSeries.inv`, `φ(0) = 1` a
unit) and — now — are genuinely *absolutely summable*, `∑ⱼ |ψⱼ| < ∞` (`ex_3_2_3_summable`). The
analytic decay `|ψⱼ| = O(rʲ)` forced by causality (`φ ≠ 0` on `|z| ≤ 1`) is *proven*, no longer out of
scope: `φ` is zero-free on a disk of radius `> 1` by compactness (`IsCausalPoly.exists_radius_gt_one`),
so `θ/φ` is analytic there and its Cauchy power-series coefficients (the `ψ`-weights) are absolutely
summable. These summable weights are reassembled into the `L²` random-variable process
`Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` over genuine white noise, with the Theorem 3.2.1 autocovariance and the §3.3
recursion, in `ex_3_2_3` (`causal_arma_linearProcess_acvf_homogeneous`). Still unformalized:
**Proposition 3.2.1** (a
zero-mean stationary `q`-correlated process — `γ(h) = 0` for `|h| > q`, `γ(q) ≠ 0` — is an MA(q)),
which needs the `L²` innovations/projection algorithm of §2.3–§2.4.

**§3.3 (computing the ARMA autocovariance).** The **First Method** is formalized at the algebraic
level: the formula `γ(k) = σ² ∑_{j≥0} ψⱼ ψ_{j+|k|}` (eq 3.3.1) **is** Theorem 3.2.1 (`thm_3_2_1`)
specialized to the ARMA `ψ`-weights, with weights the formal power series `ψ = θ/φ` (eq 3.3.2,
`eq_3_3_2`) and the Cauchy recursion `∑_{k≤j} φₖ ψ_{j−k} = θⱼ` (eq 3.3.3, `eq_3_3_3`). The earlier
*analytic* gap — the absolute convergence `∑ⱼ |ψⱼ| < ∞` — is now **closed** (`ex_3_2_3_summable`), and
its Taylor-coefficient recursion `∑_{i+j=m} φᵢ ψⱼ = θ_m` is proven (`eq_3_3_3_analytic`, by
power-series coefficient uniqueness for `φ·(θ/φ) = θ`). The homogeneous-difference-equation (Second)
method `∑_{k=0}^p φₖ γ(h−k) = 0` is formalized in three forms: the abstract `acvf_secondMethod` (given
the `φ`-convolution-vanishing), the `ARMA` form `arma_acvf_secondMethod` (given summable + one-sided +
recursion-vanishing `ψ`-weights), and — the closed endpoint — `arma_acvf_secondMethod_causal`, which
*discharges* the summability hypothesis from causality alone: it builds the real, summable, one-sided
weights `ψⱼ = Re(θ/φ)ⱼ` and derives the recursion-vanishing as the real part of `eq_3_3_3_analytic`,
so a causal `ARMA(p,q)` autocovariance provably satisfies `∑ₖ φₖ γ(h−k) = 0` for `h > q` with no
analytic side-condition left to assume.

The finite `MA(q)` autocovariance `γ(h) = σ² ∑ⱼ θⱼ θ_{j+|h|}` is the algebraically-finite special
case; the concrete low-order cases (MA(1), MA(2)) are proved in `DeepWiki.TimeSeries.ProcessExamples`
(`maProcess1`, `maProcess2`). -/

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§3.1: Theorem 3.1.3 (two-sided/noncausal Laurent solution, `φ ≠ 0` only on `|z| = 1`) [infra]
§3.2: Proposition 3.2.1 (a zero-mean `q`-correlated stationary process is an `MA(q)`) [infra]
(Thm 3.1.3 needs annulus/Laurent reciprocal infrastructure; Prop 3.2.1 needs the L²-innovations/
projection-of-past layer. Thms 3.1.1/3.1.2 ⟺, Props 3.1.1/3.1.2, Exs 3.2.1–3.2.3, and all of §3.3
are formalized.) -/

end DeepWiki.Ts
