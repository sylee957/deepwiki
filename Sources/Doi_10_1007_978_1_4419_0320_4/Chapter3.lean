import DeepWiki.TimeSeries.ArmaProcesses
import DeepWiki.TimeSeries.LinearProcess
import DeepWiki.TimeSeries.LinearProcessExamples
import DeepWiki.TimeSeries.LinearProcessArma
import DeepWiki.TimeSeries.ArmaPsiWeights
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
`⟺ θ(z) ≠ 0` for `|z| ≤ 1`), and **Propositions 3.1.1/3.1.2** (absolute / mean-square
convergence of `∑ⱼ ψⱼ Xₜ₋ⱼ` and stationarity of the filtered process) all rest on the
mean-square convergence of `∑ⱼ ψⱼ Zₜ₋ⱼ` and the power-series reciprocal `1/φ`. That analytic
layer is **not yet formalized** — infra-blocked, like the deferred analytic items elsewhere
in the project (it needs `PowerSeries`-reciprocal, `∑|ψⱼ| < ∞` summability, and `L²`-limit
infrastructure). What *is* formalized: the **root conditions** (the right-hand sides of
Theorems 3.1.1/3.1.2) as predicates, and the concrete `AR(1)` causality criterion. -/

/-- **Theorem 3.1.1** root condition (§3.1, p.85): the autoregressive polynomial `φ` has no
zero in the closed complex unit disk, `φ(z) ≠ 0` for `|z| ≤ 1`. The library's `IsCausalPoly`.
(The full equivalence "causal `⟺` this" — Theorem 3.1.1 — is infra-blocked; see the note.) -/
abbrev thm_3_1_1 := @DeepWiki.TimeSeries.IsCausalPoly

/-- **Theorem 3.1.2** root condition (§3.1, p.86): the moving-average polynomial `θ` has no
zero in the closed complex unit disk, `θ(z) ≠ 0` for `|z| ≤ 1`. The library's
`IsInvertiblePoly`. (The full equivalence "invertible `⟺` this" is infra-blocked.) -/
abbrev thm_3_1_2 := @DeepWiki.TimeSeries.IsInvertiblePoly

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

/-! ### §3.1 existence (Thm 3.1.3) and §3.3 ARMA-specific computation — still infra-blocked

**Theorem 3.1.3** (§3.1, p.88): when `φ(z) ≠ 0` for all `|z| = 1`, the ARMA equations have the
unique stationary solution `Xₜ = ∑_{j=-∞}^{∞} ψⱼ Zₜ₋ⱼ`, with `ψ` the Laurent expansion of `θ/φ`
on an annulus `r⁻¹ < |z| < r` (eq 3.1.21). The *solution form* `∑ⱼ ψⱼ Zₜ₋ⱼ` and its `L²`
convergence are now `linearProcessLp` / `hasSum_linearProcessLp`; what remains infra-blocked is the
**Laurent/power-series reciprocal** producing the `ψ`-weights from `θ, φ`.

**§3.2 remainder.** **Examples 3.2.1** (MA(q), `ψⱼ = θⱼ`) and **3.2.2** (causal AR(1), `ψⱼ = φʲ`) are
now formalized (`ex_3_2_1`/`ex_3_2_2` above). Still unformalized: **Example 3.2.3** (causal ARMA as
`∑ψⱼzʲ = θ(z)/φ(z)`) — the `MA(∞)` weights exist algebraically as the formal power series `θ/φ`
(`PowerSeries.inv`, `φ(0) = 1` a unit), but the `L²` representation needs `∑ⱼ |ψⱼ| < ∞`, which follows
only from the *analytic* decay `|ψⱼ| = O(rʲ)` forced by causality (`φ ≠ 0` on `|z| ≤ 1`) — an estimate
not in scope (infra-blocked); and **Proposition 3.2.1** (a zero-mean stationary `q`-correlated process
— `γ(h) = 0` for `|h| > q`, `γ(q) ≠ 0` — is an MA(q)), which needs the `L²` innovations/projection
algorithm of §2.3–§2.4.

**§3.3 (computing the ARMA autocovariance).** The **First Method** is now formalized at the
algebraic level: the formula `γ(k) = σ² ∑_{j≥0} ψⱼ ψ_{j+|k|}` (eq 3.3.1) **is** Theorem 3.2.1
(`thm_3_2_1`) specialized to the ARMA `ψ`-weights, and the weights themselves are the formal power
series `ψ = θ/φ` (eq 3.3.2, `eq_3_3_2`) with the Cauchy recursion `∑_{k≤j} φₖ ψ_{j−k} = θⱼ`
(eq 3.3.3, `eq_3_3_3`). What remains infra-blocked is the *analytic* link: the absolute convergence
`∑ⱼ |ψⱼ| < ∞` of the `ψ`-weights (the decay `|ψⱼ| = O(rʲ)` forced by causality `φ ≠ 0` on `|z| ≤ 1`),
which is what lets the algebraic `ψ = θ/φ` actually drive an `L²` `MA(∞)`. The
homogeneous-difference-equation (Second) method `∑_{k=0}^p φₖ γ(h−k) = 0` is now formalized — the
abstract form `acvf_secondMethod` (given the `φ`-convolution-vanishing) and the `ARMA` form
`arma_acvf_secondMethod` (given summable + one-sided + recursion-vanishing `ψ`-weights, with
summability the honest stand-in for the analytic decay). The only piece left is connecting those
hypotheses to `armaPsi` itself: the `ℤ`-extended `ψ`-filter and the lift of eq 3.3.3 to its
`ℤ`-convolution form supply the recursion-vanishing, while summability remains the analytic block.

The finite `MA(q)` autocovariance `γ(h) = σ² ∑ⱼ θⱼ θ_{j+|h|}` is the algebraically-finite special
case; the concrete low-order cases (MA(1), MA(2)) are proved in `DeepWiki.TimeSeries.ProcessExamples`
(`maProcess1`, `maProcess2`). -/

end DeepWiki.Ts
