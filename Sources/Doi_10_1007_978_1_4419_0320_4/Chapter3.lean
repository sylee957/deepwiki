import DeepWiki.TimeSeries.ArmaProcesses
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

/-- **Definition 3.1.1** (§3.1, p.78), white noise `WN(0,σ²)`: a stationary process
with mean zero and autocovariance `γ(h) = σ²` if `h = 0` else `0`. The library's
`IsWhiteNoise`. -/
abbrev def_3_1_1 := @DeepWiki.TimeSeries.IsWhiteNoise

/-- **Definition 3.1.2** (§3.1, p.78), the ARMA(p,q) process: a stationary `X` with
`φ(B)X = θ(B)Z`, `Z ~ WN(0,σ²)`, where `φ(z) = 1 − φ₁z − ⋯ − φₚzᵖ` (3.1.6) and
`θ(z) = 1 + θ₁z + ⋯ + θ_qz^q` (3.1.7). The library's `IsARMA`. -/
abbrev def_3_1_2 := @DeepWiki.TimeSeries.IsARMA

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

/-- **§3.1** (AR(1) causality, p.81): the `AR(1)` process `Xₜ = φ₁Xₜ₋₁ + Zₜ` is causal iff
`|φ₁| < 1` — its autoregressive polynomial `1 − φ₁z` has its only root `1/φ₁` outside the
closed unit disk. The library's `isCausalPoly_ar1`. -/
theorem ar1_causal_iff (φ₁ : ℝ) :
    IsCausalPoly (1 - Polynomial.C φ₁ * Polynomial.X) ↔ |φ₁| < 1 :=
  isCausalPoly_ar1 φ₁

/-! ### §3.1 (existence) and §3.2–§3.3 (MA(∞), the ARMA autocovariance), pp.88–93 — infra-blocked

**Theorem 3.1.3** (§3.1, p.88): when `φ(z) ≠ 0` for all `|z| = 1`, the ARMA equations have the
unique stationary solution `Xₜ = ∑_{j=-∞}^{∞} ψⱼ Zₜ₋ⱼ`, with `ψ` the Laurent expansion of
`θ/φ` on an annulus `r⁻¹ < |z| < r` (eq 3.1.21).

**§3.2 (MA(∞) processes).** **Definition 3.2.1** (`Xₜ = ∑_{j≥0} ψⱼ Zₜ₋ⱼ`, `∑|ψⱼ| < ∞`),
**Examples 3.2.1–3.2.3** (MA(q); causal AR(1) as `ψⱼ = φⱼ`; causal ARMA as `ψ = θ/φ`),
**Proposition 3.2.1** (a zero-mean stationary process that is `q`-correlated — `γ(h) = 0` for
`|h| > q`, `γ(q) ≠ 0` — is an MA(q), via the `L²` innovations/projection argument of §2.3–§2.4),
and **Theorem 3.2.1** (the MA(∞) autocovariance `γ(h) = σ² ∑_{j≥0} ψⱼ ψ_{j+|h|}`).

**§3.3 (computing the ARMA autocovariance).** The `ψ`-weight method (`γ(k) = σ² ∑ⱼ ψⱼ ψ_{j+|k|}`,
`ψ = θ/φ`, with the recursion 3.3.3 for `ψⱼ`) and the homogeneous-difference-equation method.

All of this rests on the MA(∞) representation and the absolute / mean-square convergence of
`∑ⱼ ψⱼ Zₜ₋ⱼ` (`∑|ψⱼ| < ∞`) — and, for §3.3, the power-series reciprocal `θ/φ`; that analytic
layer is **not yet formalized** (infra-blocked, like the deferred analytic items elsewhere in
the project). The finite `MA(q)` autocovariance `γ(h) = σ² ∑ⱼ θⱼ θ_{j+|h|}` is the one
algebraically-finite special case; it additionally needs the `lagPoly`-as-finite-sum expansion
`(p(B) x) t = ∑ₖ p.coeff k • x (t − k)` and a `q`-fold double-sum covariance computation, and is
deferred with those. The concrete low-order cases — the MA(1) and MA(2) autocovariances — are
proved in `DeepWiki.TimeSeries.ProcessExamples` (`maProcess1`, `maProcess2`). -/

end DeepWiki.Ts
