import DeepWiki.TimeSeries.SampleAutocovariance
import DeepWiki.TimeSeries.SampleMeanVariance
import DeepWiki.TimeSeries.LinearProcessCLT
import DeepWiki.TimeSeries.GeneralLinearProcessCLT
import DeepWiki.TimeSeries.LinearProcessFullCLT
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 7: Estimation of the Mean and the Autocovariance Function
The **estimators** of Chapter 7 are already formalized (the Chapter 1 sample statistics
`sampleMean`, `sampleACVF`, `sampleACF`); their **large-sample distributions** (asymptotic
variance, asymptotic normality, Bartlett's formula) rest on the Chapter 6 time-series central
limit theorem and are infra-blocked. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries
open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## §7.1 Estimation of μ (p.218)
The process mean `μ` is estimated by the sample mean `X̄ₙ = n⁻¹ ∑ₜ Xₜ` (the library's
`sampleMean`). **Theorem 7.1.1** (asymptotic variance `n·Var(X̄ₙ) → ∑ⱼ γ(j)`, `eq_7_1_1`) is now
formalized; **Theorem 7.1.2** (asymptotic normality of `X̄ₙ`) is formalized both for a **finite
`MA(q)`** process (`thm_7_1_2_maq`) and for the **general causal linear process / `MA(∞)`**
`Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}` under `∑ⱼ |ψⱼ|·j < ∞` (`thm_7_1_2_arma`, covering causal ARMA), and — the
complete B&D statement — under the **weak** hypothesis `∑ⱼ |ψⱼ| < ∞` alone (`thm_7_1_2_full`), via a
formalization of Billingsley's double-limit theorem applied to the finite-`MA(m)` truncations. -/

/-- **Theorem 7.1.1 (asymptotic variance of the sample mean)**: for a weakly stationary process with
summable autocovariance `γ`, `n · Var(X̄ₙ) → ∑ⱼ γ(j)` — the rescaled sample-mean variance converges
to the sum of all autocovariances. The library's `tendsto_nsmul_variance_sampleMean`. -/
theorem eq_7_1_1 [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ} (hX : IsWeaklyStationary X μ)
    (hsum : Summable (acvfStat X μ)) :
    Tendsto (fun n : ℕ => (n : ℝ) * variance (fun ω => sampleMean n (fun t => X t ω)) μ) atTop
      (𝓝 (∑' h : ℤ, acvfStat X μ h)) :=
  tendsto_nsmul_variance_sampleMean hX hsum

/-- **Theorem 7.1.2 (asymptotic normality of the sample mean, finite `MA(q)` case)**: for
`Yₜ = μ + ∑_{j=0}^q θⱼ Z_{t−j}` over centered iid `L²` noise `Z`, `√n(Ȳₙ − μ) ⇒ (∑θ) Y₀ =
N(0, (∑θ)² σ²)` — B&D's exact statement for a finite moving average. The library's
`maq_sampleMean_clt_mean` (the iid sample-mean CLT scaled by `∑θ`, with the moving-average
perturbation removed by an `L²`-negligibility bridge; `maq_sampleMean_clt` is the `μ = 0` form). -/
alias thm_7_1_2_maq := DeepWiki.TimeSeries.maq_sampleMean_clt_mean

/-- **Theorem 7.1.2 (asymptotic normality, general causal `MA(∞)` / ARMA case)**: for the causal
linear process `Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}` over centered iid `L²` noise `Z`, with `∑ⱼ |ψⱼ|·j < ∞`
(satisfied by every causal ARMA filter, whose `ψⱼ` decay geometrically), `√n X̄ₙ ⇒ (∑ψ) Y₀ =
N(0, (∑ψ)² σ²)`. The library's `causalLinearProcess_sampleMean_clt` (the iid sample-mean CLT scaled
by `∑ψ`, the `MA(∞)` perturbation removed by an `L²`-negligibility bridge). -/
alias thm_7_1_2_arma := DeepWiki.TimeSeries.causalLinearProcess_sampleMean_clt

/-- **Theorem 7.1.2 (asymptotic normality, full hypothesis `∑ⱼ |ψⱼ| < ∞`)**: for the causal linear
process `Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}` over centered iid `L²` noise, with the **weak** summability
`∑ⱼ |ψⱼ| < ∞` (no `·j` weight), `√n X̄ₙ ⇒ (∑ψ) Y₀ = N(0, (∑ψ)² σ²)`. The complete B&D statement —
the library's `causalLinearProcess_sampleMean_clt_of_summable`, assembled from the finite-`MA(m)`
truncation CLTs through the **double-limit theorem** (`tendstoInDistribution_of_eventually_approx`,
Billingsley Thm 3.2) with a uniform `L²` truncation-error bound. -/
alias thm_7_1_2_full := DeepWiki.TimeSeries.causalLinearProcess_sampleMean_clt_of_summable

/-! ## §7.2 Estimation of γ(·) and ρ(·) (p.220) -/

/-- **§7.2 (eq 7.2.1)**: the sample autocovariance
`γ̂(h) = n⁻¹ ∑_{t < n − h} (x_{t+h} − x̄)(xₜ − x̄)`, the estimator of `γ(·)` — identical to the
Definition 1.5.2 estimator (`def_1_5_2`). The library's `sampleACVF`. -/
noncomputable abbrev eq_7_2_1 := @DeepWiki.TimeSeries.sampleACVF

/-- **§7.2 (eq 7.2.2)**: the sample autocorrelation `ρ̂(h) = γ̂(h) / γ̂(0)`, the estimator of
`ρ(·)`. The library's `sampleACF`. -/
noncomputable abbrev eq_7_2_2 := @DeepWiki.TimeSeries.sampleACF

/-! §7.2 continued: the sample covariance matrix `Γ̂ₙ = [γ̂(i − j)]` (7.2.3) is non-negative
definite — now FORMALIZED (`eq_7_2_3`, the sample analogue of `posSemidef_covMatrix`). The **time-series
central limit theorem** underlying the asymptotic distribution of `γ̂`/`ρ̂` is now FORMALIZED: the
multivariate `m`-dependent CLT (`IsMDependent.tendstoInDistribution_multivariate`) and, on top of it, the
sample-autocovariance-vector CLT `tendstoInDistribution_sampleAutocovVec` — `√n (γ̂(0..k) − γ) ⇒ N(0, S)`
with `S` the long-run covariance matrix of the lag-product process (`longRunCovMatrix`). On top of it,
the **asymptotic normality of the sample autocorrelation** (Theorem 7.2.1's distributional content) is now
FORMALIZED: `tendstoInDistribution_linearCombo_sampleAutocov` (any linear combination
`√n · ∑ᵢ cᵢ (γ̂(i) − γ(i)) ⇒ ⟪V, c⟫`, the projected vector CLT) and the studentized ratio form
`tendstoInDistribution_studentized_linearCombo_sampleAutocov` — for `c = eₕ − ρ(h)·e₀` this is
`√n (ρ̂(h) − ρ(h)) ⇒ N(0, (w ⬝ᵥ S w)/γ(0)²)` (ratio Slutsky on the consistent `γ̂(0) →ᵖ γ(0)`). **Bartlett's
formula** (Theorems 7.2.1 and 7.2.2) — the *explicit* closed form of `w ⬝ᵥ S w` (the `ρ̂` covariance) in
terms of the autocovariance `γ` — is the one remaining analytic step (the fourth-cumulant/Isserlis expansion). -/

/-- **§7.2 (eq 7.2.3): the sample covariance matrix `Γ̂ₙ = [γ̂(i − j)]` is non-negative definite** —
its quadratic form `∑ᵢⱼ aᵢ aⱼ γ̂(|i − j|) ≥ 0` is a sum of squares (`n⁻¹ ∑ₖ (∑ᵢ aᵢ ỹ(k − i))²`). The
library's `sampleACVF_quadratic_nonneg`. -/
theorem eq_7_2_3 (n : ℕ) (x : ℕ → ℝ) (a : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        a i * a j * (if j ≤ i then sampleACVF n x (i - j) else sampleACVF n x (j - i)) :=
  DeepWiki.TimeSeries.sampleACVF_quadratic_nonneg n x a

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§7.2: Theorem 7.2.1 (the *explicit* Bartlett covariance formula `w ⬝ᵥ S w` in terms of `γ`) [research];
Theorem 7.2.2 (Bartlett's formula, general case) [research]
(The CLT blocker and the asymptotic NORMALITY of `γ̂`/`ρ̂` are now RESOLVED: `√n (γ̂(0..k) − γ) ⇒ N(0, S)`
(`tendstoInDistribution_sampleAutocovVec`) and `√n (ρ̂(h) − ρ(h)) ⇒ N(0, (w ⬝ᵥ S w)/γ(0)²)`
(`tendstoInDistribution_studentized_linearCombo_sampleAutocov`, ratio Slutsky on the consistent `γ̂(0)`),
both built on the multivariate `m`-dependent CLT. What remains for 7.2.1/7.2.2 is ONLY the explicit closed
form of the limit covariance `w ⬝ᵥ S w` — Bartlett's `wₕₗ` as a series in the ACVF `γ` — the analytic
fourth-cumulant/Isserlis expansion. The estimators eq 7.2.1/7.2.2 and eq 7.2.3 are done.) -/

end DeepWiki.Ts
