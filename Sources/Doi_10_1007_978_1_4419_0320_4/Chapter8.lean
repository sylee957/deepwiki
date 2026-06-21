import DeepWiki.TimeSeries.YuleWalker
import DeepWiki.TimeSeries.CausalArmaAcvf
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 8: Estimation for ARMA Models
The parameter estimators of Chapter 8 have largely algebraic definitions; their justification and
large-sample theory (consistency, asymptotic normality, efficiency) rest on the Chapter 6
time-series limit theorems and are infra-blocked. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries
open scoped Polynomial

/-! ## §8.1 The Yule–Walker Equations and AR Estimation (p.239)
For a causal AR(p) the population coefficients solve the **Yule–Walker equations** `Γₚ φ = γₚ`
(8.1.4) — these are the §5.1 prediction equations — with `σ² = γ(0) − φ'γₚ` (8.1.5). Replacing the
autocovariances by their sample estimates (`sampleACVF`, Chapter 7) gives the **Yule–Walker
estimator** `φ̂ = Γ̂ₚ⁻¹ γ̂ₚ` (8.1.6), `σ̂² = γ̂(0) − φ̂'γ̂ₚ` (8.1.7). **Theorem 8.1.1** (asymptotic
normality of `φ̂`) is infra-blocked (time-series central limit theorem). -/

/-- **§8.1 (eq 8.1.6)**: the **Yule–Walker estimator** `φ̂ = Γ̂⁻¹ γ̂` of the autoregressive
coefficients — the solution of the sample normal equations `Γ̂ φ̂ = γ̂` (`yuleWalkerEstimator_spec`).
The library's `yuleWalkerEstimator`. -/
noncomputable abbrev eq_8_1_6 := @DeepWiki.TimeSeries.yuleWalkerEstimator

/-- **§8.1 (eq 8.1.4, the Yule–Walker equations)**: for a causal `AR(p)` the autocovariance
`γ(h) = σ² ∑ⱼ ψⱼ ψ_{j+h}` satisfies the homogeneous recursion `∑_{k=0}^p φₖ γ(h−k) = 0` for every
`h ≥ 1` — equivalently the linear system `Γₚ φ = γₚ` that the autoregressive coefficients solve.
Specializes the causal-`ARMA` autocovariance recursion `causal_arma_acvf_homogeneous` to `θ = 1`
(so `q = deg θ = 0`, and the recursion holds for all lags `h > 0`). -/
theorem eq_8_1_4 {φ : ℝ[X]} (hφ : IsCausalPoly φ) (σ2 : ℝ) {h : ℤ} (hh : 0 < h) :
    ∃ ψ : ℤ → ℝ, Summable ψ ∧ (∀ j : ℤ, j < 0 → ψ j = 0) ∧
      ∑ k ∈ Finset.range (φ.natDegree + 1),
        φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + (h - k))) = 0 :=
  causal_arma_acvf_homogeneous (θ := 1) hφ σ2 (by simpa using hh)

/-! ## §8.2+ Further estimators (infra-blocked asymptotics)
The remaining sections develop more efficient estimators — Burg's algorithm, the
innovations-algorithm preliminary estimators for MA(q) and ARMA(p,q) (built on Proposition 5.2.2),
the Hannan–Rissanen procedure, maximum-likelihood and least-squares estimation, and order
selection by the AIC and AICC criteria. The estimating equations are algebraic, but the
efficiency, consistency, and asymptotic-normality results that motivate and justify them depend
on the time-series central limit theorem (Chapter 6) and are infra-blocked. -/

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§8.1: `σ² = γ(0) − φ'γₚ` (eq 8.1.5)
[deferred]; the Yule–Walker variance estimate `σ̂² = γ̂(0) − φ̂'γ̂ₚ` (eq 8.1.7) [deferred]; Theorem 8.1.1
(asymptotic normality of `φ̂`) [infra]
§8.2: Burg's algorithm [deferred]
§8.3: the innovations-algorithm preliminary estimators for `MA(q)` and `ARMA(p,q)` [deferred]; the
Hannan–Rissanen procedure [deferred]
§8.4–§8.6: maximum-likelihood estimation [infra]; least-squares estimation [infra]; order selection by
the AIC criterion [infra]; order selection by the AICC criterion [infra]
(The Yule–Walker estimator eq 8.1.6 is done; the estimating equations/algorithms are algebraic
[deferred] but their consistency/efficiency/asymptotic-normality rest on the Chapter 6 central limit
theorem [infra].) -/

end DeepWiki.Ts
