import DeepWiki.TimeSeries.MultivariateTimeSeries
import DeepWiki.TimeSeries.MultivariateArma
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 11: Multivariate Time Series
The second-order structure of a vector process — its mean vector and covariance matrix function —
is algebraic and formalized (the matrix analogue of the Chapter 1 autocovariance); the estimation
theory, multivariate ARMA prediction recursions, and spectral analysis rest on matrix extensions
of the earlier limit theory and are infra-blocked. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries

/-! ## §11.1 Second Order Properties of Multivariate Time Series (p.402)
An `m`-variate process `{Xₜ}` has a **mean vector** `μ = EXₜ` (eq 11.1.4) and a **covariance
matrix function** `Γ(t+h, t) = E[(X_{t+h} − μ)(Xₜ − μ)'] = [γᵢⱼ(t+h, t)]` (eq 11.1.5), the entries
being the component cross-covariances `γᵢⱼ = Cov(X_{t+h,i}, X_{t,j})`. For a stationary multivariate
series (Definition 11.1.1) these are independent of `t`, giving `μ` and `Γ(h)`. -/

/-- **§11.1 (eq 11.1.4)**: the **mean vector** `μ = E Xₜ = [E X_{t,i}]ᵢ` of a `d`-variate process.
The library's `mvMean`. -/
noncomputable abbrev eq_11_1_4 := @DeepWiki.TimeSeries.mvMean

/-- **Definition 11.1.1 (multivariate weak stationarity)**: each component square-integrable, the
mean vector constant in `t`, and the cross-covariances invariant under a common shift (`Γ(t+h,t) =
Γ(h)`). The library's `IsMultivariateStationary` (each component is univariately weakly stationary,
`IsMultivariateStationary.component`). -/
def def_11_1_1 := @DeepWiki.TimeSeries.IsMultivariateStationary

/-- **§11.1 (eq 11.1.5)**: the **covariance matrix function** `Γ(h) = [Cov(X_{h,i}, X_{0,j})]ᵢⱼ`
of a stationary `d`-variate process — the matrix analogue of the univariate autocovariance, with
diagonal the componentwise `acvf` (`mvACVF_diag`) and `Γ(0)` symmetric (`mvACVF_zero_isSymm`).
The library's `mvACVF`. -/
noncomputable abbrev eq_11_1_5 := @DeepWiki.TimeSeries.mvACVF

/-! ## §11.2 Estimation of the Mean and Covariance Function (p.413)
The mean vector and covariance matrix function are estimated by their sample analogues; the
asymptotic distribution of the sample cross-correlations `ρ̂ᵢⱼ(h)` (Theorems 11.2.1 and 11.2.2)
is infra-blocked (multivariate central limit theory). -/

/-! ## §11.3 Multivariate ARMA Processes (p.417)
The vector ARMA(p,q) process `Xₜ − Φ₁X_{t-1} − ⋯ = Zₜ + Θ₁Z_{t-1} + ⋯` with matrix coefficients,
and the **causality criterion** `det Φ(z) ≠ 0 for |z| ≤ 1` (Theorem 11.3.1) — the matrix analogue
of the Chapter 3 condition. The algebra is tractable; the spectral and limit theory is
infra-blocked. -/

/-- **§11.3 — the vector `ARMA(p, q)` process**: the matrix lag-polynomial recursion
`Xₜ − Φ₁Xₜ₋₁ − ⋯ − ΦₚXₜ₋ₚ = Zₜ + Θ₁Zₜ₋₁ + ⋯ + Θ_qZₜ₋q` (`Φ(B)Xₜ = Θ(B)Zₜ`), with matrix AR/MA
coefficients. The library's `IsVectorARMA` (the recursion; white-noise input and stationarity are
supplied as separate hypotheses, with `isVectorARMA_zero`: an `ARMA(0,0)` process is its input). -/
abbrev def_11_3_vectorARMA := @DeepWiki.TimeSeries.IsVectorARMA

/-! ## §11.4 Best Linear Predictors of Second Order Random Vectors (p.427)
The multivariate innovations algorithm computes the one-step predictors `X̂ₙ₊₁` and their error
covariance matrices (eq 11.4.27 and 11.4.28) — the vector generalization of the §5.2 innovations
recursion; its correctness via projection onto the predictor subspace is deferred. -/

/-! ## §11.5 Estimation for Multivariate ARMA Processes (p.430)
Maximum-likelihood estimation maximizes the Gaussian likelihood `L(Φ, Θ, Σ)` (eq 11.5.4),
computed via the innovations algorithm; infra-blocked (optimization and asymptotics). -/

/-! ## §11.6 The Cross Spectrum (p.434)
The **spectral density matrix** `f(λ) = (2π)⁻¹ ∑ₕ e^(−ihλ) Γ(h) = [fᵢⱼ(λ)]` (eq 11.6.4), the
**cross spectrum** `f₁₂` (Definition 11.6.1), and the derived squared coherency and phase
spectrum — the matrix analogue of the Chapter 4 spectral density. Its analytic theory is
infra-blocked. -/

/-! ## §11.7 Estimating the Cross Spectrum (p.446)
The smoothed cross-spectral estimates `f̂ᵢⱼ` (from the bivariate periodogram), and the resulting
estimates of the cross-amplitude and phase spectra, with their asymptotic distributions (Theorem
11.7.1); infra-blocked. -/

/-! ## §11.8 The Spectral Representation of a Multivariate Stationary Time Series (p.455)
The multivariate spectral representation `Xₜ = ∫ e^(itλ) dZ(λ)` via an orthogonal-increment
process `Z` with `E(dZ(λ) dZ(λ)*) = dF(λ)` (Definition 11.8.1) — the vector analogue of the
Chapter 4 spectral representation; the stochastic-integral construction is infra-blocked. -/

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§11.2: Theorem 11.2.1 (asymptotic distribution of the sample cross-correlations `ρ̂ᵢⱼ(h)`) [infra];
Theorem 11.2.2 [infra]
§11.3: Theorem 11.3.1 (vector-ARMA causality criterion `det Φ(z) ≠ 0` for `|z| ≤ 1`) [deferred]
§11.4: the multivariate innovations one-step predictors `X̂ₙ₊₁` (eq 11.4.27) [infra]; their error
covariance matrices (eq 11.4.28) [infra]
§11.5: the Gaussian likelihood `L(Φ, Θ, Σ)` for multivariate ARMA ML estimation (eq 11.5.4) [infra]
§11.6: the spectral density matrix `f(λ)` (eq 11.6.4) [infra]; Definition 11.6.1 (the cross spectrum
`f₁₂`) [infra]; the squared coherency [infra]; the phase spectrum [infra]
§11.7: the smoothed cross-spectral estimates `f̂ᵢⱼ` [infra]; the cross-amplitude and phase-spectrum
estimates with their asymptotic distributions (Theorem 11.7.1) [infra]
§11.8: Definition 11.8.1 (the multivariate spectral representation `Xₜ = ∫ e^{itλ} dZ(λ)`) [infra]
(The stationary second-order matrix algebra `Γ(h)` (eq 11.1.5) is done; the rest needs matrix
extensions of the limit/spectral theory and L² stochastic integration.) -/

end DeepWiki.Ts
