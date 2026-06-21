import DeepWiki.TimeSeries.Periodogram
import DeepWiki.TimeSeries.SpectralDensity
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 10: Inference for the Spectrum of a Stationary Process
The periodogram and the spectral-estimator shapes are algebraic and formalized; their sampling
distributions and the large-sample theory (asymptotic unbiasedness, mean-square consistency,
confidence intervals) rest on the Chapter 6 and §10.3 limit theory and are infra-blocked. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries

/-! ## §10.1 The Periodogram (p.331)
The data `x ∈ ℂⁿ` is expanded in the orthonormal Fourier basis `eⱼ` (Proposition 10.1.1, eq
10.1.4) at the Fourier frequencies `ωⱼ = 2πj/n`, `j ∈ Fₙ` (eq 10.1.5), with coefficients the
discrete Fourier transform `aⱼ = ⟨x, eⱼ⟩ = n^{-1/2} ∑ₜ xₜ e^{-itωⱼ}` (Definition 10.1.1, eq
10.1.7). The **periodogram** is `Iₙ(ωⱼ) = |aⱼ|²` (Definition 10.1.2, eq 10.1.8), and Parseval's
identity gives the analysis of variance `‖x‖² = ∑_{j∈Fₙ} Iₙ(ωⱼ)` (eq 10.1.9). The orthonormality
(**Proposition 10.1.1**) and the analysis of variance (**eq 10.1.9**) are now FORMALIZED — pure
linear algebra over the discrete Fourier basis, built on the root-of-unity orthogonality
`sum_range_exp_two_pi_mul_I`. -/

/-- **§10.1 (Definition 10.1.2, eq 10.1.8)**: the **periodogram** `Iₙ(λ) = n⁻¹ |∑ₜ xₜ e^{-itλ}|²`,
the squared modulus of the discrete Fourier transform of the data normalized by `n` — the basic
nonparametric spectral estimator (non-negative, `periodogram_nonneg`; `Iₙ(0) = n⁻¹(∑ₜxₜ)²`,
`periodogram_zero_eq`). The library's `periodogram`. -/
noncomputable abbrev def_10_1_2 := @DeepWiki.TimeSeries.periodogram

/-- **Proposition 10.1.1 (eq 10.1.4)**: the Fourier vectors `eⱼ(t) = n^{−1/2} e^{itωⱼ}`
(`ωⱼ = 2πj/n`) are orthonormal — `⟨eⱼ, eₖ⟩ = n⁻¹ ∑_{t<n} e^{it(ωⱼ−ωₖ)}` is `1` when `n ∣ (j−k)` and
`0` otherwise. The library's `fourier_inner_eq`. -/
theorem prop_10_1_1 (n : ℕ) (hn : 0 < n) (j k : ℤ) :
    (∑ t ∈ Finset.range n,
        Complex.exp (2 * Real.pi * Complex.I * ((j - k : ℤ) : ℂ) * t / n)) / n
      = if (n : ℤ) ∣ (j - k) then 1 else 0 :=
  DeepWiki.TimeSeries.fourier_inner_eq n hn j k

/-- **§10.1 (eq 10.1.9, analysis of variance / Parseval)**: the periodogram ordinates at the Fourier
frequencies sum to the total sum of squares — `∑_{j<n} Iₙ(2πj/n) = ∑_{t<n} xₜ²`. The library's
`periodogram_sum_eq`. -/
theorem eq_10_1_9 (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ) :
    ∑ j ∈ Finset.range n, periodogram n x (2 * Real.pi * j / n) = ∑ t ∈ Finset.range n, (x t) ^ 2 :=
  DeepWiki.TimeSeries.periodogram_sum_eq n hn x

/-! ## §10.2 Testing for the Presence of Hidden Periodicities (p.336)
Fisher's test and related procedures detect a deterministic periodic component by comparing the
largest periodogram ordinates with the rest; their null distributions (the order statistics `Mₖ`,
Proposition 10.2.1, Corollaries 10.2.1 and 10.2.2) are distribution theory and are infra-blocked. -/

/-! ## §10.3 Asymptotic Properties of the Periodogram (p.343)
The periodogram is extended to every `ω ∈ [−π, π]` (Definition 10.3.1) and shown to be
asymptotically unbiased for `2πf(ω)` — `E Iₙ(ω) → 2πf(ω)` (Proposition 10.3.1) — but **not**
consistent. These limit results are infra-blocked. -/

/-! ## §10.4 Smoothing the Periodogram (p.353)
A consistent estimator is obtained by smoothing: the **discrete spectral average estimator**
`f̂(λ) = (2π)⁻¹ ∑_{|k|≤mₙ} Wₙ(k) Iₙ(λ + 2πk/n)` (eq 10.4.7) with a weight function `Wₙ`. Its
mean-square consistency (Theorems 10.4.1 and 10.4.2) is infra-blocked (asymptotics). -/

/-! ## §10.5 Confidence Intervals for the Spectrum (p.363)
Confidence intervals for `f(ω)` (and simultaneous intervals over several frequencies) are built
from the asymptotic chi-squared and normal distributions of the smoothed estimator (eq 10.5.4);
infra-blocked. -/

/-! ## §10.6 Rational Spectral Density Estimators (p.367)
A parametric estimator substitutes maximum-likelihood ARMA estimates into the ARMA spectral
density: `f̂(λ) = σ̂²/(2π) · |θ̂(e^{-iλ})|² / |φ̂(e^{-iλ})|²` (eq 10.6.4) — exactly the library's
`armaSpectralDensity` (Theorem 4.4.2) evaluated at the estimated coefficients. The plug-in is
algebraic; its sampling properties are infra-blocked. -/

/-- **§10.6 (eq 10.6.4, the rational spectral density estimator)**: the maximum-likelihood plug-in
`f̂(λ) = σ̂²/(2π) · |θ̂(e^{-iλ})|² / |φ̂(e^{-iλ})|²` is the `armaSpectralDensity` formula (eq 4.4.5,
Theorem 4.4.2) evaluated at the estimated coefficients `φ̂, θ̂, σ̂²`. The library's
`armaSpectralDensity`. -/
noncomputable abbrev eq_10_6_4 := @DeepWiki.TimeSeries.armaSpectralDensity

/-! ## §10.7 The Fast Fourier Transform (FFT) Algorithm (p.373)
The Cooley–Tukey FFT computes the discrete Fourier transform in `O(n log n)` operations by
recursively factoring `n = rs` (eq 10.7.1) — an algorithm, not a theorem; not formalized. -/

/-! ## §10.8 Asymptotic Behavior of the Maximum Likelihood Estimators (p.381)
The starred section derives the asymptotic normality of the maximum-likelihood and least-squares
ARMA estimators (deferred from Chapter 8) via a Gram–Schmidt (Cholesky) factorization of the
covariance matrix (eq 10.8.18); infra-blocked. -/

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§10.1: Definition 10.1.1 (the discrete Fourier transform coefficients `aⱼ = ⟨x, eⱼ⟩` as a named
object, with the Fourier basis `eⱼ` and frequency set `Fₙ`) [deferred]
§10.2: Proposition 10.2.1 (null distribution of the order statistics `Mₖ`) [infra]; Corollary 10.2.1
[infra]; Corollary 10.2.2 [infra]; Fisher's test for hidden periodicities [infra]
§10.3: Definition 10.3.1 (periodogram extended to all `ω ∈ [−π, π]`) [deferred]; Proposition 10.3.1
(asymptotic unbiasedness `E Iₙ(ω) → 2πf(ω)`) [infra]; the inconsistency of the periodogram [infra]
§10.4: equation 10.4.7 (the discrete spectral average estimator `f̂`) [deferred]; Theorem 10.4.1
(mean-square consistency) [infra]; Theorem 10.4.2 [infra]
§10.5: equation 10.5.4 (confidence intervals for `f(ω)`) [infra]; simultaneous confidence intervals
over several frequencies [infra]
§10.6: the sampling properties of the plug-in rational estimator `f̂` [infra]
§10.7: the Cooley–Tukey FFT algorithm (eq 10.7.1, recursive `n = rs` factoring) [deferred]
§10.8: equation 10.8.18 (the Gram–Schmidt/Cholesky covariance factorization) [deferred]; asymptotic
normality of the ML and least-squares ARMA estimators [infra]
(§10.1 orthogonality / Prop 10.1.1 / Parseval eq 10.1.9 and the §10.6 estimator formula eq 10.6.4 are
done. Dominant blocker for the rest: large-sample limit theory — periodogram sampling distributions,
smoothed-estimator consistency, confidence intervals; §10.7 is a procedural algorithm.) -/

end DeepWiki.Ts
