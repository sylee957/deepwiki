import DeepWiki.TimeSeries.SampleAutocovariance
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 7: Estimation of the Mean and the Autocovariance Function
The **estimators** of Chapter 7 are already formalized (the Chapter 1 sample statistics
`sampleMean`, `sampleACVF`, `sampleACF`); their **large-sample distributions** (asymptotic
variance, asymptotic normality, Bartlett's formula) rest on the Chapter 6 time-series central
limit theorem and are infra-blocked. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries

/-! ## §7.1 Estimation of μ (p.218)
The process mean `μ` is estimated by the sample mean `X̄ₙ = n⁻¹ ∑ₜ Xₜ` (the library's
`sampleMean`). **Theorems 7.1.1 and 7.1.2** (its asymptotic variance `n·Var(X̄ₙ) → ∑ⱼ γ(j)` and
asymptotic normality) are infra-blocked — they need the time-series central limit theorem
(§6.4). -/

/-! ## §7.2 Estimation of γ(·) and ρ(·) (p.220) -/

/-- **§7.2 (eq 7.2.1)**: the sample autocovariance
`γ̂(h) = n⁻¹ ∑_{t < n − h} (x_{t+h} − x̄)(xₜ − x̄)`, the estimator of `γ(·)` — identical to the
Definition 1.5.2 estimator (`def_1_5_2`). The library's `sampleACVF`. -/
noncomputable abbrev eq_7_2_1 := @DeepWiki.TimeSeries.sampleACVF

/-- **§7.2 (eq 7.2.2)**: the sample autocorrelation `ρ̂(h) = γ̂(h) / γ̂(0)`, the estimator of
`ρ(·)`. The library's `sampleACF`. -/
noncomputable abbrev eq_7_2_2 := @DeepWiki.TimeSeries.sampleACF

/-! §7.2 continued: the sample covariance matrix `Γ̂ₙ = [γ̂(i − j)]` (7.2.3) is non-negative
definite — now FORMALIZED (`eq_7_2_3`, the sample analogue of `posSemidef_covMatrix`); the asymptotic
distribution of `ρ̂` — **Bartlett's formula** (Theorems 7.2.1 and 7.2.2) — is infra-blocked
(time-series central limit theorem). -/

/-- **§7.2 (eq 7.2.3): the sample covariance matrix `Γ̂ₙ = [γ̂(i − j)]` is non-negative definite** —
its quadratic form `∑ᵢⱼ aᵢ aⱼ γ̂(|i − j|) ≥ 0` is a sum of squares (`n⁻¹ ∑ₖ (∑ᵢ aᵢ ỹ(k − i))²`). The
library's `sampleACVF_quadratic_nonneg`. -/
theorem eq_7_2_3 (n : ℕ) (x : ℕ → ℝ) (a : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        a i * a j * (if j ≤ i then sampleACVF n x (i - j) else sampleACVF n x (j - i)) :=
  DeepWiki.TimeSeries.sampleACVF_quadratic_nonneg n x a

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§7.1: Theorem 7.1.1 (asymptotic variance of the sample mean, `n·Var(X̄ₙ) → ∑ⱼ γ(j)`) [infra]; Theorem
7.1.2 (asymptotic normality of the sample mean) [infra]
§7.2: Theorem 7.2.1 (asymptotic distribution of `ρ̂`, Bartlett's formula) [infra]; Theorem 7.2.2
(Bartlett's formula, general case) [infra]
(Dominant blocker: the time-series central limit theorem of §6.4. The estimators eq 7.2.1/7.2.2 and
the sample-covariance-matrix non-negative-definiteness eq 7.2.3 are done.) -/

end DeepWiki.Ts
