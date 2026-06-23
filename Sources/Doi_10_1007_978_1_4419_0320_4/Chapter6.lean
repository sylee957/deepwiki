import DeepWiki.TimeSeries.LinearProcessFullCLT
import DeepWiki.TimeSeries.DeltaMethod
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 6: Asymptotic Theory (structure map)

Chapter 6 (starred in the book) develops the probabilistic limit theory used for large-sample
inference. It is almost entirely **infra-blocked** in this Mathlib: the general convergence modes
have Mathlib counterparts, but the time-series limit theorems (laws of large numbers and central
limit theorems for dependent and linear processes, the delta method for time series) are not
available. This file is largely a book↔lib structure map; the **central limit theorem for (causal)
linear processes** (§6.4) is now formalized (`clt_linearProcess`), the rest stays infra-blocked.

- **§6.1 Convergence in Probability** (p.198): `Xₙ →ᵖ X` (Definition 6.1.1), the `Oₚ` and `oₚ`
  order notation (Definition 6.1.4), and Slutsky-type results. Mathlib has convergence in
  measure (`MeasureTheory.TendstoInMeasure`); the `Oₚ` and `oₚ` calculus is not packaged.
- **§6.2 Convergence in rᵗʰ Mean** (p.203): `Lʳ` convergence, Chebyshev's inequality (6.2.1) and
  mean-square convergence. Mathlib has the `Lᵖ` spaces and Chebyshev and Markov bounds; the named
  `r`-th-mean convergence predicate is spelled as `eLpNorm (Xₙ − X) r μ → 0`.
- **§6.3 Convergence in Distribution** (p.~206): weak convergence, plus the **weak law of large
  numbers for moving averages** (Proposition 6.3.2, `n⁻¹ ∑ₜ Xₜ →ᵖ μ` for a summable linear
  process). Mathlib has weak convergence of measures; the moving-average WLLN is infra-blocked.
- **§6.4 The Central Limit Theorem and Related Results** (p.~211): the delta method (Example
  6.4.2), `m`-dependence (Definition 6.4.3), and the central limit theorem for `m`-dependent and
  linear processes. Mathlib has the classical i.i.d. central limit theorem; the **linear-process
  CLT** is now formalized (`clt_linearProcess`, causal case under `∑|ψⱼ|<∞`, built from the
  finite-`MA(m)` CLTs via a formalization of Billingsley's double-limit theorem) — the engine
  behind the asymptotic normality of the Chapter 7 sample mean; the general `m`-dependent CLT and
  the delta method stay infra-blocked.
-/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries

/-- **§6.4 — Central limit theorem for (causal) linear processes**: for `Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}`
over centered iid `L²` noise with `∑ⱼ |ψⱼ| < ∞`, the standardized sample mean is asymptotically
normal, `√n X̄ₙ ⇒ (∑ψ) Y₀ = N(0, (∑ψ)² σ²)` — the §6.4 limit engine behind the asymptotic normality
of the Chapter 7 estimators. The library's `causalLinearProcess_sampleMean_clt_of_summable`,
assembled from the finite-`MA(m)` truncation CLTs through the double-limit theorem; applied in
§7.1.2 (`thm_7_1_2_full`). -/
alias clt_linearProcess := DeepWiki.TimeSeries.causalLinearProcess_sampleMean_clt_of_summable

/-- **§6.4 Example 6.4.2 — the (one-dimensional) delta method**: if `Xₙ →ᵖ a`, the standardized
`√n (Xₙ − a)` converges in distribution to `Y₀`, and `g` is differentiable at `a`, then
`√n (g Xₙ − g a) ⇒ g'(a) · Y₀` (so for `Y₀ ~ N(0, σ²)`, the limit is `N(0, g'(a)² σ²)`). The
library's `delta_method` — the asymptotic-normality transfer for smooth functionals, the §6.4 tool
behind the sample-autocorrelation limit theory (Bartlett, §7.2). -/
alias example_6_4_2 := DeepWiki.TimeSeries.delta_method

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§6.1: Definition 6.1.1 (convergence in probability `Xₙ →ᵖ X`) [infra]; Definition 6.1.4 (`Oₚ`/`oₚ`
order notation) [infra]; Slutsky's theorem [infra]
§6.2: Chebyshev's inequality (eq 6.2.1) [infra]; convergence in `rᵗʰ` mean [infra]
§6.3: Proposition 6.3.2 (weak law of large numbers for moving averages, `n⁻¹ ∑ₜ Xₜ →ᵖ μ`) [infra]
§6.4: Definition 6.4.3 (`m`-dependence) [infra]; the central limit theorem for general `m`-dependent
processes [infra] (the linear-process CLT `clt_linearProcess` and the delta method `example_6_4_2`
are done)
(Dominant blocker for the remaining items: the general dependent-process large-sample theory. The
linear-process CLT — the main §6.4 engine for Chapter 7 — is now formalized via the double-limit
theorem; the multivariate iid CLT `multivariate_iid_clt` is also available for Bartlett's formula.) -/

end DeepWiki.Ts
