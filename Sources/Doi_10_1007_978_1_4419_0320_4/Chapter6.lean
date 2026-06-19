import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 6: Asymptotic Theory (structure map)

Chapter 6 (starred in the book) develops the probabilistic limit theory used for large-sample
inference. It is almost entirely **infra-blocked** in this Mathlib: the general convergence modes
have Mathlib counterparts, but the time-series limit theorems (laws of large numbers and central
limit theorems for dependent and linear processes, the delta method for time series) are not
available. This file is a book↔lib structure map; no Chapter 6 theorem is formalized.

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
  linear processes. Mathlib has the classical i.i.d. central limit theorem; the dependent and
  linear-process CLT — the engine behind the asymptotic normality of the sample mean and sample
  autocovariance (Chapter 7) and of the ARMA estimators (Chapter 8) — is infra-blocked.
-/

namespace DeepWiki.Ts

end DeepWiki.Ts
