import DeepWiki.TimeSeries.LinearProcessFullCLT
import DeepWiki.TimeSeries.DeltaMethod
import DeepWiki.TimeSeries.MDependence
import DeepWiki.TimeSeries.MDependentCLT
import DeepWiki.TimeSeries.MovingAverageMDependent
import DeepWiki.TimeSeries.StochasticOrder
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 6: Asymptotic Theory (structure map)

Chapter 6 (starred in the book) develops the probabilistic limit theory used for large-sample
inference. It is almost entirely **infra-blocked** in this Mathlib: the general convergence modes
have Mathlib counterparts, but the time-series limit theorems (laws of large numbers and central
limit theorems for dependent and linear processes, the delta method for time series) are not
available. This file is largely a book↔lib structure map; the **central limit theorem for (causal)
linear processes** (§6.4) is now formalized (`clt_linearProcess`), the rest stays infra-blocked.

- **§6.1 Convergence in Probability** (p.198): `Xₙ →ᵖ X` (Definition 6.1.1, = Mathlib's
  `MeasureTheory.TendstoInMeasure`, cataloged `def_6_1_1`), the `Oₚ` and `oₚ` order notation
  (Definition 6.1.4), and Slutsky-type results. Mathlib has **Slutsky's theorem** itself
  (`TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, with the additive form
  `add_of_tendstoInMeasure_const`); the **ratio form** is DeepWiki's `slutsky_ratio`. The `Oₚ`/`oₚ`
  calculus is not packaged.
- **§6.2 Convergence in rᵗʰ Mean** (p.203): `Lʳ` convergence, Chebyshev's inequality (6.2.1) and
  mean-square convergence. Mathlib has `Lᵖ` spaces, **Chebyshev** (`ProbabilityTheory.meas_ge_le_variance_div_sq`,
  cataloged `eq_6_2_1`) and **Markov** (`meas_ge_le_mul_pow_eLpNorm_enorm`) bounds; `rᵗʰ`-mean
  convergence is spelled `eLpNorm (Xₙ − X) r μ → 0`, and `rᵗʰ`-mean `⇒` in probability is Mathlib's
  `tendstoInMeasure_of_tendsto_eLpNorm` (used in `prop_6_3_2`).
- **§6.3 Convergence in Distribution** (p.~206): weak convergence, plus the **weak law of large
  numbers for moving averages** (Proposition 6.3.2, `n⁻¹ ∑ₜ Xₜ →ᵖ 0` for a summable causal linear
  process) — now formalized (`prop_6_3_2`), from the `L²` bound `‖√n X̄ₙ‖₂ ≤ C` so `‖X̄ₙ‖₂ → 0`.
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

/-- **§6.1 Slutsky's theorem, ratio form**: if `Xₙ ⇒ X` and `Yₙ →ᵖ b ≠ 0`, then `Xₙ / Yₙ ⇒ X / b`.
The library's `tendstoInDistribution_div_of_tendstoInMeasure_const` — the divisive companion of
Mathlib's `TendstoInDistribution.prodMk_of_tendstoInMeasure_const` (Slutsky's theorem proper, the
joint form) and `add_of_tendstoInMeasure_const` (additive form); the inference tool behind the
sample-autocorrelation limit `ρ̂(h) = γ̂(h)/γ̂(0)` of Bartlett's formula (§7.2). -/
alias slutsky_ratio := DeepWiki.TimeSeries.tendstoInDistribution_div_of_tendstoInMeasure_const

/-- **§6.1 Definition 6.1.1 — convergence in probability**: `Xₙ →ᵖ X` iff `μ{|Xₙ − X| ≥ ε} → 0` for
every `ε > 0`. Mathlib's `MeasureTheory.TendstoInMeasure` (the convergence mode underlying the §6.3
weak law `prop_6_3_2`, the §6.4 delta method `example_6_4_2`, and Slutsky `slutsky_ratio`). -/
abbrev def_6_1_1 := @MeasureTheory.TendstoInMeasure

/-- **§6.1 Definition 6.1.4 — the `oₚ`/`Oₚ` stochastic order notation**: `Xₙ = oₚ(rₙ)` when
`Xₙ/rₙ → 0` in probability (`IsLittleOp`, with `oₚ(1) ↔ →ᵖ 0` via `isLittleOp_one_iff`), and
`Xₙ = Oₚ(rₙ)` when `Xₙ/rₙ` is bounded in probability (`IsBigOp`). The library's `IsLittleOp`
(its `Oₚ` companion is `DeepWiki.TimeSeries.IsBigOp`) — the asymptotic-order calculus for random
sequences, not present in Mathlib. -/
abbrev def_6_1_4 := @DeepWiki.TimeSeries.IsLittleOp

/-- **§6.2 Chebyshev's inequality (eq 6.2.1)**: `μ{|X − E X| ≥ c} ≤ Var X / c²` for an `L²` random
variable. Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq` — the basic deviation bound behind
mean-square convergence and the §6.3 weak law (`prop_6_3_2`). -/
alias eq_6_2_1 := ProbabilityTheory.meas_ge_le_variance_div_sq

/-- **§6.4 — Central limit theorem for (causal) linear processes**: for `Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}`
over centered iid `L²` noise with `∑ⱼ |ψⱼ| < ∞`, the standardized sample mean is asymptotically
normal, `√n X̄ₙ ⇒ (∑ψ) Y₀ = N(0, (∑ψ)² σ²)` — the §6.4 limit engine behind the asymptotic normality
of the Chapter 7 estimators. The library's `causalLinearProcess_sampleMean_clt_of_summable`,
assembled from the finite-`MA(m)` truncation CLTs through the double-limit theorem; applied in
§7.1.2 (`thm_7_1_2_full`). -/
alias clt_linearProcess := DeepWiki.TimeSeries.causalLinearProcess_sampleMean_clt_of_summable

/-- **§6.3 Proposition 6.3.2 — weak law of large numbers for the (causal) moving-average process**:
for `Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}` over centered iid `L²` noise with `∑ⱼ |ψⱼ| < ∞`, the sample mean
converges to `0` in probability, `X̄ₙ →ᵖ 0`. The library's `causalLinearProcess_sampleMean_wlln`,
obtained from the `L²` bound `‖√n X̄ₙ‖₂ ≤ C` (so `‖X̄ₙ‖₂ ≤ C/√n → 0`) via `L² ⇒` convergence in
measure. -/
alias prop_6_3_2 := DeepWiki.TimeSeries.causalLinearProcess_sampleMean_wlln

/-- **§6.4 Proposition 6.4.1 — the (one-dimensional) delta method**: if `Xₙ →ᵖ a`, the standardized
`√n (Xₙ − a)` converges in distribution to `Y₀`, and `g` is differentiable at `a`, then
`√n (g Xₙ − g a) ⇒ g'(a) · Y₀` (so for `Y₀ ~ N(0, σ²)`, the limit is `N(0, g'(a)² σ²)`). The
library's `delta_method` — the asymptotic-normality transfer for smooth functionals, the §6.4 tool
behind the sample-autocorrelation limit theory (Bartlett, §7.2). -/
alias prop_6_4_1 := DeepWiki.TimeSeries.delta_method

/-- **§6.4 Definition 6.4.3 — m-dependence**: a process `X` is `m`-dependent if any two finite blocks
separated by more than `m` time steps are independent. The library's `IsMDependent` (with its
monotonicity `IsMDependent.mono`, and the canonical example `isMDependent_of_iIndepFun`: an i.i.d.
sequence is `m`-dependent for every `m`, being `0`-dependent); the hypothesis of the §6.4 central
limit theorem for dependent processes. -/
abbrev def_6_4_3 := @DeepWiki.TimeSeries.IsMDependent

/-- **§6.4 Theorem 6.4.2 — the central limit theorem for strictly stationary `m`-dependent sequences**:
for centered `L²` strictly-stationary `m`-dependent `{Xₜ}` with `vₘ = γ(0) + 2∑_{j=1}^m γ(j) = ∑_{|h|≤m} γ(h)`,
the standardized sample mean `√n X̄ₙ` is `AN(0, vₘ)`, i.e. `√n X̄ₙ ⇒ N(0, vₘ)`. The library's
`IsMDependent.tendstoInDistribution_sqrt_sampleMean` (part (ii); the limit `√vₘ · G` for a standard
normal `G`), proved by Bernstein's big-block/small-block method. Part (i), `n · Var(X̄ₙ) → vₘ`, is
`tendsto_nsmul_variance_sampleMean_of_mDependent`. -/
alias thm_6_4_2 := DeepWiki.TimeSeries.IsMDependent.tendstoInDistribution_sqrt_sampleMean

/-- **§6.4 Theorem 6.4.2(i) — the limiting variance**: `n · Var(X̄ₙ) → vₘ = ∑_{|h| ≤ m} γ(h)` for a
strictly stationary `m`-dependent (indeed any summable-acvf weakly stationary) sequence. The library's
`tendsto_nsmul_variance_sampleMean_of_mDependent`. -/
alias thm_6_4_2_i := DeepWiki.TimeSeries.tendsto_nsmul_variance_sampleMean_of_mDependent

/-- **§6.4 Example 6.4.3 — a moving average is m-dependent**: the MA(q) process `Xₜ = ∑_{j=0}^q θⱼ Z_{t−j}`
over i.i.d. noise is `q`-dependent (Example 6.4.3 is the case `q = 1`, `Xₜ = Zₜ − Zₜ₋₁`). The library's
`isMDependent_movingAverage` (blocks separated by `> q` depend on disjoint noise windows); with the
structural lemmas `measurable_movingAverage`/`memLp_movingAverage`/`integral_movingAverage` this readies
`movingAverage` for the `m`-dependent CLT `thm_6_4_2`. -/
alias example_6_4_3 := DeepWiki.TimeSeries.isMDependent_movingAverage

/-- **§6.4 Example 6.4.4 — asymptotic normality of the moving-average sample mean**: for an MA(q) process
`Xₜ = ∑_{j=0}^q θⱼ Z_{t−j}` over centered `L²` strictly-stationary independent noise, `√n X̄ₙ ⇒ N(0, vₘ)`
with `vₘ = ∑_{|h| ≤ q} γ(h)` (the case `q = 1`, `Xₜ = Zₜ − Zₜ₋₁`, is the degenerate `N(0,0)`). The library's
`movingAverage_clt`, which assembles `q`-dependence, strict and weak stationarity, centering and `L²` and
applies the `m`-dependent CLT `thm_6_4_2`. -/
alias example_6_4_4 := DeepWiki.TimeSeries.movingAverage_clt

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§6.4: Example 6.4.2 (the sample coefficient of variation `s_n / X̄_n` is asymptotically normal) [deferred];
Definition 6.4.2 (asymptotic normality of a sequence of random `k`-vectors) [infra];
Proposition 6.4.2 (linear images `B Xₙ` of an asymptotically normal sequence are asymptotically normal) [infra];
Proposition 6.4.3 (the multivariate delta method) [infra];
the i.i.d. ⟹ strictly-stationary bridge (`movingAverage_clt` takes strict-stationary independent noise;
genuinely i.i.d. noise needs `iIndepFun + IdentDistrib ⟹ IsStrictlyStationary`, the shift-invariant
`infinitePi` joint law) [infra]
(The headline §6.4 results are done: the `m`-dependent CLT `thm_6_4_2`/`thm_6_4_2_i`, the linear-process
CLT `clt_linearProcess`, the 1-D delta method `prop_6_4_1`, MA m-dependence `example_6_4_3`, and the MA CLT
`example_6_4_4`. The remaining items are the vector-AN framework (`Definition 6.4.2`/`Proposition 6.4.2`/`6.4.3`)
and the iid⟹strictly-stationary bridge; the multivariate iid CLT `multivariate_iid_clt` is the engine for
the vector results.) -/

end DeepWiki.Ts
