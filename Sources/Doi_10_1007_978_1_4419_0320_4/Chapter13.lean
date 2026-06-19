import DeepWiki.TimeSeries.FractionalDifference
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 13: Further Topics
A survey chapter. The fractional-difference coefficients (long memory) are algebraic and
formalized; the transfer-function, long-memory, infinite-variance, and nonlinear models themselves
involve infinite linear filters, the Gamma function, stable laws, and nonlinear recursions, and are
infra-blocked or survey-level. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries

/-! ## §13.1 Transfer Function Modelling (p.506)
A transfer function model relates an output series `Yₜ = ∑_{j≥0} τⱼ X_{t-j} + Nₜ` to an input
series `{Xₜ}` through a one-sided linear filter `{τⱼ}` plus added noise `{Nₜ}` (eq 13.1.1); the
filter is estimated after **prewhitening** the input (Definition 13.1.1). The infinite filter and
its estimation are infra-blocked. -/

/-! ## §13.2 Long Memory Processes (p.521)
A **fractionally integrated** ARIMA(0,d,0) process satisfies `(1 − B)^d Xₜ = Zₜ` with
`d ∈ (−½, ½)` (Definition 13.2.1, eq 13.2.3); for such `d` there is a unique stationary causal
solution (Theorem 13.2.1) whose autocorrelations decay slowly (long memory). The fractional
difference operator `(1 − B)^d = ∑_{j≥0} binom(d,j)(−1)ʲ Bʲ` has its coefficients formalized
below; the operator's action on a process (an infinite sum) and Whittle estimation are
infra-blocked. -/

/-- **§13.2 (eq 13.2.3)**: the coefficients `binom(d,j)(−1)ʲ` of the fractional difference operator
`(1 − B)^d` defining the long-memory ARIMA(0,d,0) process (`= 1` at `j = 0`, `= −d` at `j = 1`).
The library's `fracDiffCoeff`. -/
noncomputable abbrev eq_13_2_3 := @DeepWiki.TimeSeries.fracDiffCoeff

/-! ## §13.3 Linear Processes with Infinite Variance (p.539)
Linear processes driven by heavy-tailed (infinite-variance, stable) noise — e.g. a Cauchy-driven
MA process — where the usual second-order theory fails and the limit theory uses stable laws;
infra-blocked. -/

/-! ## §13.4 Non-Linear Models (p.546)
Nonlinear time-series models — threshold autoregressions, bilinear models, and ARCH and GARCH
conditional-variance models — relaxing the linear and Gaussian assumptions, and their probabilistic
and statistical analysis; infra-blocked. -/

end DeepWiki.Ts
