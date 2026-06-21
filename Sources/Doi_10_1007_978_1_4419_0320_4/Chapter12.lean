import DeepWiki.TimeSeries.StateSpace
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 12: State-Space Models and the Kalman Recursions
The state-space model and its deterministic state and observation recursions are algebraic and
formalized; the Kalman recursions (prediction, filtering, smoothing) are matrix-algebra recursions
whose correctness rests on the L²-projection operator and are infra-blocked. -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries

/-! ## §12.1 State-Space Models (p.463)
A linear state-space model couples an observation equation `Yₜ = Gₜ Xₜ + Wₜ` (eq 12.1.1) to a
state equation `X_{t+1} = Fₜ Xₜ + Vₜ` (eq 12.1.2), where `{Vₜ}` and `{Wₜ}` are orthogonal
white-noise sequences with covariance matrices `Qₜ` and `Rₜ`. Many ARMA and ARIMA processes admit
such a representation. -/

/-- **§12.1 (eq 12.1.1 and 12.1.2)**: the (time-invariant) linear **state-space model** — the
state-transition matrix `F` and observation matrix `G` of `X_{t+1} = F Xₜ + Vₜ`, `Yₜ = G Xₜ + Wₜ`,
with the state trajectory (`state`), the observation (`obs`), and the deterministic law
`Xₜ = Fᵗ x₁` (`state_zero_noise`). The library's `StateSpaceModel`. -/
abbrev def_12_1_1 := @DeepWiki.TimeSeries.StateSpaceModel

/-! ## §12.2 The Kalman Recursions (p.474)
The Kalman recursions solve the three projection problems — **prediction** `P(Xₜ | Y₀,…,Y_{t-1})`,
**filtering** `P(Xₜ | Y₀,…,Yₜ)`, and **smoothing** `P(Xₜ | Y₀,…,Yₙ)` (Definition 12.2.1) — by a
matrix recursion for the best linear predictor `X̂ₜ` and its error covariance `Ωₜ`. The recursion
is matrix algebra (definable), but its correctness rests on the L²-projection operator `P` and is
infra-blocked. -/

/-! ## §12.3 State-Space Models with Missing Observations (p.482)
Irregularly spaced or missing data are handled by zeroing the relevant observation matrices, so
the Kalman recursions still compute the Gaussian likelihood of the realized observations `{Yₜ*}`
(eq 12.3.6) — applied to ARMA and ARIMA series with missing values (Example 12.3.1); infra-blocked. -/

/-! ## §12.4 Controllability and Observability (p.491)
The controllability and observability of a state-space representation, and their role in
determining the minimal dimension of a representation (Proposition 12.4.3, relating controllability
to the ARMA polynomials `Φ(B)` and `Θ(B)`); the matrix theory is tractable but is not formalized
here. -/

/-! ## §12.5 Recursive Bayesian State Estimation (p.496)
Recursive Bayesian filtering propagates the conditional distribution of the state, computing
conditional expectations for a large class of (not necessarily Gaussian) state-space models; the
integral recursions are infra-blocked. -/

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§12.2: Definition 12.2.1 (the prediction/filtering/smoothing projection problems) [infra]; the Kalman
prediction recursion for `X̂ₜ` and `Ωₜ` [infra]; the Kalman filtering recursion [infra]; the Kalman
smoothing recursion [infra]
§12.3: the Gaussian likelihood of the realized observations via the missing-data Kalman recursion (eq
12.3.6) [infra]; Example 12.3.1 (ARMA/ARIMA with missing values) [infra]
§12.4: Proposition 12.4.3 (controllability/observability and the minimal-representation dimension)
[deferred]; the controllability and observability definitions [deferred]
§12.5: recursive Bayesian state estimation (the conditional-distribution integral recursions) [infra]
(The state-space model and its deterministic recursions (def 12.1.1) are done; the Kalman recursions
rest on the L²-projection operator, not yet built; the §12.4 matrix theory is reachable.) -/

end DeepWiki.Ts
