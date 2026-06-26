import Sources.Doi_10_1016_S0747_7171_08_80027_2.Source

/-! # Bronstein-1990 catalog — coverage
The combined elementary-over-algebraic integration decision procedure. The **concrete** cases of the
grand unification (elementary = transcendental monomial θ + algebraic radical y) are now formalized in
`Sources.Doi_10_1016_S0747_7171_08_80027_2.ElementaryIntegration`: the algebraic-radical arc running over
a transcendental tower base `α = ℚ(x)(θ)` (θ exponential or logarithmic), with the worked elementary
integrals `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over ℚ(x)(eˣ) and `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x)
validated through the actual radical derivation. What remains is the **general** decision procedure
(the recursion over arbitrary towers, the symbolic log part, Hermite on general curves) — the
research-grade remainder below.

## NOT YET FORMALIZED (audit 2026-06-26)
§ The general elementary-over-tower recursion (Thm 1 and Thm 2): the recursive integration of an
  elementary function over an *arbitrary* tower, coupled with the Risch differential equation, of which
  `ElementaryIntegration` realizes only the concrete algebraic-radical-over-single-monomial case
  `[research]`.
§ The log part over towers: the `ℚ`-specific linear solve producing the logarithmic terms
  `Σ cᵢ log uᵢ` when the ground field is a transcendental tower (vs. the rational-part-only and worked
  antiderivative cases formalized) `[research]`.
§ Hermite reduction on algebraic curves over a liouvillian ground field: the curve-Hermite step
  removing multiple finite poles when the ground field carries logs/exps, not just constants
  `[research]`.
§ Puiseux expansions at infinity: the local analysis at the places at infinity needed to bound
  the polynomial part and the residues there `[research]`.
§ The generalized Rothstein necessary condition: the resultant/order criterion for elementary
  integrability lifted to the combined elementary-over-algebraic tower `[research]`. -/

namespace DeepWiki.Bie

end DeepWiki.Bie
