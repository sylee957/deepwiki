import Sources.Doi_10_1016_S0747_7171_08_80027_2.Source

/-! # Bronstein-1990 catalog — coverage
The combined elementary-over-algebraic integration decision procedure. The **concrete** grand-unification
cases (elementary = transcendental monomial θ + algebraic radical y) are now formalized: the
algebraic-radical arc running over a transcendental tower base `α = ℚ(x)(θ)`
(`Sources.Doi_10_1016_S0747_7171_08_80027_2.ElementaryIntegration`, the worked
`∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` / `∫ dx/(x√(log x)) = 2√(log x)`), **and** — now — the **full** elementary
integral `∫ = v + Σ cᵢ log uᵢ` over a tower with **both** halves COMPUTED by the engine
(`Sources.Doi_10_1016_S0747_7171_08_80027_2.ElementaryIntegrationFull`): the log argument computed by a
`[CField β]`-generic Gaussian elimination over the tower field (`radLogArgSolve`), the rational part
computed by Case-3 degree-lowering under the actual tower derivation (`radIntegrateCase3G`), and the unified
integrator `cIntegrateElementary` round-tripping `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over ℚ(x)(eˣ).
So the concrete full elementary integral over a tower (both halves, principal case) is done. What remains is
the **general** decision procedure — the recursion over arbitrary deeper towers, the non-principal case,
Hermite on general curves — the research-grade remainder below.

## NOT YET FORMALIZED (audit 2026-06-26)
§ The general elementary-over-tower recursion (Thm 1 and Thm 2): the recursive integration of an
  elementary function over an *arbitrary* deeper tower coupled with the Risch differential equation, of
  which `ElementaryIntegration`/`ElementaryIntegrationFull` realize only the concrete
  algebraic-radical-over-single-monomial case (`v + Σ cᵢ log uᵢ`, both halves computed) `[research]`.
§ The non-principal / torsion case (Ch 6, points of finite order): elementary integrability when the
  divisor of the candidate log argument is torsion of order > 1 — beyond the principal-case log solve
  formalized in `radLogArgSolve` `[research]`.
§ Hermite reduction on algebraic curves over a liouvillian ground field: the curve-Hermite step
  removing multiple finite poles when the ground field carries logs/exps, not just constants
  `[research]`.
§ General non-radical curves and odd-degree Puiseux expansions at infinity: the local analysis at the
  places at infinity (for curves beyond simple radicals `y² = ρ`) needed to bound the polynomial part
  and the residues there `[research]`.
§ The generalized Rothstein necessary condition: the resultant/order criterion for elementary
  integrability lifted to the combined elementary-over-algebraic tower `[research]`. -/

namespace DeepWiki.Bie

end DeepWiki.Bie
