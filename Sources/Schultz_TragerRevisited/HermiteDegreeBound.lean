import DeepWiki.SymbolicIntegration.AlgebraicHermiteCompleteness
import Sources.Schultz_TragerRevisited.Source

/-! # Schultz §4 (Hermite reduction) — catalog
Pointers to the `DeepWiki.SymbolicIntegration` algebraic-Hermite machinery: the Lemma 4.4 proper-rational
pole conditions, the §4.3 / eq.4.9 Hermite degree bound `deg(fᵢ) ≤ N − δᵢ`, and the rational-part
exhaustiveness (the Hermite reduction captures all of the rational part).

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
Hermite-uniqueness solvability (§4.6, the unique `fᵢ mod V` of the linear system) [infra]: the
  degree-bounded `K`-linear system's solvability/uniqueness as a proved theorem (the residual
  `HermiteDerivativePartResidual` is stated and shown equivalent to the frontier, not discharged).
The infinite-place degree-bound linear solve (§4.7–4.9, eq.4.9 as a solved system) [infra]: the
  operational construction of the `fᵢ` of bounded degree, beyond the degree *inequality* below.
-/

namespace DeepWiki.Sch

open DeepWiki.SymbolicIntegration.AlgebraicHermite

/-- **Lemma 4.4(1)** (§4, the finite-place pole condition): the differential `Σ(aᵢ/b)ηᵢ dx` (relatively
prime `b, aᵢ`) has only simple finite poles iff the denominator `b` is squarefree (over char 0,
`IsCoprime b b'`). The library's `pole_condition_finite_iff_squarefree`. -/
abbrev lemma_4_4_finite := @pole_condition_finite_iff_squarefree

/-- **Lemma 4.4(2)** (§4, the infinite-place pole condition): `Σ(aᵢ/b)ηᵢ dx` has only simple poles at
infinite places iff `∀ i, deg(aᵢ) + δᵢ < deg(b)` — the proper-rational degree datum. The library's
`pole_condition_infinite_iff_degree`. -/
abbrev lemma_4_4_infinite := @pole_condition_infinite_iff_degree

/-- **The Hermite degree bound, leading-coefficient form** (§4.3, eq.4.9): for the differentiated Hermite
relation `a = c·V'·f + e·f + g` with a non-cancelling top coefficient, `deg(e·f)` and `deg(g)` are bounded
by the candidate top degree. The sharp leading-coefficient comparison. The library's
`natDegree_hermiteNum_le_of_topCoeff_ne_zero`. -/
abbrev hermite_degreeBound_topCoeff := @natDegree_hermiteNum_le_of_topCoeff_ne_zero

/-- **★ The Hermite degree bound in Schultz's `N − δ` form** (§4.3, eq.4.9): packaging the
leading-coefficient bound with the infinite-place degree datum `deg(c) = deg(b)`, `deg(fᵢ) ≤ N − δᵢ` for
`N = hermiteBoundN` — the exact degree bound the §4.7–4.9 infinite-place linear solve searches under. The
library's `natDegree_hermiteNum_le`. -/
abbrev eq_4_9_degreeBound := @natDegree_hermiteNum_le

/-- **Rational-part exhaustiveness** (§4.9, the Hermite reduction captures all of the rational part):
given the precise residual (the Hermite-reduced `v` drives the derivative part of `f − v′` to a constant),
`f − v′` is purely logarithmic for every `f, v` with both elementary. The library's
`rationalPartExhaustiveness_of_residual`. -/
abbrev rationalPartExhaustiveness := @rationalPartExhaustiveness_of_residual

end DeepWiki.Sch
