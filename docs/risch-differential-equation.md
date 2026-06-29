# The Risch Differential Equation

Lifting integration up one level of the tower reduces to solving the _Risch
differential equation_ (RDE): given $f$ and $g$ in a differential field, find
$y$ with $y' + f\,y = g$. This is the engine that drives the recursion through
the monomial extensions.

This chapter lays out the RDE and its solution strategy: the decomposition into
_normal_, _special_, and _polynomial_ parts, the distinct regimes that arise for
logarithmic, exponential, and tangent monomials, and the algorithm that solves
each. The RDE solver is what the soundness and completeness results are
ultimately about.

Throughout, a declaration name links to its definition in the local source tree.

## The corrected solver

The solver [`crischDESolveSound`](../DeepWiki/SymbolicIntegration/ComputableRischDESolveSound.lean#L165)
is the genuinely sound recursive RDE procedure over the tower carrier
`QFunNZG β`. It weak-normalizes the input, runs the §6.1 solvability check that
the raw oracle omits, and only then hands off to the inner solve — returning
`none` exactly when the equation has no elementary solution.

## Unconditional soundness

The capstone [`crischDESolveSound_field`](../DeepWiki/SymbolicIntegration/ComputableRischDESolveSound.lean#L284)
states that whenever the solver returns an answer, that answer really solves the
original field-level Risch differential equation. The conclusion is the literal
identity $D(Y) + F\cdot Y = G$ over the rational-function field, and there is
_no_ `IsCanonNormalized` hypothesis — the solver's own check supplies it.
