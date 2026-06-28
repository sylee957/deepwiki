import VersoManual

open Verso.Genre Manual

/-! Risch-differential-equation chapter of the tutorial (prose-only stub). -/

#doc (Manual) "The Risch Differential Equation" =>

Lifting integration up one level of the tower reduces to solving the _Risch
differential equation_ (RDE): given $`f` and $`g` in a differential field, find
$`y` with $`y' + f\,y = g`. This is the engine that drives the recursion through
the monomial extensions.

This chapter will lay out the RDE and its solution strategy: the decomposition
into _normal_, _special_, and _polynomial_ parts, the distinct regimes that arise
for logarithmic, exponential, and tangent monomials, and the algorithms that
solve each. The RDE solver is what the soundness and completeness results are
ultimately about; its formalized form is linked at `/deepwiki/api/`.
