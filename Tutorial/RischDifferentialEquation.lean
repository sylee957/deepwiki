import VersoManual

-- The DeepWiki formalization lives in the SAME lake package, so a `Tutorial.*`
-- module can `import` it directly. This pulls in the corrected Risch-DE solver
-- and its soundness capstone so the prose below renders the REAL declarations.
import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound

open Verso.Genre Manual

-- Bring the formalization's namespace into scope so `{docstring …}` and
-- `{name …}` can resolve the declarations by their short names.
open DeepWiki.SymbolicIntegration

/-! Risch-differential-equation chapter of the tutorial — backed by the real
formalized solver and its soundness theorem (rendered inline via `{docstring …}`). -/

#doc (Manual) "The Risch Differential Equation" =>

Lifting integration up one level of the tower reduces to solving the _Risch
differential equation_ (RDE): given $`f` and $`g` in a differential field, find
$`y` with $`y' + f\,y = g`. This is the engine that drives the recursion through
the monomial extensions.

This chapter lays out the RDE and its solution strategy: the decomposition into
_normal_, _special_, and _polynomial_ parts, the distinct regimes that arise for
logarithmic, exponential, and tangent monomials, and the algorithm that solves
each. The RDE solver is what the soundness and completeness results are
ultimately about.

The declarations shown below are _not_ links or paraphrases: they are the actual
Lean declarations from the DeepWiki library, imported into this document and
rendered with their machine-checked signatures and docstrings.

# The corrected solver

The solver {InlineLean.name}`crischDESolveSound` is the genuinely sound recursive RDE
procedure over the tower carrier `QFunNZG β`. It weak-normalizes the input,
runs the §6.1 solvability check that the raw oracle omits, and only then hands
off to the inner solve — returning `none` exactly when the equation has no
elementary solution.

{docstring crischDESolveSound}

# Unconditional soundness

The capstone {InlineLean.name}`crischDESolveSound_field` states that whenever the solver
returns an answer, that answer really solves the original field-level Risch
differential equation. Note the rendered signature: the conclusion is the literal
identity $`D(Y) + F\cdot Y = G` over the rational-function field, and there is
_no_ `IsCanonNormalized` hypothesis — the solver's own check supplies it.

{docstring crischDESolveSound_field}
