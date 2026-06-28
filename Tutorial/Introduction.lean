import VersoManual

open Verso.Genre Manual

/-! Introduction chapter of the Risch-algorithm tutorial (prose-only stub). -/

#doc (Manual) "Introduction" =>

_Symbolic integration_ is the problem of computing an antiderivative of a given
function in closed form, or proving that none exists among the _elementary_
functions. The _Risch algorithm_ is the decision procedure that solves this
problem for the transcendental elementary functions: given $`f`, it either
returns an elementary $`g` with $`g' = f`, or certifies that no such $`g` exists.

This tutorial is a guided tour of the DeepWiki formalization of that algorithm in
Lean 4. The punchline: the project mechanizes both directions. _Soundness_ — that
every integral the algorithm returns is correct, $`D(\int f) = f`, across all
three regimes (rational, exponential, primitive) — and the _completeness_
machinery — the Risch differential-equation tower induction together with
Liouville's theorem (logarithmic, exponential, and multi-level extensions) and the
tangent case — modulo the honest new-monomial side conditions stated explicitly.

The chapters that follow build the theory from the ground up: differential
algebra, the integration problem and Liouville's theorem, the rational case, the
transcendental tower, the Risch differential equation, and finally the soundness
and completeness results as they are proved in the library. The full Lean API is
linked at `/deepwiki/api/`.
