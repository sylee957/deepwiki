# Introduction

_Symbolic integration_ is the problem of computing an antiderivative of a given
function in closed form, or proving that none exists among the _elementary_
functions. The _Risch algorithm_ is the decision procedure that solves this
problem for the transcendental elementary functions: given $f$, it either
returns an elementary $g$ with $g' = f$, or certifies that no such $g$ exists.

This tutorial is a guided tour of the DeepWiki formalization of that algorithm in
Lean 4. The punchline is that the project mechanizes both directions through the
single driver
[`cIntegrateGFull`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L681).
_Soundness_ is the guarantee that every integral the algorithm returns is correct,
$D(\int f) = f$, across all three regimes (rational, exponential, primitive). The
_completeness_ machinery — the Risch differential-equation tower induction together
with Liouville's theorem (logarithmic, exponential, and multi-level extensions) and
the tangent case — establishes the converse, that a reported failure is a genuine
proof of non-elementarity, modulo the honest new-monomial side conditions stated
explicitly in the later chapters.

The chapters that follow build the theory from the ground up: differential
algebra, the integration problem and Liouville's theorem, the rational case, the
transcendental tower, the Risch differential equation, the soundness and
completeness results as they are proved in the library, and a closing chapter on
integrating algebraic functions. Throughout, a declaration name links to its
definition in the local source tree.
