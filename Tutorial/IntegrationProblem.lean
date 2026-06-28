import VersoManual

open Verso.Genre Manual

/-! Integration-problem chapter: elementary functions and Liouville's theorem. -/

#doc (Manual) "The Integration Problem and Liouville's Theorem" =>

What does it mean to integrate "in closed form"? The honest answer is a
definition, and then a theorem that makes the definition tractable.

# Elementary functions

Fix a base differential field — for us $`\mathbb{Q}(x)` with $`D = d/dx`. A function
is _elementary_ over the base if it lives in some tower
$`F_0 \subseteq F_1 \subseteq \cdots \subseteq F_n`, with $`F_0` the base and each
step $`F_{i+1} = F_i(t)` adjoining one of three kinds of monomial:

* an _algebraic_ element ($`t` is a root of a polynomial over $`F_i`);
* a _logarithm_ ($`D(t) = D(u)/u` for some $`u \in F_i`);
* an _exponential_ ($`D(t)/t = D(u)` for some $`u \in F_i`).

This captures exactly the functions one writes with roots, $`\log`, and $`\exp`
(and hence the trigonometric and inverse-trigonometric functions, via complex
exponentials and logarithms). The _integration problem_ is: given $`f` in such a
tower, produce an elementary $`g` with $`D(g) = f`, or prove that no elementary
$`g` exists.

# Liouville's theorem

The naive search space — "all elementary functions" — is unbounded. Liouville's
theorem collapses it. In its differential-algebra form: if $`f \in F` has an
antiderivative elementary over $`F`, then the antiderivative already has a very
restricted shape, expressible inside $`F` itself (with constants from an algebraic
extension):

$`f = D(v) + \sum_{i} c_i \, \dfrac{D(u_i)}{u_i}`,

with $`v \in F`, the $`c_i` constants, and the $`u_i \in F` (after adjoining the
needed constants). Equivalently $`\int f = v + \sum_i c_i \log u_i`. The content is
sharp: the only _new_ transcendentals an elementary integral may introduce are
*logarithms*, and their arguments and the rational part $`v` stay in the field
you started in.

# Why it is the foundation

Liouville turns an open-ended search into a structured one. To integrate $`f` it
suffices to look for a single field element $`v` and a finite logarithmic sum — and
if that search provably fails, Liouville guarantees no elementary integral exists
at all. That is precisely the shape of a decision procedure, and it is the
backbone of the completeness direction proved later in this tutorial: the
algorithm's `none` is a refutation _because_ Liouville says any integral would have
had the form the algorithm searched for.

Mathlib provides the abstract Liouville property (`IsLiouville`) and the algebraic
case; the DeepWiki project adds the transcendental instances — the logarithmic and
exponential single-step extensions and the multi-level tower — which this tutorial
returns to in the completeness chapter. The declarations are linked at
`/deepwiki/api/`.
