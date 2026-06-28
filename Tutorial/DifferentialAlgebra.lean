import VersoManual

open Verso.Genre Manual

/-! Differential-algebra chapter: derivations, constants, the logarithmic derivative. -/

#doc (Manual) "Differential Algebra" =>

The setting for symbolic integration is _differential algebra_: a ring or field
equipped with a _derivation_ $`D` — an additive map satisfying the Leibniz rule
$`D(ab) = a\,D(b) + b\,D(a)`. Everything the Risch algorithm does is phrased here,
with no limits or topology: differentiation is the map $`D`, and integration is
the search for a preimage under it.

# Derivations and constants

A _derivation_ on a commutative ring $`R` is an additive map $`D : R \to R` with
$`D(ab) = a\,D(b) + b\,D(a)`. Additivity and Leibniz already force the familiar
calculus identities — $`D(1) = 0`, the power rule $`D(a^n) = n\,a^{n-1} D(a)`, and,
over a field, the quotient rule $`D(a/b) = (b\,D(a) - a\,D(b))/b^2`. A
_differential field_ is a field with a derivation; a _differential field
extension_ $`K \subseteq L` is one whose derivation restricts to $`K`'s.

The _constants_ are the kernel $`\mathrm{Const} = \{c : D(c) = 0\}`. They form a
subring — a subfield when $`R` is a field — and play the structural role that
$`\mathbb{R}` or $`\mathbb{C}` play in analysis. The running base example is the
rational functions $`\mathbb{Q}(x)` with $`D = d/dx`, whose constants are exactly
$`\mathbb{Q}`. The constants matter because the antiderivative of a given element
is unique only up to a constant, and because "is this expression a new
transcendental?" ultimately asks whether it stays inside the existing constants.

# The logarithmic derivative

For a nonzero $`a`, the _logarithmic derivative_ is $`D(a)/a`. Its defining
property is that it turns products into sums:
$`D(ab)/(ab) = D(a)/a + D(b)/b` and $`D(a^n)/a^n = n\,D(a)/a`. It is a
homomorphism from the multiplicative group to the additive group of the field.

This single identity is why logarithms and exponentials are the organizing cases
of the whole algorithm. A logarithm $`t = \log u` is, by definition, an element
with $`D(t) = D(u)/u` — its derivative _is_ a logarithmic derivative of the base.
An exponential $`t = \exp u` satisfies $`D(t)/t = D(u)` — its logarithmic
derivative lands back in the base. So the two transcendental monomials are exactly
the two ways the logarithmic-derivative map can behave, and the algorithm's case
split follows that dichotomy.

# Why this is the right setting

"Elementary" has a purely algebraic definition here: a function is elementary over
a base differential field if it lives in a tower of extensions, each step adjoining
an algebraic element, a logarithm, or an exponential. Integration becomes the
_preimage problem_ for $`D` inside such a tower — find $`g` with $`D(g) = f`, or
prove there is none — and the Risch algorithm is the decision procedure for it. No
analytic notion of "function" is needed; the derivation carries all the structure.

The library builds on Mathlib's differential-algebra hierarchy — the
`Differential` class, `Derivation`, and `Differential.logDeriv` with its
homomorphism lemmas (`logDeriv_mul`, `logDeriv_div`, `logDeriv_pow`). The
project's computable carriers add their own derivations on top; the relevant
declarations are linked at `/deepwiki/api/`.
