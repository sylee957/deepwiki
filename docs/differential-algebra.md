# Computational Differential Algebra

The setting for symbolic integration is _differential algebra_, and this project
makes it _computational_: the carriers are fields with **computable** operations
and a **computable** derivation, bridged to Mathlib's abstract differential-algebra
hierarchy by a homomorphism. Below, each mathematical notion is paired with the
Lean typeclass or theorem that realizes it.

## The differential field

A _differential field_ is a field $K$ with a _derivation_ $D : K \to K$ — an
additive map satisfying the Leibniz rule $D(ab) = a\,D(b) + b\,D(a)$. Additivity
and Leibniz already force the familiar calculus identities: $D(1) = 0$, the power
rule $D(a^n) = n\,a^{n-1} D(a)$, and the quotient rule
$D(a/b) = (b\,D(a) - a\,D(b))/b^2$.

_In Mathlib_ this is the `Differential` class (a field carrying a derivation
$a \mapsto a'$), built on `Derivation`. _In the engine_ it splits into two
**computable** typeclasses, deliberately free of any abstract field so they reduce
under `native_decide`:

- [`CField`](../DeepWiki/SymbolicIntegration/GenericPolyEngine.lean#L33) — a type with
  computable field operations (`add`, `mul`, `neg`, `inv`, and a _decidable_
  `isZero`);
- [`CDiffField`](../DeepWiki/SymbolicIntegration/ComputableMonomialDeriv.lean#L40) —
  one further computable operation `cderiv : α → α`, the derivation.

## The bridge to Mathlib: a homomorphism

A computable carrier is deliberately _not_ a Mathlib field — keeping it
abstraction-free is exactly what lets the engine evaluate. The connection to
Mathlib's theory is made instead by a _homomorphism_, supplied by a companion
specification:

- [`CFieldSpec`](../DeepWiki/SymbolicIntegration/GenericPolyEngine.lean#L72) carries a
  map `toK : α → K` into a genuine Mathlib `Field K` and certifies that it
  _intertwines every operation_ — `toK_add`, `toK_mul`, `toK_neg`, `toK_inv`,
  `toK_zero`, `toK_one`, so `toK` is a field homomorphism — together with
  `isZero_iff`, that the computable zero test is correct ($\mathtt{isZero}\,a$ iff
  $\mathrm{toK}\,a = 0$). The map need not be injective; the engine computes on
  representatives.
- [`CDiffFieldSpec`](../DeepWiki/SymbolicIntegration/ComputableMonomialDeriv.lean#L47)
  extends the bridge to the derivation: it supplies a Mathlib `Differential K` and
  certifies `toK_cderiv`, that $\mathrm{toK}(\mathtt{cderiv}\,a) = (\mathrm{toK}\,a)'$
  — the computable derivation commutes with Mathlib's field derivation through
  `toK`.

So every identity the engine establishes by computation transfers to Mathlib's
abstract differential field by pushing it through `toK`. This split — bridge-free
computable operations on one side, the noncomputable `toK` homomorphism on the
other — is the keystone that makes the whole tower simultaneously _evaluable_ and
_provably correct_.

## Constants

The _constants_ are the kernel $\{c : D(c) = 0\}$, a subfield that plays the
structural role $\mathbb{R}$ or $\mathbb{C}$ play in analysis. The running base is
the rational functions $\mathbb{Q}(x)$ with $D = d/dx$, whose constants are
exactly $\mathbb{Q}$. In the engine this base is the `CDiffField ℚ` instance with
`cderiv := 0` — $\mathbb{Q}$ is a field of constants — whose bridge sends `cderiv`
to the zero derivation on Mathlib's $\mathbb{Q}$. Constants matter because an
antiderivative is unique only up to one, and because "is this a genuinely new
transcendental?" ultimately asks whether an element stays among the existing
constants.

## The logarithmic derivative

For a nonzero $a$, the _logarithmic derivative_ is $D(a)/a$. It turns products into
sums — $D(ab)/(ab) = D(a)/a + D(b)/b$ and $D(a^n)/a^n = n\,D(a)/a$ — a homomorphism
from the multiplicative group to the additive group. _In Mathlib_ this is
`Differential.logDeriv`, with the homomorphism lemmas `logDeriv_mul`,
`logDeriv_div`, `logDeriv_pow`.

This single identity is why logarithms and exponentials organize the whole
algorithm. A logarithm $t = \log u$ is, by definition, an element with
$D(t) = D(u)/u$ — its derivative _is_ a logarithmic derivative of the base. An
exponential $t = \exp u$ satisfies $D(t)/t = D(u)$ — its logarithmic derivative
lands back in the base. The two transcendental monomials are exactly the two
behaviours of the logarithmic-derivative map, and the algorithm's case split
follows that dichotomy.

## Integration as a preimage problem

In this language integration is a _preimage problem_ for $D$: given $f$, find $g$
with $D(g) = f$, or prove there is none. No analytic notion of "function" is
needed — the derivation carries all the structure. The next chapter states which
$f$ admit an _elementary_ answer (Liouville's theorem); the chapters after build
the computable tower and the decision procedure that finds $g$.
