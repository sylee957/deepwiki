# Proof Status

A reader-facing digest of what the formalization proves, and of what is — by
design — left as an explicit hypothesis. The authoritative, always-current detail
is the verified function index `IntegrationFunctionsCatalog` and the full Lean
API; this page is the map, not the territory.

The one-line summary: the transcendental Risch integrator is verified on **both**
axes — _soundness_ (every integral it returns is correct) and _completeness_ (its
`none` is a correct "not elementary" verdict) — resting only on the honest Risch
new-monomial conditions described below.

Throughout, a declaration name links to its definition in the local source tree.

## Soundness: every returned integral is correct

The a-priori guarantee is $D(\int f) = f$: whenever the driver returns an answer,
that answer differentiates back to the integrand. This is proved, not merely
checked at runtime, across the full transcendental driver.

* The driver `cIntegrateGFull` is sound in the base regime across all three
  branches — the normal (Hermite) part, the polynomial part, and the special
  part.
* The logarithmic part rests on the _Rothstein–Trager_ residue-to-root
  bijection: a simple root's resultant gcd is exactly the linear factor it
  predicts.
* The Hermite reduction's leftover is proved proper, so the rational part is
  genuinely reduced —
  [`cIntegrateGFull_primitive_oneShot_inputProper_qfunNZG`](../DeepWiki/SymbolicIntegration/ComputableOneShotAssembly.lean#L1769).
* The Risch differential-equation _cleared identity_ holds in all three
  cancellation regimes — non-cancellation, primitive cancellation, and
  hyperexponential cancellation — each modulo a single shared gcd-`Associated`
  residual whose mathematical core is itself proved (the tower gcd witness).
* The cancellation-case polynomial Risch-DE solver is sound independently of the
  base oracle: the degree-by-degree subtraction makes the identity exact however
  the leading coefficients are chosen.

## Completeness: `none` is a correct verdict

Completeness is the converse — if an elementary antiderivative exists, the
algorithm finds it; equivalently, a `none` answer is a proof of
non-elementarity. The machinery is assembled in two layers.

The _Risch differential-equation_ layer: the solver is a decision procedure
(`some` exactly when the field-level equation is solvable), and this lifts up the
whole differential tower by induction — completeness at the constant base $\mathbb{Q}$
(where the equation is plain linear algebra), and a step that propagates
completeness from one level to the next, with the base oracle's role discharged by
the level below —
[`crischFieldComplete_step`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDECompleteness.lean#L477).

The _structure-theorem_ layer, via Liouville's theorem in the transcendental
setting:

* the rational base, where non-degeneracy is a single decidable test;
* the logarithmic extension, unconditional given the new-monomial condition —
  [`isLiouville_logExtension_uncond`](../DeepWiki/SymbolicIntegration/LiouvilleLogExtension.lean#L2052);
* the exponential extension, likewise (and, structurally, the cleaner of the two
  — its "interior" reduction needs no surviving linear term);
* and the multi-level tower, obtained by stacking the single-level result through
  the transitivity of the Liouville property.

The tangent case (Bronstein §8.4) is a separate coupled differential-equation
engine; its abstract soundness is proved end to end — the underlying
$\mathbb{Q}$-Gaussian-elimination is proved correct, and the degree-by-degree telescoping
is proved to reconstruct a genuine solution — so it needs no runtime
self-certificate.

## The honest hypotheses

Some side conditions correctly remain hypotheses rather than gaps: they are the
genuine _new-monomial_ conditions of the Risch theory, the facts that make each
tower level a real transcendental extension. The completeness results are stated
modulo exactly these, and no more:

* non-degeneracy of a logarithmic or exponential monomial (its logarithmic
  derivative is not already "trivial" in the base);
* the analogous parametric non-degeneracy in the §6.3 degree bound;
* the §6.1 normal-denominator pole bound.

These are necessary — drop them and the corresponding statement is genuinely
false — so they are inputs, not omissions.

## Computable, and validated

The entire engine is _computable_: the integrator, the gcd and Risch-DE towers,
and the algebraic machinery all reduce, and the worked examples are checked by
`native_decide` against the integrand. The design that makes this possible is a
split between computable field operations and a non-computable specification
bridge, which keeps the tower evaluable while still admitting abstract proofs.

## The algebraic case

Alongside the transcendental tower, the project develops the _algebraic_ side —
integrating $\int y\,dx$ for $y$ algebraic over $\mathbb{Q}(x)$ (Trager/Bronstein,
realized as computational algebraic geometry rather than abstract Riemann–Roch).
For the $n = 2$ hyperelliptic case it is complete end to end: the rational part,
the logarithmic part with its Jacobian-torsion decision (Cantor's algorithm), and
both soundness
([`cIntegrateAlgebraicDecide_sound`](../DeepWiki/SymbolicIntegration/ComputableAlgebraicDecide.lean#L184))
and completeness
([`cIntegrateAlgebraicDecide_complete`](../DeepWiki/SymbolicIntegration/ComputableAlgebraicDecide.lean#L273)).
The one assumed input is Weil's torsion-order bound (Mathlib lacks Jacobian good
reduction); higher-degree radicals and general-curve integral bases are in
progress. The [Integrating Algebraic Functions](algebraic-functions.md) chapter
covers it.

## Beyond the current scope

Two further algorithms are genuinely separate engines, not yet formalized: the
§8.2 hyperexponential-coupled and §8.3 general-nonlinear differential-equation
cases. The tangent soundness headline is currently stated at the worked-example
level, with the general degree case already available as the proved telescoping
lemma it instantiates.
