# Integrating Algebraic Functions

The transcendental tower of the previous chapters adjoins logarithms,
exponentials, and tangents. The other way an elementary extension can arise is
_algebraic_: adjoining a root $y$ of a polynomial over the base — for instance
$y = \sqrt{x^3 + 1}$, a root of $y^2 - (x^3 + 1)$. Integrating $\int R\,dx$ when
the integrand involves such a $y$ is a genuinely different problem, and its
solution — due to Trager and Bronstein — is _computational algebraic geometry_:
resultants, Gröbner bases, and divisor arithmetic on a curve, not the abstract
Riemann–Roch machinery the theory is often phrased with. The project realizes
that computational form.

## The algebraic function field

Fix the base differential field $K(x)$. An _algebraic function_ $y$ satisfies a
polynomial equation over it; the simplest case is a _radical_, $y^n = f$ with
$f \in K(x)$, and then the functions built from $x$ and $y$ form the field
$K(x)[y]/(y^n - f)$. An element is $\sum_{i<n} a_i y^i$ with coefficients
$a_i \in K(x)$.

_In the engine_ this carrier is
[`RadElem`](../DeepWiki/SymbolicIntegration/ComputableRadicalExtension.lean#L74) — a
coefficient list $[a_0, \dots, a_{n-1}]$, with the degree $n$ and radicand $f$
carried by the operations rather than the type. (Trager's thesis writes the
carrier $\mathrm{RadExt}\,\alpha\,n\,f$; the realized Lean type is `RadElem`.) The
coefficients live in a tower level, so the algebraic engine composes _on top of_
the transcendental one — $K$ can itself be $\mathbb{Q}(x)$ or a transcendental
tower. Arbitrary (non-radical) curves $K(x)[y]/(f)$ for monic $f$ are handled by a
parallel carrier with its own multiplication, trace, and discriminant in
[`afReduce`](../DeepWiki/SymbolicIntegration/ComputableAlgFunctionField.lean#L63).

## The derivation: Trager's diagonal insight

Differentiating $y^n = f$ gives $n\,y^{n-1}\,D(y) = D(f)$, so
$D(y) = \dfrac{D(f)}{n\,f}\,y$. The logarithmic-derivative-like factor
$\ell = D(f)/(n f)$ lies in the base, so the derivation is _diagonal_:

$$ D\!\left(\sum_i a_i y^i\right) = \sum_i \big(D(a_i) + a_i\,i\,\ell\big)\,y^i. $$

No power of $y$ mixes into another — a structural simplification that makes $D$
commute with each coefficient projection.

_In the engine_ this is
[`radDeriv`](../DeepWiki/SymbolicIntegration/ComputableRadicalExtension.lean#L155), and
the diagonal identity is checked on the running elliptic example: for $y^2 = x^3+1$
it computes $D(y) = \tfrac{3x^2}{2(x^3+1)}\,y$
([`radDeriv_radGen_eq`](../DeepWiki/SymbolicIntegration/ComputableRadicalExtension.lean#L196)).
For arbitrary curves the derivation uses the implicit $y' = -f_x/f_y$, computed
through a Bézout cofactor in
[`afDeriv`](../DeepWiki/SymbolicIntegration/ComputableGeneralDerivation.lean#L113).

## The rational part

As in the rational case, the first stage extracts the part of the integral that is
itself an algebraic function. Over the extension this is a Hermite-style reduction
of $\int R/(B\,y)$: the denominator $B$ is squarefree-decomposed and partial-
fractioned, and each factor is classified by how it meets the branch locus of the
curve, dispatching one of several reduction cases.

_In the engine_ the driver is
[`radIntegrateRational`](../DeepWiki/SymbolicIntegration/ComputableRadicalRationalDriver.lean#L188).
Its correctness is the round-trip on the worked elliptic integral
$\int \frac{dx}{(x-1)^3\sqrt{x^3+1}}$:
[`cubeDriver_integrates`](../DeepWiki/SymbolicIntegration/ComputableRadicalIntegrate.lean#L241)
checks that the _actual_ diagonal `radDeriv` of the assembled rational part equals
the integrand's rational part — a genuine elliptic-curve radical, integrated and
verified by computation.

## The logarithmic part and torsion

What remains after the rational part is a sum of logarithms — but here the theory
becomes deep. A residual term has the form $c\log u$, and finding $u$ leads, as in
Rothstein–Trager, to a residue computation
([`cAlgResidueResultant`](../DeepWiki/SymbolicIntegration/ComputableAlgebraicResidues.lean#L95)).
The subtlety is _when such a $u$ exists at all_: a term $\tfrac1m\log g$ is
available exactly when the divisor $m\cdot D$ of the candidate is _principal_ on
the curve's Jacobian — a statement that the corresponding point has _finite order_
(is torsion). If no multiple of the divisor is principal, the integral is **not
elementary**.

_In the engine_: a log candidate is verified by
[`radIsLogIntegral`](../DeepWiki/SymbolicIntegration/ComputableRadicalLogIntegral.lean#L69)
and solved for by
[`radLogArgSolve`](../DeepWiki/SymbolicIntegration/ComputableRadicalLogArgument.lean#L213);
the torsion question is decided by
[`cantorOrder`](../DeepWiki/SymbolicIntegration/ComputableDivisorOrder.lean#L124) —
Cantor's algorithm on the hyperelliptic Jacobian, run by good reduction modulo a
prime — and, when the order is finite, the generator is reconstructed by
[`principalGenerator`](../DeepWiki/SymbolicIntegration/ComputablePrincipalGenerator.lean#L133).
This divisor arithmetic (Mumford representatives, Cantor's composition) has no
Mathlib counterpart and is built computationally here, on the same resultant
([`cresultantG`](../DeepWiki/SymbolicIntegration/ComputableGenericBezout.lean#L97)) and
Gröbner primitives the rest of the engine uses.

## Soundness, completeness, and scope

The pieces assemble into a decision procedure for $\int R/(B\,y)$: it returns a
rational part plus a finite logarithmic sum, or reports that the integral is not
elementary.

_In the engine_:
[`cIntegrateAlgebraicDecide`](../DeepWiki/SymbolicIntegration/ComputableAlgebraicDecide.lean#L78)
is that procedure, and it is proved on both axes —
[`cIntegrateAlgebraicDecide_sound`](../DeepWiki/SymbolicIntegration/ComputableAlgebraicDecide.lean#L184)
(whenever it returns an answer $F$, $D(F)$ really is the integrand, with no runtime
re-check) and
[`cIntegrateAlgebraicDecide_complete`](../DeepWiki/SymbolicIntegration/ComputableAlgebraicDecide.lean#L273)
(a `none` is a correct "not elementary" verdict), both resting on Mathlib's
`Differential.IsLiouville` for the algebraic case.

The $n = 2$ hyperelliptic case is complete end to end — rational part, log part,
torsion decision, soundness, and completeness. The general-curve case — arbitrary
plane curves beyond radicals — is realized too, for the principal part and the
elementarity decision, by
[`cIntegrateGeneralCurveDecide`](../DeepWiki/SymbolicIntegration/ComputableGeneralCurveDecide.lean#L173).
The one genuine theoretical floor is _Weil's bound_ on the order of a torsion point
(the ceiling that makes the good-reduction search terminate): Mathlib has no
Jacobian good-reduction theory, so that bound is currently an input rather than a
proved lemma — the torsion decision itself runs, only its abstract termination
ceiling is assumed. Radicals of degree $n \ge 3$, general-curve integral bases, and
the general (non-hyperelliptic) torsion case are in progress.
