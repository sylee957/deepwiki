# The Rational Case

Integrating a rational function $f \in K(x)$ is the base case, and it always
succeeds: every rational function has an elementary integral — a rational part
plus a sum of logarithms. The method has two stages, *Hermite reduction* and the
*Rothstein–Trager* logarithmic part, and it is the template the transcendental
tower later imitates one monomial at a time.

Throughout, a declaration name links to its definition in the local source tree.

## Hermite reduction

The first stage removes the *repeated* poles. Writing $f = P + A/D$, the
denominator $D$ is *squarefree-factored* as $\prod_i D_i^{\,i}$, where each
[`sqfreeFactPart`](../DeepWiki/SymbolicIntegration/SquarefreeFactorization.lean#L226)
$D_i$ collects the irreducible factors of multiplicity exactly $i$ and is itself
squarefree —
[`sqfreeFactPart_squarefree`](../DeepWiki/SymbolicIntegration/SquarefreeFactorization.lean#L291).
Against that structure,
[`hermiteReduce`](../DeepWiki/SymbolicIntegration/HermiteCompute.lean#L84)
integrates by parts: it peels off an explicit rational
part $g$ and returns a residual whose denominator is squarefree — so everything
left to integrate has only *simple* poles.

Correctness is the defining identity: the integrand is recovered as $D(g)$ plus
the residual, so the reduction loses nothing —
[`hermiteReduce_spec_cnorm`](../DeepWiki/SymbolicIntegration/HermiteCorrectness.lean#L679).

## The logarithmic part (Rothstein–Trager)

What remains is a proper fraction $B/V$ with $V$ squarefree, and by Liouville's
theorem its integral is a sum of logarithms — the only transcendentals an
elementary integral may introduce. Rothstein–Trager pins them down: the residues
are the roots of a resultant, and the argument of each logarithm is a gcd. The
core fact is that the residue of a logarithmic derivative at a root counts that
root's multiplicity —
[`residueAt_logDeriv_eq_rootMultiplicity`](../DeepWiki/SymbolicIntegration/RecognizingLogDeriv.lean#L264).

The Lazard–Rioboo–Trager refinement computes the logarithm arguments through the
subresultant polynomial-remainder sequence, staying inside $K$ instead of
factoring over an algebraic extension. Its correctness is that the PRS output is
*similar* to the gcd it is meant to equal —
[`lazardRiobooTrager_isSimilar_gcd`](../DeepWiki/SymbolicIntegration/LazardRiobooTragerCorrectness.lean#L116).

## Why logarithms are unavoidable

The logarithmic part is genuinely new — it is the derivative of no rational
function. With a squarefree denominator the integral is forced outside $K(x)$ —
[`logPart_not_rational_derivative`](../DeepWiki/SymbolicIntegration/InFieldIntegration.lean#L91).
