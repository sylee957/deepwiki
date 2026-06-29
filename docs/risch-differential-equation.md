# The Risch Differential Equation

Lifting integration up one level of the tower reduces to solving the _Risch
differential equation_ (RDE): given $f$ and $g$ in a differential field, find $y$
in that field with $D(y) + f\,y = g$, or prove that no such $y$ exists. This is the
engine that drives the recursion through the monomial extensions: integrating in
$F(t)$ repeatedly hands a coefficient-level problem down to an RDE over $F$.

Throughout, a declaration name links to its definition in the local source tree.

## Why integration becomes an RDE

Take an exponential monomial, $D(t) = D(u)\,t$, and a candidate antiderivative
written one power of $t$ at a time, $\int f = \sum_k y_k\,t^k$. Differentiating and
matching the coefficient of $t^k$ turns $D(\sum_k y_k t^k) = f$ into a family of
equations of the shape $D(y_k) + (k\,D(u))\,y_k = (\text{known})$ — each one an RDE
in the coefficient field $F$, with $f = k\,D(u)$. So solving an integral one tower
level up is exactly solving RDEs one level down, and the recursion bottoms out at
the constant base where the equation is linear algebra. The RDE solver is therefore
what the soundness and completeness results are ultimately about.

## The denominator: normal and special parts

The first move is to clear denominators in a controlled way. The denominator of a
fraction in $F(t)$ splits into a _normal_ part (whose irreducible factors stay
squarefree under $D$) and a _special_ part (the factors $D$ can collapse). The
special factor is dictated by the monomial: $t^2+1$ for a tangent, $t$ for an
exponential, and trivial for a logarithm — read off the monomial derivation by
[`cSpecialPolyG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L186).

Before the split can be exploited, $f$ must be _weakly normalized_ — its
denominator made equal to its own normal part, so the residue obstruction at each
special pole is exhausted. The engine computes the polynomial $q$ with $f - D(q)/q$
weakly normalized by
[`cWeakNormalizerG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L118),
which inspects the roots of a residue resultant and multiplies out exactly the
poles with a positive-integer residue. The normalized input is then
$\tilde f = f - D(q)/q$, formed as
[`weakNormalizedF`](../DeepWiki/SymbolicIntegration/ComputableRischDESolveNorm.lean#L114).

With $\tilde f$ in hand, the two denominator reductions strip the equation down to a
purely polynomial one:

- the _normal_ reduction
  [`cRdeNormalDenominatorG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L148)
  rewrites $D(y) + \tilde f\,y = g$ so that every solution $y$ has $q = y\,h$
  satisfying a cleared equation $a\,D(q) + b\,q = c$ over $F[t]$ (returning `none`
  when a divisibility test fails, i.e. there is no solution);
- the _special_ reduction
  [`cRdeSpecialDenominatorG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L203)
  clears the remaining special factor $p$, producing
  $\bar a\,D(r) + \bar b\,r = \bar c$ for a genuine polynomial $r = q\,h$.

## The degree bound

A polynomial equation $a\,D(q) + b\,q = c$ has solutions of bounded degree, and the
bound depends only on $\delta = \deg_t D(t)$ — the same invariant that classifies
the monomial. The engine computes it directly from the degrees of $a$, $b$, $c$ and
$\delta$ by
[`cRdeBoundDegreeG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L237):
in the nonlinear case ($\delta \ge 2$, tangent) the bound is
$\max(0,\, d_c - \max(d_a + \delta - 1,\, d_b))$, in the exponential case
($\delta = 1$) $\max(0,\, d_c - \max(d_b, d_a))$, and in the primitive case
($\delta = 0$) it is read off $d_b$ versus $d_a$. A finite degree bound is what
makes the polynomial solve a terminating search rather than an open one.

## The three regimes

With the equation reduced to $D(q) + b\,q = c$ and a degree bound $n$ in hand, how
$q$ is found depends on whether the leading terms of $D(q)$ and $b\,q$ cancel — and
that, again, is governed by $\delta$ and $\deg b$. The dispatcher
[`cPolyRischDEG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L432) routes
to one of three solves:

- **non-cancellation** — when $\deg b > \max(0, \delta - 1)$ the top terms do not
  cancel, so the leading coefficient of $q$ is forced outright,
  $\mathrm{lc}(q) = \mathrm{lc}(c)/\mathrm{lc}(b)$; subtract its contribution and
  recurse on a strictly lower-degree remainder. This is
  [`cPolyRischDENoCancelG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L298);
- **primitive cancellation** — when $\delta = 0$ and $\deg b = 0$, $D$ does not
  raise the $t$-degree, so the leading terms _do_ cancel and the next coefficient is
  fixed by an RDE one level down in the coefficient field $F$ itself,
  $D(s) + b_0\,s = \mathrm{lc}(c)$. This recursive descent is
  [`cPolyRischDECancelPrimG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L337) —
  the point at which the tower recursion ties back into the same solver one level
  below;
- **hyperexponential cancellation** — when $\delta = 1$ and $\deg b = 0$, the
  $t^m$ factor contributes an extra $m\,\eta$ (with $\eta = D(t)/t \in F$) to the
  coefficient, so the descended RDE is $D(s) + (b_0 + m\,\eta)\,s = \mathrm{lc}(c)$,
  solved by
  [`cPolyRischDECancelExpG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L376).

When $b = 0$ the equation is the pure integration $D(q) = c$, handled termwise in
the primitive base. Assembling the weak normalization, the two denominator
reductions, the degree bound, and the three regimes gives the per-level RDE solver
[`cRischDEG`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L466).

## The corrected solver

Stacked over the tower carrier `QFunNZG β`, the field-level solver is
[`crischDESolveSound`](../DeepWiki/SymbolicIntegration/ComputableRischDESolveSound.lean#L165).
It weak-normalizes the input, runs the solvability check that the raw oracle omits —
returning `none` when a non-positive-integer-residue special pole survives (an
unsolvable RDE) — and only then reduces to lowest terms and hands off to the inner
solve. That extra check is exactly what makes "the solver returned an answer" imply
"the answer is correct", with no hypothesis carried in from outside.

## Unconditional soundness

The capstone
[`crischDESolveSound_field`](../DeepWiki/SymbolicIntegration/ComputableRischDESolveSound.lean#L284)
states that whenever the solver returns an answer, that answer really solves the
original field-level Risch differential equation: the conclusion is the literal
identity $D(Y) + F\cdot Y = G$ over the rational-function field, with _no_
`IsCanonNormalized` hypothesis — the solver's own check supplies it.

## A decision procedure

Soundness is one half; the full statement is that the solver _decides_ RDE
solvability. The procedure returns `some` exactly when the field-level equation
$D(Y) + F\cdot Y = G$ has a solution —
[`crischDESolveSound_isDecisionProcedure`](../DeepWiki/SymbolicIntegration/ComputableRischDEDecisionProcedure.lean#L182) —
with the forward (soundness) half unconditional and the converse modulo the three
precisely named §6 completeness residuals. This decision procedure for the RDE one
level up is the recursive heart of the completeness argument, lifted level by level
in the next chapters.
