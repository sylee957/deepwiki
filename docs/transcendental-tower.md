# The Transcendental Tower

Functions beyond the rational ones are reached by adjoining _monomials_ one at a
time, building a tower of differential field extensions $K(x)(t_1)(t_2)\cdots$.
Each monomial $t_i$ is logarithmic, exponential, or tangent over the field below
it, and is characterized purely by how the derivation acts on it.

Throughout, a declaration name links to its definition in the local source tree.

## The three monomials

A new monomial $t$ over the field $F$ directly below it is fixed entirely by the
single value $D(t)$:

* _logarithmic_: $D(t) = D(u)/u$ for some $u \in F$ (so $t$ "is" $\log u$) —
  here $D(t)$ already lives in $F$, degree $0$ in $t$;
* _exponential_: $D(t) = D(u)\cdot t$ (so $t$ "is" $\exp u$) — degree $1$;
* _tangent_: $D(t) = D(u)\cdot(t^2 + 1)$ (so $t$ "is" $\tan u$) — degree $2$.

The number $\delta = \deg_t D(t)$ — $0$, $1$, or $\ge 2$ — is the one invariant
that drives the algorithm's case split at each level of the tower.

## The polynomial representation

Computing in $F(t)$ starts from polynomials in $t$ over $F$. The engine carries
them in a single generic representation, reused unchanged at every level —
[`CPolyG`](../DeepWiki/SymbolicIntegration/GenericPolyEngine.lean#L152).

## The monomial derivation

Once $D(t)$ is chosen, the derivation extends from $F$ to $F[t]$ by additivity
and the Leibniz rule. The engine computes that extension directly on the
representation —
[`cmonomialDeriv`](../DeepWiki/SymbolicIntegration/ComputableMonomialDeriv.lean#L130).

## The tower as a field

A full element of $F(t)$ is a fraction of such polynomials, kept with a nonzero,
normalized denominator —
[`QFunNZG`](../DeepWiki/SymbolicIntegration/ComputableTowerField.lean#L91).

The decisive property is that this carrier is _itself_ a computable field —
[`instCFieldQFunNZG`](../DeepWiki/SymbolicIntegration/ComputableTowerField.lean#L208). So the
very same engine — polynomials, derivation, fraction field — runs again one level
up, and the construction iterates to arbitrary depth $K(x)(t_1)(t_2)\cdots$.
