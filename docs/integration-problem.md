# The Integration Problem and Liouville's Theorem

To integrate a function "in closed form" is to find an antiderivative among the
_elementary_ functions, or to prove that none exists. This chapter makes that
precise and states the single theorem — Liouville's — that turns it into a problem
a machine can decide; the later chapters are how that decision procedure is built
and proved.

## Elementary functions

Start from a base differential field — for us the rational functions $\mathbb{Q}(x)$
with $D = d/dx$ from the previous chapter. A function is _elementary_ over the base
if it is reached by a finite tower of field extensions
$F_0 \subseteq F_1 \subseteq \cdots \subseteq F_n$, with $F_0$ the base and each
step $F_{i+1} = F_i(t)$ adjoining a single new element $t$ of one of these kinds:

- a _logarithm_: $D(t) = D(u)/u$ for some $u \in F_i$ — written $t = \log u$;
- an _exponential_: $D(t)/t = D(u)$ for some $u \in F_i$ — written $t = \exp u$;
- a _tangent_: $D(t) = D(u)\,(t^2 + 1)$ for some $u \in F_i$ — written $t = \tan u$.

These are the _transcendental_ monomials — towers of logarithms, exponentials, and
tangents — and they are what the chapters through Completeness build. The remaining
kind of extension adjoins an _algebraic_ $t$ (a root of a polynomial over $F_i$,
such as $\sqrt{x^3+1}$); it completes the definition of "elementary" and is
developed in [Integrating Algebraic Functions](algebraic-functions.md). The
_integration problem_ is then: given $f$ somewhere in such a tower, produce an
elementary $g$ with $D(g) = f$, or prove that no elementary $g$ exists.

## Liouville's theorem

"All elementary functions" is an unbounded search space, so deciding the problem by
trying candidates is hopeless. Liouville's theorem collapses the space to a finite
shape. In differential-algebra form: if $f \in F$ has an antiderivative that is
elementary over $F$, then it already has one expressible inside $F$ itself,

$$ f = D(v) + \sum_i c_i\,\frac{D(u_i)}{u_i}, $$

with $v \in F$, each $c_i$ a constant, and each $u_i \in F$ (after adjoining
finitely many constants) — equivalently $\int f = v + \sum_i c_i \log u_i$. The
statement is sharp: the only _new_ transcendentals an elementary integral may
introduce are logarithms, and their arguments $u_i$ together with the rational part
$v$ stay in the field you began in.

_In the formalization_, this is the bridge from "the algorithm found nothing" to
"no elementary integral exists." Mathlib provides the abstract property
`IsLiouville` (and its algebraic case); the engine supplies the transcendental
instances the algorithm relies on — the single-step logarithmic extension
[`isLiouville_logExtension_uncond`](../DeepWiki/SymbolicIntegration/LiouvilleLogExtension.lean#L2052)
and the exponential extension
[`isLiouville_expExtension_uncond`](../DeepWiki/SymbolicIntegration/ComputableLiouvilleExpBridge.lean#L775)
— and stacks them through a multi-level tower.

Both instances reward reading once, because the _type_ already encodes the whole
claim:

```lean
theorem isLiouville_logExtension_uncond (u : F) (hnd : NondegenerateLog u) :
    letI := logDifferential u         -- adjoin t = log u: RatFunc F becomes a differential field, t′ = u′/u
    letI := logDifferentialAlgebra u  -- and F ⊆ RatFunc F is a differential-field extension
    IsLiouville F (RatFunc F)
```

Reading left to right: `u : F` is the argument of the new logarithm, and
`RatFunc F` — the rational functions in one indeterminate over $F$ — _is_ the
extension $F(\log u)$, with the indeterminate $t$ playing the role of $\log u$. The
two `letI`s are what turn the bare field `RatFunc F` into a _differential_ extension
of $F$: the first fixes the derivation by $t' = u'/u$ (the defining equation of a
logarithm), the second records that $F$ sits inside compatibly. The single
hypothesis `NondegenerateLog u` is exactly the Risch _new-monomial condition_,
$\log u \notin F$ — $t$ is genuinely transcendental and new; it is necessary (drop
it, $t$ collapses into $F$, and the statement is false). The conclusion
`IsLiouville F (RatFunc F)` is Liouville's theorem _for this one step_: every
$f \in F$ whose antiderivative is elementary over $F(\log u)$ already has the
Liouville form $D(v) + \sum_i c_i\,D(u_i)/u_i$ with everything back in $F$.

The exponential instance
[`isLiouville_expExtension_uncond`](../DeepWiki/SymbolicIntegration/ComputableLiouvilleExpBridge.lean#L775)
is identical in shape — its `letI` fixes $t' = u'\,t$ instead, and the hypothesis
`NondegenerateExp u` reads $\exp(k u) \notin F$ for every $k \neq 0$ — so the two
together cover both transcendental monomials. Because `IsLiouville` _composes_
across extensions, chaining these single steps is exactly what carries Liouville's
theorem up the whole tower.

## Why it is the foundation

Liouville turns an open-ended search into a structured one: to integrate $f$, it is
enough to look for one field element $v$ and a finite sum of constant multiples of
logarithms of the shape above. If that structured search provably fails, Liouville
guarantees that no elementary integral exists at all — and a search that always
succeeds or provably fails is exactly a decision procedure. Every later chapter
carries out a piece of that search by computation: the rational case finds $v$ and
the logarithms when the field is $\mathbb{Q}(x)$; the Risch differential equation
finds them one tower level up; the soundness chapter proves a returned $g$ really
satisfies $D(g) = f$; and the completeness chapter proves a failure is final,
resting on the Liouville instances named above.
