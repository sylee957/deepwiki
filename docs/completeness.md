# Completeness

_Completeness_ is the harder direction: when the algorithm reports failure, there
really is no elementary integral. A `none` is a proof of non-elementarity. The
argument is assembled in two layers — a decision procedure for the Risch
differential equation, lifted up the tower, and Liouville's theorem supplying the
structural reason a failure is final — and it is stated modulo exactly the honest
new-monomial side conditions described in the next chapter, and no more.

Throughout, a declaration name links to its definition in the local source tree.

## The decision procedure, lifted up the tower

At the constant base $\mathbb{Q}$ the per-level Risch-DE oracle is complete outright, where
the equation is plain linear algebra —
[`crischFieldComplete_Q`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDECompleteness.lean#L125).
Completeness then propagates one tower level at a time, the base oracle's role at
each step discharged by the level below —
[`crischFieldComplete_step`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDECompleteness.lean#L477).

## Liouville's theorem in the tower

The structural layer. Adjoining a single logarithm preserves the Liouville property
(unconditionally, given the logarithm's new-monomial condition) —
[`isLiouville_logExtension_uncond`](../DeepWiki/SymbolicIntegration/LiouvilleLogExtension.lean#L2052).
Likewise a single exponential —
[`isLiouville_expExtension_uncond`](../DeepWiki/SymbolicIntegration/ComputableLiouvilleExpBridge.lean#L775).
Because the property is preserved at each step, it stacks through a multi-level
tower by transitivity —
[`isLiouville_logTower_two`](../DeepWiki/SymbolicIntegration/ComputableLiouvilleLogTower.lean#L277).

## The payoff: non-elementarity

Combining the layers yields the contrapositive that completeness is really about —
if the integrand has no elementary antiderivative at the base, none appears in the
extension either —
[`not_elementary_logExtension_of_not_elementary_base`](../DeepWiki/SymbolicIntegration/ComputableIntegratorCompleteness.lean#L171).

## The tangent case

The tangent monomial is handled by a separate coupled differential-equation engine,
and its soundness is proved end to end: the Gaussian-elimination system solver
[`cCoupledDESystem_sound_of_check`](../DeepWiki/SymbolicIntegration/ComputableCoupledDE.lean#L484),
and the tangent cancellation, reconstructed by degree-by-degree telescoping,
[`cCoupledDECancelTan_sound_of_check`](../DeepWiki/SymbolicIntegration/ComputableCoupledDE.lean#L844).
