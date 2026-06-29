# Soundness

_Soundness_ is the guarantee that the algorithm never lies: whenever it returns an
antiderivative $g$ for an input $f$, that answer is correct, $D(g) = f$. This is
proved _a priori_ — as a theorem about the integration function — not checked after
the fact by re-differentiating a particular output.

Throughout, a declaration name links to its definition in the local source tree.

## The driver

The entire transcendental integrator is one function,
[`cIntegrateGFull`](../DeepWiki/SymbolicIntegration/ComputableTowerRischDE.lean#L681). It
splits the integrand by the canonical normal/special/polynomial decomposition,
sends the polynomial part to the Risch differential-equation oracle, and assembles
the logarithmic part by Rothstein–Trager.

Soundness is then established part by part — each piece of the output is proved to
contribute exactly its share of the integrand.

## The normal part

The Hermite-reduced normal part is the subtle one: its correctness needs the
leftover to be genuinely proper. That degree obstruction is discharged, giving the
primitive normal-part capstone over $\mathbb{Q}(x)(t)$ —
[`cIntegrateGFull_primitive_oneShot_inputProper_qfunNZG`](../DeepWiki/SymbolicIntegration/ComputableOneShotAssembly.lean#L1769).

## The logarithmic part

The logarithmic part's correctness reduces to a clean combinatorial bijection: the
roots of the residue resultant are _exactly_ the Rothstein–Trager residues, so the
logarithms the algorithm emits are precisely the right ones —
[`roots_residueResultantTowerG_eq_residues`](../DeepWiki/SymbolicIntegration/ComputableLogPartTowerSoundness.lean#L104).

## The polynomial part

The polynomial part is itself a Risch differential equation. Its solver is sound as
a literal field identity, and — crucially — independently of the base oracle: the
degree-by-degree subtraction makes the equation exact however the leading
coefficients were chosen —
[`field_identity_of_cPolyRischDEG`](../DeepWiki/SymbolicIntegration/ComputableOneShotSoundness.lean#L321).

In the non-cancellation regime this is the general cleared identity —
[`cPolyRischDENoCancelG_cleared_identity_gen`](../DeepWiki/SymbolicIntegration/ComputableRischDETowerCorrectG.lean#L392).
