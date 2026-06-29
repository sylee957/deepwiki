import VersoManual

-- Real declarations from the library, imported so the prose can render them inline.
import DeepWiki.SymbolicIntegration.HermiteCompute
import DeepWiki.SymbolicIntegration.HermiteCorrectness
import DeepWiki.SymbolicIntegration.LazardRiobooTragerCorrectness
import DeepWiki.SymbolicIntegration.RecognizingLogDeriv
import DeepWiki.SymbolicIntegration.InFieldIntegration

open Verso.Genre Manual
open DeepWiki.SymbolicIntegration Compute

/-! Rational-case chapter — Hermite reduction and Rothstein–Trager, backed by the
real formalized routines (rendered inline via `{docstring …}`). -/

#doc (Manual) "The Rational Case" =>

Integrating a rational function $`f \in K(x)` is the base case, and it always
succeeds: every rational function has an elementary integral — a rational part
plus a sum of logarithms. The method has two stages, _Hermite reduction_ and the
_Rothstein–Trager_ logarithmic part, and it is the template the transcendental
tower later imitates one monomial at a time.

The declarations below are not paraphrases: they are the actual Lean routines and
correctness theorems from the DeepWiki library, rendered with their machine-checked
signatures.

# Hermite reduction

The first stage removes the _repeated_ poles. Writing $`f = P + A/D` with $`D`
squarefree-factored as $`\prod_i D_i^{\,i}`, {InlineLean.name}`hermiteReduce`
integrates by parts against that structure: it peels off an explicit rational part
$`g` and returns a residual whose denominator is squarefree — so everything left
to integrate has only _simple_ poles.

{docstring hermiteReduce}

Correctness is the defining identity — the integrand is recovered as $`D(g)` plus
the residual, so the reduction loses nothing:

{docstring hermiteReduce_spec_cnorm}

# The logarithmic part (Rothstein–Trager)

What remains is a proper fraction $`B/V` with $`V` squarefree, and by Liouville's
theorem its integral is a sum of logarithms — the only transcendentals an
elementary integral may introduce. Rothstein–Trager pins them down: the residues
are the roots of a resultant, and the argument of each logarithm is a gcd. The
core fact is that the residue of a logarithmic derivative at a root counts that
root's multiplicity:

{docstring residueAt_logDeriv_eq_rootMultiplicity}

The Lazard–Rioboo–Trager refinement computes the logarithm arguments through the
subresultant polynomial-remainder sequence, staying inside $`K` instead of
factoring over an algebraic extension. Its correctness is that the PRS output is
_similar_ to the gcd it is meant to equal:

{docstring lazardRiobooTrager_isSimilar_gcd}

# Why logarithms are unavoidable

The logarithmic part is genuinely new — it is the derivative of no rational
function. With a squarefree denominator the integral is forced outside $`K(x)`:

{docstring logPart_not_rational_derivative}
