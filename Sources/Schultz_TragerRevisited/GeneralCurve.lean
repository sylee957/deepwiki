import DeepWiki.SymbolicIntegration.ComputableGeneralCurveDecide
import Sources.Schultz_TragerRevisited.Source

/-! # Schultz §4 (general case — infinite places / divisors) — catalog
Pointers to the `DeepWiki.SymbolicIntegration` self-determining decision procedure for elementary
integrability of an algebraic function over an **arbitrary** plane curve: the rational solve, the
principal-log solve, and the `Pic⁰`-torsion decision on the residue divisor (Schultz's general case,
beyond the hyperelliptic special case).

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
The general `Pic⁰`-torsion decision correctness (§4, the residue-divisor order over an arbitrary curve)
  [research]: the deep `GeneralPicTorsionFrontier` (good-reduction torsion bound + the Liouville criterion
  on the residue divisor `δ`) is isolated as a named `Prop` consumed by the decision theorems below, not
  proved.
-/

namespace DeepWiki.Sch

/-- **§4 general-curve integrator** (the self-determining decision): on an arbitrary curve `K(x)[y]/(T)`
with integral basis `basis`, runs the rational solve, then the principal-log solve, then the residue-divisor
`Pic⁰`-torsion decision — returning `some` (elementary) or `none` (not elementary, within the searched
budget). The library's `cIntegrateGeneralCurveDecide`. -/
abbrev generalCurveDecide := @DeepWiki.SymbolicIntegration.cIntegrateGeneralCurveDecide

/-- **§4 soundness** (`some F → D(F) = integrand`): whenever the general-curve integrator returns `some F`,
the output differentiates to the integrand in the carrier quotient — modulo the soundness residual (the
three branch instances of the proven general capstone). The library's `cIntegrateGeneralCurveDecide_sound`. -/
abbrev generalCurveDecide_sound := @DeepWiki.SymbolicIntegration.cIntegrateGeneralCurveDecide_sound

/-- **§4 completeness** (`none → ¬ elementary`): on the non-principal-log path, under the general
`Pic⁰`-torsion frontier, a `none` output certifies the integrand is NOT elementary. The library's
`cIntegrateGeneralCurveDecide_complete`. -/
abbrev generalCurveDecide_complete := @DeepWiki.SymbolicIntegration.cIntegrateGeneralCurveDecide_complete

/-- **★ §4 decision procedure** (`some ↔ elementary`): under the general `Pic⁰`-torsion frontier, the
general-curve integrator returns `some F` for some `F` iff the integrand is elementary — a genuine decision
procedure for elementary integrability over an arbitrary plane curve. The library's
`cIntegrateGeneralCurveDecide_decides`. -/
abbrev generalCurveDecide_decides := @DeepWiki.SymbolicIntegration.cIntegrateGeneralCurveDecide_decides

end DeepWiki.Sch
