import DeepWiki.SymbolicIntegration.Compute.LogToAtan
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtResultant
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant
import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree

/-! # Computable Rothstein–Trager resultant over `ℚ`
A `#eval`-able rendering of the resultant `R(t) = res_x(D, A − t·D')` on the carrier
`DensePoly ℚ := List ℚ`: the fuel-free `DensePoly.cresultantWf`, followed by
`R(t)` recovered by evaluation and Lagrange interpolation (`cinterpolate`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-- Constant `DensePoly ℚ` `cC c = [c]`, normalized to `[]` when `c = 0`. -/
def cC (c : ℚ) : DensePoly ℚ := cnorm [c]

/-! ### The Rothstein–Trager resultant `R(t) = res_x(D, A − t·D')` -/

/-- Computable Rothstein–Trager resultant `rtResultantCompute A D = R(t) = res_x(D, A − t·D')`,
returned as a `DensePoly ℚ` in `t`, computed by sampling and Lagrange interpolation. -/
def rtResultantCompute (A D : DensePoly ℚ) : DensePoly ℚ :=
  let D' := cderiv D
  let n := cdeg D  -- `deg_t R ≤ deg_x D = n`, so `n + 1` sample points determine `R`.
  let pts : List (ℚ × ℚ) := (List.range (n + 1)).map (fun k =>
    let a : ℚ := (k : ℚ)
    let Aa := csub A (cscale a D')
    (a, DensePoly.cresultantWf D Aa))
  DensePoly.cinterpolate pts

/-! ### Bridge back to `ℚ[X]`

`DensePoly.cresultantWf` agrees with Mathlib's `Polynomial.resultant`, and
`toPoly (rtResultantCompute …)` agrees with the noncomputable `rtResultant`, in the correctness
files for those algorithms. -/

end Compute

end DeepWiki.SymbolicIntegration
