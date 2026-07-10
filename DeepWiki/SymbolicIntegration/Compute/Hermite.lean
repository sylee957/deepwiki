import DeepWiki.SymbolicIntegration.Compute.Subresultant
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Computable Hermite reduction over `ℚ`
Specializes the generic tower Hermite reducer to `ℚ[x]` and combines it with `lrtLogPart` for the full
`∫A/D = rational part + log part`. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### Full rational integrator: Hermite rational part + LRT log part -/

/-- Full rational-function integrator `ratIntegrate fuel A D = ((gnum, gden), logpart)`: the Hermite
rational part `gnum/gden` plus the logarithmic part of the residual `∫B/Dstar`, giving
`∫ A/D = gnum/gden + ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`. The rational part is returned as
`Option (DenseFrac ℚ)`, so an unchecked zero denominator cannot escape the computation. -/
def ratIntegrate (fuel : ℕ) (A D : DensePoly ℚ) :
    Option (DenseFrac ℚ) × List (DensePoly ℚ × GBPolyCore ℚ) :=
  let ((gnum, gden), (B, Dstar)) :=
    DensePoly.cHermiteReduceTower ([1] : DensePoly ℚ) A D
  let g := if h : DensePoly.cisZero gden = false then
      some (CFrac.ofFraction gnum gden h : DenseFrac ℚ)
    else none
  (g, lrtLogPart fuel B Dstar)

/-! Correctness is supplied by the generic tower Hermite development in `Engine/Hermite`. -/

end Compute

end DeepWiki.SymbolicIntegration
