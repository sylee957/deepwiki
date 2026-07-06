import DeepWiki.SymbolicIntegration.Compute.Squarefree
import DeepWiki.SymbolicIntegration.Compute.Subresultant

/-! # Computable logarithmic-part assembly
`lrtLogPart` assembles the `(Qᵢ, Sᵢ)` pairs describing `∫A/D` as a sum of logarithms, using
`csqfreeFactor` for the squarefree factorization of the Rothstein-Trager resultant. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-- Logarithmic part of `∫A/D`: `lrtLogPart fuel A D` returns the `(Qᵢ, Sᵢ)` pairs meaning
`∫A/D = ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`, for squarefree `D`. -/
def lrtLogPart (fuel : ℕ) (A D : CPoly) : List (CPoly × BPoly) :=
  let R := rtResultantCompute fuel A D
  (csqfreeFactor fuel R).map (fun (Qi, i) => (Qi, lrtGcdCompute fuel i Qi A D))

end Compute

end DeepWiki.SymbolicIntegration
