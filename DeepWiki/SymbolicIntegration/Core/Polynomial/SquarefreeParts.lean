import DeepWiki.SymbolicIntegration.Core.Polynomial.SquarefreeDeflation

/-! # Polynomial squarefree-factorization parts

Multiplicity-indexed squarefree factors of primitive polynomial parts.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section SquarefreeParts
open UniqueFactorizationMonoid
variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D]

open Classical in
/-- Squarefree-factorization part `Aᵢ = ∏_{eₚ = i} P`: the product of the prime factors of `pp(A)`
of multiplicity exactly `i`. -/
noncomputable def sqfreeFactPart (A : D[X]) (i : ℕ) : D[X] :=
  ∏ P ∈ (normalizedFactors A.primPart).toFinset.filter
    (fun P => (normalizedFactors A.primPart).count P = i), P

end SquarefreeParts

end DeepWiki.SymbolicIntegration
