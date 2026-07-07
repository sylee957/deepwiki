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

open Classical in
/-- `(A⁻ⁱ)* · Aᵢ = (A⁻⁽ⁱ⁻¹⁾)*` (`1 ≤ i`): consecutive deflation squarefree parts differ exactly by
the multiplicity-`i` factor `Aᵢ`. -/
theorem squarefreePart_deflation_mul_sqfreeFactPart (A : D[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    squarefreePart (deflation A i) * sqfreeFactPart A i = squarefreePart (deflation A (i - 1)) := by
  have hdisj : Disjoint ((normalizedFactors A.primPart).toFinset.filter
        (fun P => i < (normalizedFactors A.primPart).count P))
      ((normalizedFactors A.primPart).toFinset.filter
        (fun P => (normalizedFactors A.primPart).count P = i)) := by
    rw [Finset.disjoint_left]; intro P h1 h2
    rw [Finset.mem_filter] at h1 h2; omega
  rw [squarefreePart_deflation A i hA, squarefreePart_deflation A (i - 1) hA, sqfreeFactPart,
    ← Finset.prod_union hdisj, ← Finset.filter_or]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro P _
  omega

end SquarefreeParts

end DeepWiki.SymbolicIntegration
