import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # Polynomial squarefree deflations

Core definitions for squarefree parts and multiplicity deflations of primitive polynomial factors.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section Deflation
open UniqueFactorizationMonoid
variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D]

open Classical in
/-- Squarefree part `A* = ∏ Pᵢ`: the product of the distinct normalized prime factors of the
primitive part `pp(A)`. -/
noncomputable def squarefreePart (A : D[X]) : D[X] :=
  ∏ P ∈ (normalizedFactors A.primPart).toFinset, P

open Classical in
/-- `k`-deflation `A⁻ᵏ = ∏ Pᵢ^max(0, eᵢ−k)`: the primitive part with each factor exponent
truncated by `k`. -/
noncomputable def deflation (A : D[X]) (k : ℕ) : D[X] :=
  ∏ P ∈ (normalizedFactors A.primPart).toFinset, P ^ ((normalizedFactors A.primPart).count P - k)

end Deflation

end DeepWiki.SymbolicIntegration
