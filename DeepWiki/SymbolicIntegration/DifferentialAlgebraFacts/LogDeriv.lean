import DeepWiki.SymbolicIntegration.AlgebraicConstants

/-! # Logarithmic derivative of a finite product

The explicit quotient form of the finite-product logarithmic derivative identity.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section LogDerivIdentity
variable {F : Type*} [Field F] [Differential F]

/-- Logarithmic-derivative identity for a finite product with integer exponents:
`D(∏ᵢ uᵢ^{eᵢ}) / (∏ᵢ uᵢ^{eᵢ}) = ∑ᵢ eᵢ·(Duᵢ/uᵢ)` — `logDeriv_prod_zpow` in explicit `D(P)/P`
shape. -/
theorem logDeriv_prod_zpow_div {ι : Type*} (s : Finset ι) (u : ι → F) (e : ι → ℤ)
    (h : ∀ i ∈ s, u i ≠ 0) :
    (∏ i ∈ s, u i ^ e i)′ / (∏ i ∈ s, u i ^ e i)
      = ∑ i ∈ s, (e i : F) * ((u i)′ / u i) := by
  have hlhs : Differential.logDeriv (∏ i ∈ s, u i ^ e i)
      = (∏ i ∈ s, u i ^ e i)′ / (∏ i ∈ s, u i ^ e i) := rfl
  rw [← hlhs, logDeriv_prod_zpow s u e h]
  exact Finset.sum_congr rfl fun i _ => by rw [Differential.logDeriv]

end LogDerivIdentity

end DeepWiki.SymbolicIntegration
