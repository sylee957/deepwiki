import DeepWiki.SymbolicIntegration.DifferentialFields
import DeepWiki.SymbolicIntegration.DifferentialAlgebraFacts.LogArctan
import DeepWiki.SymbolicIntegration.DifferentialAlgebraFacts.Rao

/-! # Worked differential-algebra facts

Aggregator for coefficient-lifting derivations, logarithm/arctangent cancellation,
and Rao normal/special polynomials, with verification examples for adjacent differential-field facts.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## Verification examples -/

section Verification

-- The logarithmic derivative of a product of integer powers is the weighted sum of logarithmic derivatives.
example {F : Type*} [Field F] [Differential F] {ι : Type*} (s : Finset ι) (u : ι → F) (e : ι → ℤ)
    (h : ∀ i ∈ s, u i ≠ 0) :
    (∏ i ∈ s, u i ^ e i)′ / (∏ i ∈ s, u i ^ e i) = ∑ i ∈ s, (e i : F) * ((u i)′ / u i) :=
  logDeriv_prod_zpow_div s u e h

-- The logarithm-arctangent combination `t₁·√−1 − 2·t₂` is a `D`-constant.
example {E : Type*} [Field E] [Differential E] [CharZero E] {i u v t₁ t₂ : E} (hi : i ^ 2 = -1)
    (hu : u ^ 2 + 1 ≠ 0) (hv : v = (u + i) / (u - i)) (ht₁ : t₁′ = v′ / v)
    (ht₂ : t₂′ = u′ / (1 + u ^ 2)) : (t₁ * i - 2 * t₂)′ = 0 :=
  deriv_log_arctan_combination_eq_zero hi hu hv ht₁ ht₂

-- The Rao derivation satisfies the Leibniz rule.
example {k : Type*} [Field k] [Differential k] (a b p q : k[X]) :
    bDeriv a b (p * q) = p * bDeriv a b q + q * bDeriv a b p :=
  bDeriv_mul a b p q

-- A product of linear factors is Rao-normal iff every root avoids the special-value equation.
example {k : Type*} [Field k] [Differential k] (a b : k[X]) (s : Finset k) :
    IsNormalRao a b (∏ α ∈ s, (X - C α)) ↔ ∀ α ∈ s, a.eval α ≠ b.eval α * α′ :=
  isNormalRao_prod_X_sub_C_iff a b s

-- A product of linear factors is Rao-special iff every root satisfies the special-value equation.
example {k : Type*} [Field k] [Differential k] (a b : k[X]) (s : Finset k) :
    IsSpecialRao a b (∏ α ∈ s, (X - C α)) ↔ ∀ α ∈ s, a.eval α = b.eval α * α′ :=
  isSpecialRao_prod_X_sub_C_iff a b s

-- A Rao-special prime is coprime to the denominator under a coprime numerator-denominator pair.
example {k : Type*} [Field k] [Differential k] [CharZero k] {a b π : k[X]} (hab : IsCoprime a b)
    (hπ : Prime π) (hsp : IsSpecialRao a b π) : IsCoprime π b :=
  isCoprime_of_isSpecialRao_prime hab hπ hsp

end Verification

end DeepWiki.SymbolicIntegration
