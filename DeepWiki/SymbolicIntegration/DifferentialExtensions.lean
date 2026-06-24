import DeepWiki.SymbolicIntegration.DifferentialFields
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Galois.Basic

/-! # Existence and uniqueness of derivation extensions (Bronstein §3.2)
Extending a derivation `D` from a base field to a larger ring or field. A derivation on an
integral domain extends *uniquely* to its quotient field by the quotient rule; a transcendental
extension `F(t)` extends in many ways, one per choice of `Dt`; a *separable algebraic* extension
`E ⊇ F` extends *uniquely*, with `Dα = −κ_D(p)(α)/p'(α)` forced by the minimal polynomial `p`.
In characteristic `0` (our setting) every algebraic extension is separable, and Mathlib already
builds the unique finite-extension derivation via this very formula
(`Differential.differentialFiniteDimensional`, the `AdjoinRoot` instance). We package those as the
§3.2 theorems and add the trace/norm transport: a field automorphism commutes with `D`, hence the
trace commutes with `D` and `Tr(Da/a) = D(N a)/N a`. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section FractionField
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Differential R]

/-- **Theorem 3.2.1** (§3.2), uniqueness clause: a derivation on the fraction field `K` of an
integral domain `R` that extends `D` on `R` (`Δ (algebraMap R K a) = algebraMap R K (Da)`) is
unique. (Forced by the quotient rule `Δ(a/b) = (b·Da − a·Db)/b²`.) Existence — when a compatible
`Differential K` is available — is `existsUnique_derivation_fractionRing`. -/
theorem unique_derivation_fractionRing {Δ₁ Δ₂ : Derivation ℤ K K}
    (h₁ : ∀ a : R, Δ₁ (algebraMap R K a) = algebraMap R K (a′))
    (h₂ : ∀ a : R, Δ₂ (algebraMap R K a) = algebraMap R K (a′)) : Δ₁ = Δ₂ :=
  derivation_ext_fractionRing (R := R) fun a => (h₁ a).trans (h₂ a).symm

/-- **Theorem 3.2.1** (§3.2), existence + uniqueness: if the fraction field `K` carries a
differential structure compatible with `D` (`DifferentialAlgebra R K`), then the extending
derivation on `K` is the *unique* one with `Δ (algebraMap R K a) = algebraMap R K (Da)`. So a
derivation on an integral domain extends uniquely to its quotient field. -/
theorem existsUnique_derivation_fractionRing [Differential K] [DifferentialAlgebra R K] :
    ∃! Δ : Derivation ℤ K K, ∀ a : R, Δ (algebraMap R K a) = algebraMap R K (a′) := by
  refine ⟨Differential.deriv, fun a => ?_, fun Δ hΔ => ?_⟩
  · rw [deriv_algebraMap]
  · exact unique_derivation_fractionRing (R := R) hΔ (fun a => by rw [deriv_algebraMap])

end FractionField

end DeepWiki.SymbolicIntegration
