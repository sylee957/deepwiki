import DeepWiki.SymbolicIntegration.AlgebraicConstants

/-! # Coefficient-lifting derivation

The derivation `κ_D` on `R[t]` induced by differentiating coefficients and fixing `t`.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section KappaD
variable {R : Type*} [CommRing R] [Differential R]

/-- The coefficient-lifting map `κ_D : R[t] → R[t]`, `κ_D(∑ aᵢ tⁱ) = ∑ (Daᵢ) tⁱ`, is a
derivation (Mathlib's `Differential.mapCoeffs`); it is the extension of `D` to `R[t]` with `Dt = 0`. -/
noncomputable def kappaD (R : Type*) [CommRing R] [Differential R] : Derivation ℤ R[X] R[X] :=
  Differential.mapCoeffs

@[simp] theorem kappaD_coeff (p : R[X]) (i : ℕ) : (kappaD R p).coeff i = (p.coeff i)′ :=
  Differential.coeff_mapCoeffs p i

@[simp] theorem kappaD_X : kappaD R (X : R[X]) = 0 := Differential.mapCoeffs_X

@[simp] theorem kappaD_C (x : R) : kappaD R (C x) = C x′ := Differential.mapCoeffs_C x

/-- `κ_D` is additive (the derivation property): `κ_D(p + q) = κ_D p + κ_D q`. -/
theorem kappaD_add (p q : R[X]) : kappaD R (p + q) = kappaD R p + kappaD R q := map_add _ _ _

/-- `κ_D` satisfies the Leibniz rule: `κ_D(p·q) = p·κ_D q + q·κ_D p`. -/
theorem kappaD_mul (p q : R[X]) : kappaD R (p * q) = p * kappaD R q + q * kappaD R p := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

end KappaD

end DeepWiki.SymbolicIntegration
