import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-! # Derivation extensions

Extensionality and uniqueness principles for derivations on polynomial rings and fraction fields.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- A derivation on a fraction field is determined by its restriction to `R`. -/
theorem derivation_ext_fractionRing {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Δ₁ Δ₂ : Derivation ℤ K K}
    (h : ∀ a : R, Δ₁ (algebraMap R K a) = Δ₂ (algebraMap R K a)) : Δ₁ = Δ₂ := by
  ext x
  obtain ⟨⟨a, b, hb⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hbne : algebraMap R K b ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact nonZeroDivisors.ne_zero hb
  have e1 := congrArg (⇑Δ₁) hx
  have e2 := congrArg (⇑Δ₂) hx
  rw [Derivation.leibniz] at e1 e2
  rw [h b, h a] at e1
  have key : algebraMap R K b • Δ₁ x = algebraMap R K b • Δ₂ x :=
    add_left_cancel (e1.trans e2.symm)
  rw [smul_eq_mul, smul_eq_mul] at key
  exact mul_left_cancel₀ hbne key

/-- A derivation on a fraction field `K` of `R` is unique if it extends the derivation on `R`. -/
theorem unique_derivation_fractionRing {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Differential R] {Δ₁ Δ₂ : Derivation ℤ K K}
    (h₁ : ∀ a : R, Δ₁ (algebraMap R K a) = algebraMap R K (a′))
    (h₂ : ∀ a : R, Δ₂ (algebraMap R K a) = algebraMap R K (a′)) : Δ₁ = Δ₂ :=
  derivation_ext_fractionRing (R := R) fun a => (h₁ a).trans (h₂ a).symm

/-- A compatible differential structure on a fraction field gives the unique extending derivation. -/
theorem existsUnique_derivation_fractionRing_of_differentialAlgebra
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Differential R] [Differential K]
    [DifferentialAlgebra R K] :
    ∃! Δ : Derivation ℤ K K, ∀ a : R, Δ (algebraMap R K a) = algebraMap R K (a′) := by
  refine ⟨Differential.deriv, fun a => ?_, fun Δ hΔ => ?_⟩
  · rw [deriv_algebraMap]
  · exact unique_derivation_fractionRing (R := R) hΔ (fun a => by rw [deriv_algebraMap])

/-- A derivation on `R[X]` is determined by its values on constants and on `X`. -/
theorem derivation_polynomial_ext {R : Type*} [CommRing R] {Δ₁ Δ₂ : Derivation ℤ R[X] R[X]}
    (hC : ∀ c : R, Δ₁ (Polynomial.C c) = Δ₂ (Polynomial.C c))
    (hX : Δ₁ Polynomial.X = Δ₂ Polynomial.X) : Δ₁ = Δ₂ := by
  refine Derivation.ext fun p => ?_
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial n a ih => rw [pow_succ, ← mul_assoc, Δ₁.leibniz, Δ₂.leibniz, ih, hX]

/-- There is a unique derivation on `R[X]` extending `D` on constants and sending `X` to `w`. -/
theorem existsUnique_derivation_polynomial {R : Type*} [CommRing R] [Differential R] (w : R[X]) :
    ∃! Δ : Derivation ℤ R[X] R[X],
      (∀ c : R, Δ (Polynomial.C c) = Polynomial.C (c′)) ∧ Δ Polynomial.X = w := by
  refine ⟨Differential.implicitDeriv w, ⟨fun c => Differential.implicitDeriv_C w c,
    Differential.implicitDeriv_X w⟩, ?_⟩
  rintro Δ ⟨hC, hX⟩
  exact derivation_polynomial_ext
    (fun c => (hC c).trans (Differential.implicitDeriv_C w c).symm)
    (hX.trans (Differential.implicitDeriv_X w).symm)

/-- A derivation on a fraction field of `F[X]` is determined by constants and `X`. -/
theorem unique_derivation_rationalFunction {F K : Type*} [Field F] [Field K] [Algebra F[X] K]
    [IsFractionRing F[X] K] {Δ₁ Δ₂ : Derivation ℤ K K}
    (hC : ∀ c : F, Δ₁ (algebraMap F[X] K (C c)) = Δ₂ (algebraMap F[X] K (C c)))
    (hX : Δ₁ (algebraMap F[X] K X) = Δ₂ (algebraMap F[X] K X)) : Δ₁ = Δ₂ := by
  refine derivation_ext_fractionRing (R := F[X]) fun p => ?_
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Δ₁.leibniz, Δ₂.leibniz, ih, hX]

end DeepWiki.SymbolicIntegration
