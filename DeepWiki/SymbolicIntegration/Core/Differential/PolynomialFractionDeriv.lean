import Mathlib.Algebra.Polynomial.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-! # Polynomial fraction-field derivations

The quotient-rule extension of a derivation on `F[X]` to any fraction field of `F[X]`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.PolynomialFractionDeriv

section FractionFieldDeriv

open IsLocalization
open scoped nonZeroDivisors

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F[X] K] [IsFractionRing F[X] K]

/-- The raw quotient-rule value on a numerator/denominator pair: `(q * d p - p * d q) / q ^ 2`. -/
noncomputable def rawDeriv (d : Derivation ℤ F[X] F[X]) (p : F[X]) (q : F[X]⁰) : K :=
  mk' K ((q : F[X]) * d p - p * d q) (q * q)

/-- Equal fractions give equal `rawDeriv` values. -/
theorem rawDeriv_well_defined (d : Derivation ℤ F[X] F[X]) (p₁ p₂ : F[X]) (q₁ q₂ : F[X]⁰)
    (h : mk' K p₁ q₁ = mk' K p₂ q₂) :
    rawDeriv (K := K) d p₁ q₁ = rawDeriv (K := K) d p₂ q₂ := by
  rw [IsLocalization.mk'_eq_iff_eq'] at h
  have hinj : Function.Injective (algebraMap F[X] K) := IsFractionRing.injective F[X] K
  have hcross : p₁ * (q₂ : F[X]) = p₂ * (q₁ : F[X]) := hinj h
  have hd : p₁ * d q₂ + (q₂ : F[X]) * d p₁ = p₂ * d q₁ + (q₁ : F[X]) * d p₂ := by
    have := congrArg d hcross
    simpa only [Derivation.leibniz, smul_eq_mul] using this
  rw [rawDeriv, rawDeriv, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  push_cast
  linear_combination
    (-((q₁ : F[X]) * d q₂ + (q₂ : F[X]) * d q₁)) * hcross + ((q₁ : F[X]) * q₂) * hd

/-- The extended derivation's underlying function on `K`, using a canonical representative. -/
noncomputable def fracDerivFun (d : Derivation ℤ F[X] F[X]) (x : K) : K :=
  rawDeriv d (IsLocalization.sec F[X]⁰ x).1 (IsLocalization.sec F[X]⁰ x).2

/-- `fracDerivFun` computes by the raw quotient rule on any representative. -/
theorem fracDerivFun_mk' (d : Derivation ℤ F[X] F[X]) (p : F[X]) (q : F[X]⁰) :
    fracDerivFun (K := K) d (mk' K p q) = rawDeriv d p q := by
  apply rawDeriv_well_defined
  rw [IsLocalization.mk'_sec]

/-- Additivity of the raw quotient rule over a common denominator. -/
theorem rawDeriv_add (d : Derivation ℤ F[X] F[X]) (p₁ p₂ : F[X]) (q₁ q₂ : F[X]⁰) :
    rawDeriv (K := K) d (p₁ * q₂ + p₂ * q₁) (q₁ * q₂)
      = rawDeriv d p₁ q₁ + rawDeriv d p₂ q₂ := by
  rw [rawDeriv, rawDeriv, rawDeriv, ← IsLocalization.mk'_add, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  push_cast
  simp only [map_add, Derivation.leibniz, smul_eq_mul]
  ring

/-- Leibniz product rule for the raw quotient rule. -/
theorem rawDeriv_mul (d : Derivation ℤ F[X] F[X]) (p₁ p₂ : F[X]) (q₁ q₂ : F[X]⁰) :
    rawDeriv (K := K) d (p₁ * p₂) (q₁ * q₂)
      = mk' K p₁ q₁ * rawDeriv d p₂ q₂ + mk' K p₂ q₂ * rawDeriv d p₁ q₁ := by
  rw [rawDeriv, rawDeriv, rawDeriv, ← IsLocalization.mk'_mul, ← IsLocalization.mk'_mul,
    ← IsLocalization.mk'_add, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  push_cast
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

/-- `fracDerivFun` sends `0` to `0`. -/
theorem fracDerivFun_zero (d : Derivation ℤ F[X] F[X]) : fracDerivFun (K := K) d 0 = 0 := by
  have h0 : (0 : K) = mk' K 0 (1 : F[X]⁰) := by simp only [IsLocalization.mk'_zero]
  rw [h0, fracDerivFun_mk', rawDeriv, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  simp

/-- `fracDerivFun` is additive. -/
theorem fracDerivFun_add (d : Derivation ℤ F[X] F[X]) (x y : K) :
    fracDerivFun d (x + y) = fracDerivFun d x + fracDerivFun d y := by
  obtain ⟨⟨p₁, q₁⟩, rfl⟩ := IsLocalization.mk'_surjective F[X]⁰ x
  obtain ⟨⟨p₂, q₂⟩, rfl⟩ := IsLocalization.mk'_surjective F[X]⁰ y
  rw [← IsLocalization.mk'_add, fracDerivFun_mk', fracDerivFun_mk', fracDerivFun_mk', rawDeriv_add]

/-- `fracDerivFun` satisfies the Leibniz product rule. -/
theorem fracDerivFun_mul (d : Derivation ℤ F[X] F[X]) (x y : K) :
    fracDerivFun d (x * y) = x * fracDerivFun d y + y * fracDerivFun d x := by
  obtain ⟨⟨p₁, q₁⟩, rfl⟩ := IsLocalization.mk'_surjective F[X]⁰ x
  obtain ⟨⟨p₂, q₂⟩, rfl⟩ := IsLocalization.mk'_surjective F[X]⁰ y
  rw [← IsLocalization.mk'_mul, fracDerivFun_mk', fracDerivFun_mk', fracDerivFun_mk', rawDeriv_mul]

/-- `fracDerivFun` as an additive homomorphism. -/
noncomputable def fracDerivHom (d : Derivation ℤ F[X] F[X]) : K →+ K where
  toFun := fracDerivFun d
  map_zero' := fracDerivFun_zero d
  map_add' := fracDerivFun_add d

/-- A derivation on `F[X]` extended to a fraction field of `F[X]` by the quotient rule. -/
noncomputable def fracDeriv (d : Derivation ℤ F[X] F[X]) : Derivation ℤ K K :=
  Derivation.mk' (fracDerivHom d).toIntLinearMap (fun a b => by
    have := fracDerivFun_mul (K := K) d a b
    simpa only [AddMonoidHom.coe_toIntLinearMap, fracDerivHom, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, smul_eq_mul] using this)

/-- `fracDeriv` computes by the raw quotient rule on a localization representative. -/
@[simp]
lemma fracDeriv_mk' (d : Derivation ℤ F[X] F[X]) (p : F[X]) (q : F[X]⁰) :
    fracDeriv (K := K) d (mk' K p q) = rawDeriv d p q := fracDerivFun_mk' d p q

/-- `fracDeriv` restricts to `d` on the image of `F[X]`. -/
theorem fracDeriv_algebraMap (d : Derivation ℤ F[X] F[X]) (p : F[X]) :
    fracDeriv (K := K) d (algebraMap F[X] K p) = algebraMap F[X] K (d p) := by
  have h1 : (algebraMap F[X] K p) = mk' K p (1 : F[X]⁰) := by rw [IsLocalization.mk'_one]
  rw [h1, fracDeriv_mk', rawDeriv]
  have hnum : ((1 : F[X]⁰) : F[X]) * d p - p * d (1 : F[X]⁰) = d p := by
    rw [show ((1 : F[X]⁰) : F[X]) = 1 from rfl, one_mul, Derivation.map_one_eq_zero,
      mul_zero, sub_zero]
  have hden : ((1 : F[X]⁰) * (1 : F[X]⁰) : F[X]⁰) = (1 : F[X]⁰) := by simp
  rw [hnum, hden, IsLocalization.mk'_one]

/-- The fraction-field differential structure induced by a differential structure on `F[X]`. -/
@[reducible]
noncomputable def fracDifferential (h : Differential F[X]) : Differential K :=
  letI := h
  ⟨fracDeriv h.deriv⟩

end FractionFieldDeriv

end DeepWiki.SymbolicIntegration.PolynomialFractionDeriv
