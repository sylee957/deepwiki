import DeepWiki.SymbolicIntegration.Core.Differential.DerivationExt
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-! # Basic differential algebra
Basic differential calculus over Mathlib's `Differential` typeclass: the constant subring, the
constant-linearity / quotient / power / chain rules, the logarithmic-derivative identity, and the
module of derivations. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section Ring

/-- The subring of constants `{a ∈ R | a′ = 0}` (the kernel of the derivation). -/
def constants (R : Type*) [CommRing R] [Differential R] : Subring R where
  carrier := {a | a′ = 0}
  zero_mem' := by simp
  one_mem' := (Differential.deriv : Derivation ℤ R R).map_one_eq_zero
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    rw [ha, hb, add_zero]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg] at *
    rw [ha, neg_zero]

/-- Membership in `constants R` is exactly vanishing derivative. -/
@[simp] theorem mem_constants {R : Type*} [CommRing R] [Differential R] {a : R} :
    a ∈ constants R ↔ a′ = 0 := Iff.rfl

/-- `(1 : R)′ = 0`: the derivative of the multiplicative unit vanishes. -/
theorem deriv_one {R : Type*} [CommRing R] [Differential R] : (1 : R)′ = 0 :=
  (Differential.deriv : Derivation ℤ R R).map_one_eq_zero

/-- `(a + b)′ = a′ + b′`: the derivation is additive. -/
theorem deriv_add {R : Type*} [CommRing R] [Differential R] (a b : R) : (a + b)′ = a′ + b′ := by
  simp only [map_add]

/-- Leibniz product rule: `(p·b)′ = p·b′ + b·p′`. -/
theorem deriv_mul_eq {R : Type*} [CommRing R] [Differential R] (p b : R) :
    (p * b)′ = p * b′ + b * p′ := by
  simp only [Derivation.leibniz, smul_eq_mul]

/-- **Constant-linearity**: `(ca)′ = c·a′` for a constant `c` (so `D` is `constants R`-linear). -/
theorem deriv_const_mul {R : Type*} [CommRing R] [Differential R] {c : R} (a : R) (hc : c′ = 0) :
    (c * a)′ = c * a′ := by
  rw [Derivation.leibniz, hc, smul_zero, add_zero, smul_eq_mul]

/-- **Power rule** (natural exponent): `(aⁿ)′ = n·aⁿ⁻¹·a′`. -/
theorem deriv_pow {R : Type*} [CommRing R] [Differential R] (a : R) (n : ℕ) :
    (a ^ n)′ = (n : R) * a ^ (n - 1) * a′ := by
  rw [Derivation.leibniz_pow]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

/-- **Chain rule** (univariate): if every coefficient of `P` is a constant, then
`(P(u))′ = P'(u)·u′`. -/
theorem deriv_eval_of_const_coeffs {R : Type*} [CommRing R] [Differential R]
    (p : R[X]) (u : R) (hp : ∀ i, (p.coeff i)′ = 0) :
    (p.eval u)′ = p.derivative.eval u * u′ := by
  have hmc : (Differential.deriv : Derivation ℤ R R).mapCoeffs p = 0 :=
    PolynomialModule.ext (Finsupp.ext fun i => by
      simp only [Derivation.mapCoeffs_apply, PolynomialModule.coeff_zero,
        Finsupp.zero_apply, hp i])
  rw [Derivation.apply_eval_eq, hmc, map_zero, zero_add, smul_eq_mul]

/-- Multivariate chain rule over the constant subring: `D(P(u)) = ∑ i, (∂P/∂Xᵢ)(u) · D(uᵢ)`. -/
theorem deriv_mveval₂_constants {R σ : Type*} [CommRing R] [Differential R] [Fintype σ]
    (p : MvPolynomial σ (constants R)) (u : σ → R) :
    (MvPolynomial.eval₂ (constants R).subtype u p)′ =
      ∑ i, MvPolynomial.eval₂ (constants R).subtype u (MvPolynomial.pderiv i p) * (u i)′ := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [mem_constants.mp a.property]
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, hp, hq,
      Finset.sum_add_distrib, MvPolynomial.pderiv, add_mul]
  | mul_X p i hp =>
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Derivation.leibniz,
        smul_eq_mul, hp, MvPolynomial.eval₂_add, MvPolynomial.pderiv_X, Pi.single_apply]
      simp [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · simp

example {R : Type*} [CommRing R] [Differential R] {n : ℕ}
    (p : MvPolynomial (Fin n) (constants R)) (u : Fin n → R) :
    (MvPolynomial.eval₂ (constants R).subtype u p)′ =
      ∑ i, MvPolynomial.eval₂ (constants R).subtype u (MvPolynomial.pderiv i p) * (u i)′ :=
  deriv_mveval₂_constants p u

/-- `(c • D₁ + D₂) a = c * D₁ a + D₂ a`: a linear combination of derivations acts pointwise. -/
theorem smul_add_derivation_apply {R : Type*} [CommRing R]
    (c : R) (D₁ D₂ : Derivation ℤ R R) (a : R) :
    (c • D₁ + D₂) a = c * D₁ a + D₂ a := by
  simp [smul_eq_mul]

/-- The module `Derivation ℤ R R` of all derivations `R → R` is a left `R`-module. -/
abbrev derivationModule {R : Type*} [CommRing R] : Module R (Derivation ℤ R R) := inferInstance

end Ring

section Field

/-- **Quotient rule**: `(a/b)′ = (b·a′ − a·b′)/b²` in a differential field. -/
theorem deriv_div {F : Type*} [Field F] [Differential F] (a b : F) :
    (a / b)′ = (b * a′ - a * b′) / b ^ 2 := by
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv, inv_pow]
  ring

/-- **Power rule** (integer exponent, field case): `(aⁿ)′ = n·aⁿ⁻¹·a′`. -/
theorem deriv_zpow {F : Type*} [Field F] [Differential F] (a : F) (n : ℤ) :
    (a ^ n)′ = (n : F) * a ^ (n - 1) * a′ := by
  rw [Derivation.leibniz_zpow]
  simp only [zsmul_eq_mul, smul_eq_mul]
  ring

/-- The logarithmic derivative of a power: `logDeriv (aⁿ) = n · logDeriv a` for integer `n`. -/
theorem logDeriv_zpow {F : Type*} [Field F] [Differential F] (a : F) (n : ℤ) (ha : a ≠ 0) :
    Differential.logDeriv (a ^ n) = (n : F) * Differential.logDeriv a := by
  have hn : (a ^ n) ≠ 0 := zpow_ne_zero _ ha
  simp only [Differential.logDeriv, deriv_zpow, zpow_sub₀ ha, zpow_one]
  field_simp

/-- `logDeriv (a·b) = logDeriv a + logDeriv b`: the logarithmic derivative sends products to sums
(a homomorphism from the multiplicative group to the additive group). -/
theorem logDeriv_mul {F : Type*} [Field F] [Differential F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Differential.logDeriv (a * b) = Differential.logDeriv a + Differential.logDeriv b :=
  Differential.logDeriv_mul a b ha hb

/-- `logDeriv (aⁿ) = n · logDeriv a` for a natural exponent. -/
theorem logDeriv_pow {F : Type*} [Field F] [Differential F] (n : ℕ) (a : F) :
    Differential.logDeriv (a ^ n) = (n : F) * Differential.logDeriv a :=
  Differential.logDeriv_pow n a

/-- `logDeriv (a/b) = logDeriv a − logDeriv b`: the logarithmic derivative sends quotients to
differences. -/
theorem logDeriv_div {F : Type*} [Field F] [Differential F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Differential.logDeriv (a / b) = Differential.logDeriv a - Differential.logDeriv b :=
  Differential.logDeriv_div a b ha hb

/-- `logDeriv a = 0` iff `a` is a constant (`a′ = 0`). -/
theorem logDeriv_eq_zero {F : Type*} [Field F] [Differential F] (a : F) :
    Differential.logDeriv a = 0 ↔ a′ = 0 :=
  Differential.logDeriv_eq_zero a

/-- `logDeriv (∏ uᵢ^{eᵢ}) = ∑ eᵢ · logDeriv uᵢ`: the logarithmic derivative of a product of powers. -/
theorem logDeriv_prod_zpow {F : Type*} [Field F] [Differential F] {ι : Type*}
    (s : Finset ι) (u : ι → F) (e : ι → ℤ) (h : ∀ i ∈ s, u i ≠ 0) :
    Differential.logDeriv (∏ i ∈ s, u i ^ e i)
      = ∑ i ∈ s, (e i : F) * Differential.logDeriv (u i) := by
  rw [Differential.logDeriv_prod _ _ _ (fun i hi => zpow_ne_zero _ (h i hi))]
  exact Finset.sum_congr rfl (fun i hi => logDeriv_zpow (u i) (e i) (h i hi))

/-- Logarithmic-derivative identity for a finite product with integer exponents:
`D(∏ᵢ uᵢ^{eᵢ}) / (∏ᵢ uᵢ^{eᵢ}) = ∑ᵢ eᵢ·(Duᵢ/uᵢ)` — `logDeriv_prod_zpow` in explicit `D(P)/P`
shape. -/
theorem logDeriv_prod_zpow_div {F : Type*} [Field F] [Differential F] {ι : Type*}
    (s : Finset ι) (u : ι → F) (e : ι → ℤ) (h : ∀ i ∈ s, u i ≠ 0) :
    (∏ i ∈ s, u i ^ e i)′ / (∏ i ∈ s, u i ^ e i)
      = ∑ i ∈ s, (e i : F) * ((u i)′ / u i) := by
  have hlhs : Differential.logDeriv (∏ i ∈ s, u i ^ e i)
      = (∏ i ∈ s, u i ^ e i)′ / (∏ i ∈ s, u i ^ e i) := rfl
  rw [← hlhs, logDeriv_prod_zpow s u e h]
  exact Finset.sum_congr rfl fun i _ => by rw [Differential.logDeriv]

end Field

end DeepWiki.SymbolicIntegration
