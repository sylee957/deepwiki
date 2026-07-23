import DeepWiki.SymbolicIntegration.DifferentialAlgebra.DerivationExtension

/-! # Fraction-field differential extensions

The quotient-rule extension of a derivation on an integral domain to any fraction field.
-/

open scoped Differential nonZeroDivisors

namespace DeepWiki.SymbolicIntegration

namespace FractionRingDeriv

open IsLocalization

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The quotient-rule value `(q·D(p) - p·D(q))/q²` on a numerator-denominator pair. -/
noncomputable def rawDeriv (D : Derivation ℤ R R) (p : R) (q : R⁰) : K :=
  mk' K ((q : R) * D p - p * D q) (q * q)

/-- Equal fractions give equal quotient-rule values. -/
theorem rawDeriv_wellDefined (D : Derivation ℤ R R) (p₁ p₂ : R) (q₁ q₂ : R⁰)
    (h : mk' K p₁ q₁ = mk' K p₂ q₂) :
    rawDeriv (K := K) D p₁ q₁ = rawDeriv (K := K) D p₂ q₂ := by
  rw [IsLocalization.mk'_eq_iff_eq'] at h
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hcross : p₁ * (q₂ : R) = p₂ * (q₁ : R) := hinj h
  have hD : p₁ * D q₂ + (q₂ : R) * D p₁ = p₂ * D q₁ + (q₁ : R) * D p₂ := by
    have := congrArg D hcross
    simpa only [Derivation.leibniz, smul_eq_mul] using this
  rw [rawDeriv, rawDeriv, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  push_cast
  linear_combination
    (-((q₁ : R) * D q₂ + (q₂ : R) * D q₁)) * hcross + ((q₁ : R) * q₂) * hD

/-- The quotient-rule function on a fraction field, evaluated through a chosen representative. -/
noncomputable def derivFun (D : Derivation ℤ R R) (x : K) : K :=
  rawDeriv D (IsLocalization.sec R⁰ x).1 (IsLocalization.sec R⁰ x).2

/-- `derivFun` computes by the quotient rule on every localization representative. -/
theorem derivFun_mk (D : Derivation ℤ R R) (p : R) (q : R⁰) :
    derivFun (K := K) D (mk' K p q) = rawDeriv D p q := by
  apply rawDeriv_wellDefined
  rw [IsLocalization.mk'_sec]

/-- The raw quotient rule is additive after putting two fractions over a common denominator. -/
theorem rawDeriv_add (D : Derivation ℤ R R) (p₁ p₂ : R) (q₁ q₂ : R⁰) :
    rawDeriv (K := K) D (p₁ * q₂ + p₂ * q₁) (q₁ * q₂) =
      rawDeriv D p₁ q₁ + rawDeriv D p₂ q₂ := by
  rw [rawDeriv, rawDeriv, rawDeriv, ← IsLocalization.mk'_add,
    IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  push_cast
  simp only [map_add, Derivation.leibniz, smul_eq_mul]
  ring

/-- The raw quotient rule satisfies the Leibniz product rule. -/
theorem rawDeriv_mul (D : Derivation ℤ R R) (p₁ p₂ : R) (q₁ q₂ : R⁰) :
    rawDeriv (K := K) D (p₁ * p₂) (q₁ * q₂) =
      mk' K p₁ q₁ * rawDeriv D p₂ q₂ + mk' K p₂ q₂ * rawDeriv D p₁ q₁ := by
  rw [rawDeriv, rawDeriv, rawDeriv, ← IsLocalization.mk'_mul, ← IsLocalization.mk'_mul,
    ← IsLocalization.mk'_add, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  push_cast
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

/-- `derivFun` sends zero to zero. -/
theorem derivFun_zero (D : Derivation ℤ R R) : derivFun (K := K) D 0 = 0 := by
  have h0 : (0 : K) = mk' K 0 (1 : R⁰) := by simp only [IsLocalization.mk'_zero]
  rw [h0, derivFun_mk, rawDeriv, IsLocalization.mk'_eq_iff_eq']
  apply congrArg
  simp

/-- `derivFun` is additive. -/
theorem derivFun_add (D : Derivation ℤ R R) (x y : K) :
    derivFun D (x + y) = derivFun D x + derivFun D y := by
  obtain ⟨⟨p₁, q₁⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
  obtain ⟨⟨p₂, q₂⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ y
  rw [← IsLocalization.mk'_add, derivFun_mk, derivFun_mk, derivFun_mk, rawDeriv_add]

/-- `derivFun` satisfies the Leibniz product rule. -/
theorem derivFun_mul (D : Derivation ℤ R R) (x y : K) :
    derivFun D (x * y) = x * derivFun D y + y * derivFun D x := by
  obtain ⟨⟨p₁, q₁⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
  obtain ⟨⟨p₂, q₂⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ y
  rw [← IsLocalization.mk'_mul, derivFun_mk, derivFun_mk, derivFun_mk, rawDeriv_mul]

/-- The quotient-rule function as an additive homomorphism. -/
noncomputable def addHom (D : Derivation ℤ R R) : K →+ K where
  toFun := derivFun D
  map_zero' := derivFun_zero D
  map_add' := derivFun_add D

/-- The quotient-rule extension of `D` to a fraction field of `R`. -/
noncomputable def deriv (D : Derivation ℤ R R) : Derivation ℤ K K :=
  Derivation.mk' (addHom D).toIntLinearMap fun x y => by
    have h := derivFun_mul (K := K) D x y
    simpa only [AddMonoidHom.coe_toIntLinearMap, addHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      smul_eq_mul] using h

/-- The extended derivation computes by the quotient rule on every representative. -/
@[simp] theorem deriv_mk (D : Derivation ℤ R R) (p : R) (q : R⁰) :
    deriv (K := K) D (mk' K p q) = rawDeriv D p q :=
  derivFun_mk D p q

/-- The quotient-rule derivation restricts to `D` on the image of `R`. -/
theorem deriv_algebraMap (D : Derivation ℤ R R) (p : R) :
    deriv (K := K) D (algebraMap R K p) = algebraMap R K (D p) := by
  have h1 : algebraMap R K p = mk' K p (1 : R⁰) := by rw [IsLocalization.mk'_one]
  rw [h1, deriv_mk, rawDeriv]
  have hnum : ((1 : R⁰) : R) * D p - p * D (1 : R⁰) = D p := by
    rw [show ((1 : R⁰) : R) = 1 from rfl, one_mul, Derivation.map_one_eq_zero,
      mul_zero, sub_zero]
  have hden : ((1 : R⁰) * (1 : R⁰) : R⁰) = (1 : R⁰) := by simp
  rw [hnum, hden, IsLocalization.mk'_one]

/-- The differential structure on a fraction field induced by the quotient rule. -/
@[reducible] noncomputable def differential [Differential R] : Differential K :=
  ⟨deriv (Differential.deriv : Derivation ℤ R R)⟩

/-- The quotient-rule differential structure makes `K` a differential extension of `R`. -/
theorem differentialAlgebra [Differential R] :
    letI := differential (R := R) (K := K)
    DifferentialAlgebra R K := by
  letI := differential (R := R) (K := K)
  exact ⟨deriv_algebraMap (Differential.deriv : Derivation ℤ R R)⟩

end FractionRingDeriv

/-- A derivation on an integral domain extends uniquely to every realization of its fraction field. -/
theorem existsUnique_derivation_fractionRing {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Differential R] :
    ∃! Δ : Derivation ℤ K K,
      ∀ a : R, Δ (algebraMap R K a) = algebraMap R K (a′) := by
  let Δ₀ := FractionRingDeriv.deriv (K := K) (Differential.deriv : Derivation ℤ R R)
  refine ⟨Δ₀, FractionRingDeriv.deriv_algebraMap _, ?_⟩
  intro Δ hΔ
  exact unique_derivation_fractionRing (R := R) hΔ (FractionRingDeriv.deriv_algebraMap _)

/-- A fraction field has a unique differential structure making it a differential extension. -/
theorem existsUnique_differentialAlgebra_fractionRing
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Differential R] :
    ∃! Δ : Differential K, @DifferentialAlgebra R K _ _ _ _ Δ := by
  let Δ₀ := FractionRingDeriv.differential (R := R) (K := K)
  refine ⟨Δ₀, FractionRingDeriv.differentialAlgebra, ?_⟩
  intro Δ hΔ
  apply Differential.ext
  exact unique_derivation_fractionRing (R := R) hΔ.deriv_algebraMap
    (FractionRingDeriv.deriv_algebraMap _)

end DeepWiki.SymbolicIntegration
