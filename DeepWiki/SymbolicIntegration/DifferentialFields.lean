import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-! # Differential rings and fields — derivations and their basic calculus
The algebraic foundation of symbolic integration (Ritt's program): a *derivation* on a ring `R`
is a map `D : R → R` with `D(a+b) = Da + Db` and the Leibniz rule `D(ab) = a·Db + b·Da`, defined
purely algebraically — no `function`, `limit`, or `tangent line`. We build on Mathlib's
`Differential` typeclass (`x′` for `D x`, a `Derivation ℤ R R`): the constant subring
`Const_D R`, the constant-linearity / quotient / power / chain rules, the logarithmic-derivative
identity, the `R`-module `Ω(R)` of all derivations, and the notion of a differential ideal. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section Ring
variable {R : Type*} [CommRing R] [Differential R]

/-- The constants `Const_D R = {a ∈ R | Da = 0}`, as a subring of `R`. -/
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

@[simp] theorem mem_constants {a : R} : a ∈ constants R ↔ a′ = 0 := Iff.rfl

/-- **Theorem 3.1.1(i)**: `D(ca) = c·Da` for a constant `c` (`D` is `Const_D R`-linear). -/
theorem deriv_const_mul {c : R} (a : R) (hc : c′ = 0) : (c * a)′ = c * a′ := by
  rw [Derivation.leibniz, hc, smul_zero, add_zero, smul_eq_mul]

/-- **Theorem 3.1.1(iv)** for natural exponents: the power rule `D(aⁿ) = n·aⁿ⁻¹·Da`. -/
theorem deriv_pow (a : R) (n : ℕ) : (a ^ n)′ = (n : R) * a ^ (n - 1) * a′ := by
  rw [Derivation.leibniz_pow]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

/-- **Theorem 3.1.1(vi)** (univariate): if every coefficient of `P` is a constant, then the
chain rule `D(P(u)) = P'(u)·Du` holds. -/
theorem deriv_eval_of_const_coeffs (p : R[X]) (u : R) (hp : ∀ i, (p.coeff i)′ = 0) :
    (p.eval u)′ = p.derivative.eval u * u′ := by
  have hmc : (Differential.deriv : Derivation ℤ R R).mapCoeffs p = 0 :=
    Finsupp.ext fun i => by simp [Derivation.mapCoeffs_apply, hp i, PolynomialModule.zero_apply]
  rw [Derivation.apply_eval_eq, hmc, map_zero, zero_add, smul_eq_mul]

/-- **Definition 3.1.2**: a differential ideal of `(R, D)` is an ideal `I` closed under `D`
(`D I ⊆ I`). -/
def IsDifferentialIdeal (I : Ideal R) : Prop := ∀ a ∈ I, a′ ∈ I

/-- **Theorem 3.1.1(iii)**: the constants `Const_D R` form a *differential subring* of `(R, D)` — the
zero ideal `⊥` is a differential ideal, and `Const_D R` is closed under `D` (trivially: `Da = 0` on it,
and `0 ∈ Const_D R`). -/
theorem isDifferentialIdeal_bot_and_deriv_mem_constants :
    IsDifferentialIdeal (⊥ : Ideal R) ∧ ∀ a ∈ constants R, a′ ∈ constants R := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · simp only [Ideal.mem_bot] at ha ⊢; simp [ha]
  · simp only [mem_constants] at ha ⊢; simp [ha]

omit [Differential R] in
/-- **Lemma 3.1.1** (action): a linear combination of derivations is a derivation —
`(c·D₁ + D₂)` acts pointwise as `a ↦ c·D₁a + D₂a`. The module `Ω(R) = Derivation ℤ R R`
itself is `derivationModule` below. -/
theorem smul_add_derivation_apply (c : R) (D₁ D₂ : Derivation ℤ R R) (a : R) :
    (c • D₁ + D₂) a = c * D₁ a + D₂ a := by
  simp [smul_eq_mul]

/-- **Lemma 3.1.1**: the set `Ω(R)` of all derivations `R → R` is a left `R`-module. -/
abbrev derivationModule : Module R (Derivation ℤ R R) := inferInstance

end Ring

section Field
variable {F : Type*} [Field F] [Differential F]

/-- **Theorem 3.1.1(ii)**: the quotient rule `D(a/b) = (b·Da − a·Db)/b²` in a differential field. -/
theorem deriv_div (a b : F) : (a / b)′ = (b * a′ - a * b′) / b ^ 2 := by
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv, inv_pow]
  ring

/-- **Theorem 3.1.1(iv)** for integer exponents (field case): `D(aⁿ) = n·aⁿ⁻¹·Da`. -/
theorem deriv_zpow (a : F) (n : ℤ) : (a ^ n)′ = (n : F) * a ^ (n - 1) * a′ := by
  rw [Derivation.leibniz_zpow]
  simp only [zsmul_eq_mul, smul_eq_mul]
  ring

/-- The logarithmic derivative of a power: `logDeriv (aⁿ) = n · logDeriv a` for integer `n`. -/
theorem logDeriv_zpow (a : F) (n : ℤ) (ha : a ≠ 0) :
    Differential.logDeriv (a ^ n) = (n : F) * Differential.logDeriv a := by
  have hn : (a ^ n) ≠ 0 := zpow_ne_zero _ ha
  simp only [Differential.logDeriv, deriv_zpow, zpow_sub₀ ha, zpow_one]
  field_simp

/-- **Theorem 3.1.1(v)**: the logarithmic-derivative identity
`D(u₁^{e₁} ⋯ uₙ^{eₙ}) / (u₁^{e₁} ⋯ uₙ^{eₙ}) = e₁·Du₁/u₁ + ⋯ + eₙ·Duₙ/uₙ`, i.e.
`logDeriv (∏ uᵢ^{eᵢ}) = ∑ eᵢ · logDeriv uᵢ`. -/
theorem logDeriv_prod_zpow {ι : Type*} (s : Finset ι) (u : ι → F) (e : ι → ℤ)
    (h : ∀ i ∈ s, u i ≠ 0) :
    Differential.logDeriv (∏ i ∈ s, u i ^ e i)
      = ∑ i ∈ s, (e i : F) * Differential.logDeriv (u i) := by
  rw [Differential.logDeriv_prod _ _ _ (fun i hi => zpow_ne_zero _ (h i hi))]
  exact Finset.sum_congr rfl (fun i hi => logDeriv_zpow (u i) (e i) (h i hi))

end Field

/-- **Theorem 3.2.1** (§3.2), uniqueness: a derivation on a fraction field `K` of an integral
domain `R` is determined by its restriction to `R` — if `Δ₁, Δ₂` agree on `algebraMap R K` then
`Δ₁ = Δ₂`. (Forced by the quotient rule: for `x = a/b`, `Δx = (Δa − x·Δb)/b`.) -/
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

/-- **Theorem 3.2.2** (§3.2), uniqueness (polynomial-ring case): a derivation on `R[X]` is
determined by its values on the constants `C c` and on `X` (`Dt`). So the extension of a
derivation to a monomial `t` with `Dt` prescribed is unique. -/
theorem derivation_polynomial_ext {R : Type*} [CommRing R] {Δ₁ Δ₂ : Derivation ℤ R[X] R[X]}
    (hC : ∀ c : R, Δ₁ (Polynomial.C c) = Δ₂ (Polynomial.C c)) (hX : Δ₁ Polynomial.X = Δ₂ Polynomial.X) :
    Δ₁ = Δ₂ := by
  refine Derivation.ext fun p => ?_
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial n a ih => rw [pow_succ, ← mul_assoc, Δ₁.leibniz, Δ₂.leibniz, ih, hX]

/-- **Theorem 3.2.2** (§3.2), polynomial-ring existence + uniqueness: for `(R, D)` differential and any
target `w : R[X]`, there is a *unique* derivation `Δ` on `R[X]` extending `D` on the constants
(`Δ (C c) = C (Dc)`) and sending `X` to `w` (`Δ X = w`). Existence is `Differential.implicitDeriv w`;
uniqueness is `derivation_polynomial_ext`. -/
theorem existsUnique_derivation_polynomial {R : Type*} [CommRing R] [Differential R] (w : R[X]) :
    ∃! Δ : Derivation ℤ R[X] R[X],
      (∀ c : R, Δ (Polynomial.C c) = Polynomial.C (c′)) ∧ Δ Polynomial.X = w := by
  refine ⟨Differential.implicitDeriv w, ⟨fun c => Differential.implicitDeriv_C w c,
    Differential.implicitDeriv_X w⟩, ?_⟩
  rintro Δ ⟨hC, hX⟩
  exact derivation_polynomial_ext
    (fun c => (hC c).trans (Differential.implicitDeriv_C w c).symm)
    (hX.trans (Differential.implicitDeriv_X w).symm)

end DeepWiki.SymbolicIntegration
