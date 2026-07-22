import DeepWiki.SymbolicIntegration.DifferentialAlgebra.Ideals

/-! # Polynomial implicit derivation
Concrete instances of the differential-field machinery: the induced derivation
`Δ = κ_D + X·d/dX` on `R[X]` and its restriction to the substitution quotient `R[X]/(X) ≃ R`,
and the differential ideals `(X^m)`. -/

open scoped Differential
open Polynomial

namespace ImplicitDiffX

/-- The opt-in differential structure `Δ = κ_D + X·d/dX` on `R[X]`. -/
noncomputable scoped instance {R : Type*} [CommRing R] [Differential R] : Differential R[X] :=
  ⟨Differential.implicitDeriv X⟩

end ImplicitDiffX

namespace DeepWiki.SymbolicIntegration

section PolynomialDerivation
variable {R : Type*} [CommRing R] [Differential R]
open scoped ImplicitDiffX

/-- The induced derivation `Δ = κ_D + X·d/dX` on `R[X]` (`Differential.implicitDeriv X`, the
unique derivation extending `D` with `Δ X = X`) acts on a monomial by
`Δ(a·Xⁿ) = (Da + n·a)·Xⁿ`. -/
theorem implicitDeriv_X_monomial (n : ℕ) (a : R) :
    Differential.implicitDeriv (X : R[X]) (Polynomial.monomial n a)
      = Polynomial.monomial n (a′ + n * a) := by
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Differential.mapCoeffs_monomial, Derivation.smul_apply,
    Derivation.restrictScalars_apply, Polynomial.derivative'_apply, Polynomial.derivative_monomial,
    smul_eq_mul]
  rw [Polynomial.X_mul, ← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_mul_monomial]
  rcases n with _ | m
  · simp
  · rw [Nat.add_sub_cancel, ← (Polynomial.monomial (m + 1)).map_add]
    congr 1
    push_cast
    ring

/-- `(Δ p).coeff 0 = (p.coeff 0)′` for `Δ = Differential.implicitDeriv X`: on the substitution
quotient `R[X]/(X) ≃ R` (the substitution `X ↦ 0`) the induced derivation equals `D`. -/
theorem implicitDeriv_X_coeff_zero (p : R[X]) :
    (Differential.implicitDeriv (X : R[X]) p).coeff 0 = (p.coeff 0)′ := by
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Polynomial.coeff_add, Differential.coeff_mapCoeffs,
    Derivation.smul_apply, Derivation.restrictScalars_apply, Polynomial.derivative'_apply,
    smul_eq_mul, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero]
  ring

/-- The differential ideal `(X^m)` for `Differential.implicitDeriv X`. -/
noncomputable def implicitDerivXSpanXPow (m : ℕ) : DifferentialIdeal R[X] where
  toIdeal := Ideal.span {X ^ m}
  deriv_mem' := by
    change ∀ p ∈ Ideal.span ({X ^ m} : Set R[X]),
      Differential.implicitDeriv X p ∈ Ideal.span ({X ^ m} : Set R[X])
    have hcalc := implicitDeriv_X_monomial (R := R) m 1
    have hpow : ((X : R[X]) ^ m) ∣ Differential.implicitDeriv X (X ^ m) := by
      refine ⟨Polynomial.C (m : R), ?_⟩
      rw [← Polynomial.monomial_one_right_eq_X_pow, hcalc]
      rw [deriv_one, zero_add, mul_one, Polynomial.monomial_mul_C, one_mul]
    intro p hp
    rw [Ideal.mem_span_singleton] at hp ⊢
    obtain ⟨b, rfl⟩ := hp
    rw [Derivation.leibniz]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hpow b)

/-- The evaluation-at-zero differential ideal `(X)`. -/
noncomputable abbrev implicitDerivXSpanX : DifferentialIdeal R[X] where
  toIdeal := Ideal.span {X - C 0}
  deriv_mem' := by
    simpa [implicitDerivXSpanXPow] using (implicitDerivXSpanXPow (R := R) 1).deriv_mem'

/-- The derivation on `R[X] ⧸ (X)` induced by `Differential.implicitDeriv X`. -/
noncomputable def implicitDeriv_X_quotientDerivation :
    Derivation ℤ (R[X] ⧸ Ideal.span ({X - C 0} : Set R[X]))
      (R[X] ⧸ Ideal.span ({X - C 0} : Set R[X])) :=
  implicitDerivXSpanX.quotientDerivation

/-- The induced quotient derivation sends the class of `p` to the class of `Δp`. -/
@[simp] theorem implicitDeriv_X_quotientDerivation_mk (p : R[X]) :
    implicitDeriv_X_quotientDerivation
        (Ideal.Quotient.mk (Ideal.span ({X - C 0} : Set R[X])) p) =
      Ideal.Quotient.mk (Ideal.span ({X - C 0} : Set R[X]))
        (Differential.implicitDeriv X p) := by
  unfold implicitDeriv_X_quotientDerivation
  exact DifferentialIdeal.quotientDerivation_mk _ p

/-- Under `R[X] ⧸ (X) ≃ R`, the quotient derivation induced by
`Differential.implicitDeriv X` agrees with `D`. -/
theorem implicitDeriv_X_quotientSpanX_apply
    (x : R[X] ⧸ Ideal.span ({X - C 0} : Set R[X])) :
    Polynomial.quotientSpanXSubCAlgEquiv 0
        (implicitDeriv_X_quotientDerivation x) =
      (Polynomial.quotientSpanXSubCAlgEquiv 0 x)′ := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [implicitDeriv_X_quotientDerivation_mk,
    Polynomial.quotientSpanXSubCAlgEquiv_mk,
    Polynomial.quotientSpanXSubCAlgEquiv_mk]
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
  exact implicitDeriv_X_coeff_zero p

example (m : ℕ) (_hm : 0 < m) :
    (implicitDerivXSpanXPow m).toIdeal = Ideal.span {(X : R[X]) ^ m} :=
  rfl

example (x : R[X] ⧸ Ideal.span ({X - C 0} : Set R[X])) :
    Polynomial.quotientSpanXSubCAlgEquiv 0 (implicitDeriv_X_quotientDerivation x) =
      (Polynomial.quotientSpanXSubCAlgEquiv 0 x)′ :=
  implicitDeriv_X_quotientSpanX_apply x

end PolynomialDerivation

end DeepWiki.SymbolicIntegration
