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

/-- The canonical equivalence `R[X] ⧸ (X) ≃ R` induced by evaluation at `X = 0`. -/
noncomputable def quotientSpanXAlgEquiv :
    (R[X] ⧸ Ideal.span ({X} : Set R[X])) ≃ₐ[R] R := by
  let h : Ideal.span ({X} : Set R[X]) = Ideal.span ({X - C 0} : Set R[X]) := by simp
  exact (Ideal.quotientEquivAlgOfEq R h).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (R := R) 0)

omit [Differential R] in
/-- Under `R[X] ⧸ (X) ≃ R`, the quotient projection is substitution `X ↦ 0`. -/
@[simp] theorem quotientSpanXAlgEquiv_mk (p : R[X]) :
    let π := Ideal.Quotient.mk (Ideal.span ({X} : Set R[X]))
    let e := quotientSpanXAlgEquiv (R := R)
    e (π p) = p.eval 0 := by
  simp [quotientSpanXAlgEquiv]

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

/-- The derivation on `R[X] ⧸ (X)` induced by `Differential.implicitDeriv X`. -/
noncomputable def implicitDeriv_X_quotientDerivation :
    Derivation ℤ (R[X] ⧸ Ideal.span ({X} : Set R[X]))
      (R[X] ⧸ Ideal.span ({X} : Set R[X])) := by
  let I : DifferentialIdeal R[X] :=
    { toIdeal := Ideal.span {X}
      deriv_mem' := by
        simpa [implicitDerivXSpanXPow] using
          (implicitDerivXSpanXPow (R := R) 1).deriv_mem' }
  exact I.quotientDerivation

/-- The induced quotient derivation sends the class of `p` to the class of `Δp`. -/
@[simp] theorem implicitDeriv_X_quotientDerivation_mk (p : R[X]) :
    let π := Ideal.Quotient.mk (Ideal.span ({X} : Set R[X]))
    let Δ := Differential.implicitDeriv (X : R[X])
    let Δstar := implicitDeriv_X_quotientDerivation (R := R)
    Δstar (π p) = π (Δ p) := by
  dsimp only
  unfold implicitDeriv_X_quotientDerivation
  exact DifferentialIdeal.quotientDerivation_mk _ p

/-- Under `R[X] ⧸ (X) ≃ R`, `Δstar(π(p)) = D(p(0))` for every `p ∈ R[X]`. -/
theorem implicitDeriv_X_quotientDerivation_mk_eval_zero (p : R[X]) :
    let π := Ideal.Quotient.mk (Ideal.span ({X} : Set R[X]))
    let Δstar := implicitDeriv_X_quotientDerivation (R := R)
    let e := quotientSpanXAlgEquiv (R := R)
    e (Δstar (π p)) = (p.eval 0)′ := by
  dsimp only
  calc
    quotientSpanXAlgEquiv (R := R)
        (implicitDeriv_X_quotientDerivation (R := R)
          (Ideal.Quotient.mk (Ideal.span ({X} : Set R[X])) p)) =
      quotientSpanXAlgEquiv (R := R)
        (Ideal.Quotient.mk (Ideal.span ({X} : Set R[X]))
          (Differential.implicitDeriv X p)) :=
      congrArg (quotientSpanXAlgEquiv (R := R))
        (implicitDeriv_X_quotientDerivation_mk p)
    _ = (Differential.implicitDeriv X p).eval 0 :=
      quotientSpanXAlgEquiv_mk (Differential.implicitDeriv X p)
    _ = (p.eval 0)′ := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
      exact implicitDeriv_X_coeff_zero p

/-- Under `R[X] ⧸ (X) ≃ R`, the quotient derivation induced by
`Differential.implicitDeriv X` agrees pointwise with `D`. -/
theorem implicitDeriv_X_quotientSpanX :
    let Δstar := implicitDeriv_X_quotientDerivation (R := R)
    let e := quotientSpanXAlgEquiv (R := R)
    ∀ x, e (Δstar x) = (e x)′ := by
  dsimp only
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [implicitDeriv_X_quotientDerivation_mk,
    quotientSpanXAlgEquiv_mk, quotientSpanXAlgEquiv_mk]
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
  exact implicitDeriv_X_coeff_zero p

end PolynomialDerivation

end DeepWiki.SymbolicIntegration
