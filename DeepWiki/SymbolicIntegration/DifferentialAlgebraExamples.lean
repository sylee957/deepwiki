import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import DeepWiki.SymbolicIntegration.DifferentialAlgebraFacts

/-! # Worked differential-algebra examples
Concrete instances of the differential-field machinery: the induced derivation
`Δ = κ_D + X·d/dX` on `R[X]` and its restriction to the substitution quotient `R[X]/(X) ≃ R`,
the differential ideals of `(K[X], d/dX)`, and the fraction-field uniqueness of derivation
extensions. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section PolynomialDerivation
variable {R : Type*} [CommRing R] [Differential R]

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

end PolynomialDerivation

section DifferentialIdealsPolynomial
variable {K : Type*} [Field K]

/-- The `(deg p)`-fold `d/dX`-derivative of a nonzero `p ∈ K[X]` is the nonzero constant
`(deg p)! · lc(p)`: above its degree the iterated derivative vanishes (a constant), and its `0`th
coefficient is `descFactorial (deg p) (deg p) • lc(p) = (deg p)! · lc(p)`. -/
theorem iterate_derivative_natDegree_eq_C (p : K[X]) :
    Polynomial.derivative^[p.natDegree] p
      = Polynomial.C (Nat.factorial p.natDegree • p.leadingCoeff) := by
  have hle : (Polynomial.derivative^[p.natDegree] p).natDegree ≤ 0 := by
    simpa using Polynomial.natDegree_iterate_derivative p p.natDegree
  rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hle)]
  congr 1
  rw [Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self]
  rw [Polynomial.coeff_natDegree]

/-- The only differential ideals of `(K[X], d/dX)` over a characteristic-`0` field `K` are
`⊥` and `⊤`: an ideal closed under `d/dX` containing a nonzero `p` contains the nonzero constant
`(deg p)! · lc(p)`, a unit. -/
theorem differentialIdeal_eq_bot_or_top [CharZero K] (I : Ideal K[X])
    (hI : ∀ p ∈ I, Polynomial.derivative p ∈ I) : I = ⊥ ∨ I = ⊤ := by
  rcases eq_or_ne I ⊥ with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    obtain ⟨p, hpI, hp0⟩ := (Submodule.ne_bot_iff I).mp h
    have hiter : ∀ k, Polynomial.derivative^[k] p ∈ I := by
      intro k
      induction k with
      | zero => simpa using hpI
      | succ m ih => rw [Function.iterate_succ_apply']; exact hI _ ih
    have hmem := hiter p.natDegree
    rw [iterate_derivative_natDegree_eq_C p] at hmem
    have hc : (Nat.factorial p.natDegree • p.leadingCoeff) ≠ 0 := by
      simp only [nsmul_eq_mul, ne_eq, mul_eq_zero, not_or]
      exact ⟨by exact_mod_cast Nat.factorial_ne_zero _, Polynomial.leadingCoeff_ne_zero.mpr hp0⟩
    exact Ideal.eq_top_of_isUnit_mem I hmem
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))

/-- `⊥` and `⊤` are differential ideals of `(K[X], d/dX)`; with
`differentialIdeal_eq_bot_or_top` the differential ideals are exactly `{⊥, ⊤}`. -/
theorem differentialIdeal_bot_and_top :
    (∀ p ∈ (⊥ : Ideal K[X]), Polynomial.derivative p ∈ (⊥ : Ideal K[X])) ∧
      (∀ p ∈ (⊤ : Ideal K[X]), Polynomial.derivative p ∈ (⊤ : Ideal K[X])) :=
  ⟨fun p hp => by rw [Ideal.mem_bot.mp hp, map_zero]; exact Ideal.zero_mem _,
   fun _ _ => Submodule.mem_top⟩

end DifferentialIdealsPolynomial

end DeepWiki.SymbolicIntegration
