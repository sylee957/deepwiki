import DeepWiki.SymbolicIntegration.Computable.ConcreteCoherence
import DeepWiki.SymbolicIntegration.CanonicalRepresentation

/-! # Generic associate/derivative helpers for splitting factorization
Two field- and derivation-generic helpers: `gcd_derivative_dvd_gcd_implicitDeriv` (the denominator gcd
divides the numerator gcd, char `0`) and `natDegree_eq_of_associated` (degree is associate-invariant). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

open UniqueFactorizationMonoid Classical in
/-- `gcd(p, dp/dt) ∣ gcd(p, Dp)` in char `0` for the monomial derivation `D = implicitDeriv v`. -/
theorem gcd_derivative_dvd_gcd_implicitDeriv {K : Type*} [Field K] [CharZero K] [Differential K]
    (v : K[X]) {p : K[X]} (hp : p ≠ 0) :
    gcd p (derivative p) ∣ gcd p (Differential.implicitDeriv v p) := by
  have hunit := fun π (hπ : π ∈ primeFactors p) => isUnit_natCast_count_primeFactors hπ
  have hnum : Associated (gcd p (Differential.implicitDeriv v p))
      ((∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1))
        * ∏ π ∈ (primeFactors p).filter
            (fun π => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π), π) :=
    @associated_gcd_deriv_special_part K _ ⟨Differential.implicitDeriv v⟩ p hp hunit
  have hfilt : (primeFactors p).filter
      (fun π => @IsSpecial _ _ ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩ π) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro π hπ
    exact not_isSpecial_derivative_of_irreducible
      (irreducible_of_normalized_factor π (mem_primeFactors.mp hπ))
  have hden : Associated (gcd p (derivative p))
      (∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1)) := by
    have h := @associated_gcd_deriv_special_part K _
      ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩ p hp hunit
    rwa [hfilt, Finset.prod_empty, mul_one] at h
  refine hden.dvd.trans ?_
  exact (dvd_mul_right _ _).trans hnum.symm.dvd

/-- `Associated a b → a.natDegree = b.natDegree` in `K[X]`: degree is associate-invariant. -/
theorem natDegree_eq_of_associated {K : Type*} [Field K] {a b : K[X]} (h : Associated a b) :
    a.natDegree = b.natDegree :=
  Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated h)

end DeepWiki.SymbolicIntegration
