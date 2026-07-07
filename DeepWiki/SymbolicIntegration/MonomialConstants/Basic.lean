import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # Basic monomial constant facts

Quotient-constant criteria for special numerators and denominators. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Coprime
variable {R : Type*} [CommRing R] [Differential R]

/-- If `a` and `b` are coprime and `b * a′ = a * b′`, then both are special. -/
theorem isSpecial_of_coprime_of_deriv_quotient_num_eq_zero {a b : R} (hco : IsCoprime a b)
    (h : b * a′ = a * b′) : IsSpecial a ∧ IsSpecial b := by
  refine ⟨hco.dvd_of_dvd_mul_left ?_, hco.symm.dvd_of_dvd_mul_left ?_⟩
  · exact ⟨b′, h⟩
  · exact ⟨a′, h.symm⟩

end Coprime

section FractionConstants
variable {R K : Type*} [CommRing R] [Differential R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Differential K] [DifferentialAlgebra R K]

omit [IsDomain R] in
/-- A constant quotient with coprime numerator and nonzero denominator has special numerator and denominator. -/
theorem isSpecial_num_denom_of_const_quotient {a b : R} (hco : IsCoprime a b) (hb : b ≠ 0)
    (hconst : (algebraMap R K a / algebraMap R K b)′ = 0) :
    IsSpecial a ∧ IsSpecial b := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hbK : algebraMap R K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
  have hnum : algebraMap R K (b * a′) = algebraMap R K (a * b′) := by
    rw [deriv_div, div_eq_zero_iff] at hconst
    rcases hconst with hz | hz
    · rw [sub_eq_zero] at hz
      rw [map_mul, map_mul, ← deriv_algebraMap, ← deriv_algebraMap]
      exact hz
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp hz) hbK
  exact isSpecial_of_coprime_of_deriv_quotient_num_eq_zero hco (hinj hnum)

end FractionConstants

end DeepWiki.SymbolicIntegration
