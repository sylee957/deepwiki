import DeepWiki.SymbolicIntegration.Constants

/-! # Algebraic constants

Minimal-polynomial facts showing that integral constants are algebraic over the
base constants.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section AlgebraicConstant
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- High coefficients of `Differential.mapCoeffs p` vanish for monic `p`. -/
theorem coeff_mapCoeffs_eq_zero_of_monic {p : F[X]} (hp : p.Monic) {i : ℕ}
    (hi : p.natDegree ≤ i) : (Differential.mapCoeffs p).coeff i = 0 := by
  rw [Differential.coeff_mapCoeffs]
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [Polynomial.Monic.coeff_natDegree hp]; simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]; simp

/-- `Differential.mapCoeffs p` has degree strictly below monic `p`. -/
theorem degree_mapCoeffs_lt {p : F[X]} (hp : p.Monic) :
    (Differential.mapCoeffs p).degree < p.degree := by
  rw [Polynomial.degree_eq_natDegree hp.ne_zero]
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  exact coeff_mapCoeffs_eq_zero_of_monic hp hk

/-- The minimal polynomial of an integral constant has constant coefficients. -/
theorem minpoly_coeff_deriv_eq_zero_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) :
    ∀ i, ((minpoly F c).coeff i)′ = 0 := by
  set p := minpoly F c with hpdef
  have hpmonic : p.Monic := minpoly.monic hint
  -- the κ_D(p) term vanishes at c
  have hkappa : Polynomial.aeval c (Differential.mapCoeffs p) = 0 := by
    have hchain := Differential.deriv_aeval_eq (A := F) (R := E) c p
    rw [minpoly.aeval, map_zero, hc, mul_zero, add_zero] at hchain
    exact hchain.symm
  -- minimality forces mapCoeffs p = 0
  have hmc0 : Differential.mapCoeffs p = 0 := by
    by_contra hne
    have hle := minpoly.degree_le_of_ne_zero F c hne hkappa
    rw [← hpdef] at hle
    exact absurd (lt_of_le_of_lt hle (degree_mapCoeffs_lt hpmonic)) (lt_irrefl _)
  -- hence every coefficient of p is a constant
  have hconst : ∀ i, (p.coeff i)′ = 0 := fun i => by
    have := congrArg (fun r => Polynomial.coeff r i) hmc0
    rwa [Differential.coeff_mapCoeffs, Polynomial.coeff_zero] at this
  intro i
  exact hconst i

/-- An integral constant has a nonzero annihilating polynomial over the base constants. -/
theorem isAlgebraicOverConst_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) :
    ∃ p : F[X], p ≠ 0 ∧ (∀ i, (p.coeff i)′ = 0) ∧ Polynomial.aeval c p = 0 := by
  refine ⟨minpoly F c, (minpoly.monic hint).ne_zero, ?_, ?_⟩
  · exact minpoly_coeff_deriv_eq_zero_of_deriv_eq_zero hc hint
  · rw [minpoly.aeval]

/-- Mapping a base-constant annihilator gives an ambient constant-coefficient polynomial. -/
theorem isAlgebraicOverConst_map_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) :
    ∃ q : E[X], q ≠ 0 ∧ (∀ i, (q.coeff i)′ = 0) ∧ q.eval c = 0 := by
  obtain ⟨p, hpne, hconst, hroot⟩ := isAlgebraicOverConst_of_deriv_eq_zero hc hint
  refine ⟨p.map (algebraMap F E), ?_, ?_, ?_⟩
  · rw [Ne, Polynomial.map_eq_zero_iff (algebraMap F E).injective]
    exact hpne
  · intro i
    rw [Polynomial.coeff_map, deriv_algebraMap, hconst i, map_zero]
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hroot

end AlgebraicConstant

end DeepWiki.SymbolicIntegration
