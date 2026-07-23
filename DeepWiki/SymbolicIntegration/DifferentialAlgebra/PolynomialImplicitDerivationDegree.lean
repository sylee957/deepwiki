import DeepWiki.SymbolicIntegration.DifferentialAlgebra.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-! # Implicit-derivative degree bounds

Degree estimates for the monomial derivation `implicitDeriv v` on `R[X]`. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Polynomial in
/-- Degree bound: `(implicitDeriv v p).natDegree ≤ deg p + max(0, deg v − 1)`. -/
theorem natDegree_implicitDeriv_le {R : Type*} [CommRing R] [Differential R] (v p : R[X]) :
    (Differential.implicitDeriv v p).natDegree ≤ p.natDegree + max 0 (v.natDegree - 1) := by
  have happly : Differential.implicitDeriv v p = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have h1 : (Differential.mapCoeffs p).natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    rw [Differential.coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt hN]
    simp
  rw [happly]
  rcases eq_or_ne (derivative p) 0 with hdp | hdp
  · rw [hdp, mul_zero, add_zero]
    exact h1.trans (Nat.le_add_right _ _)
  · have hp1 : 1 ≤ p.natDegree := by
      rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
      · rw [Polynomial.natDegree_eq_zero] at h0
        obtain ⟨c, rfl⟩ := h0
        simp at hdp
      · exact h0
    have h2 : (v * derivative p).natDegree ≤ v.natDegree + (p.natDegree - 1) := by
      calc (v * derivative p).natDegree ≤ v.natDegree + (derivative p).natDegree := natDegree_mul_le
        _ ≤ v.natDegree + (p.natDegree - 1) := by gcongr; exact natDegree_derivative_le p
    calc (Differential.mapCoeffs p + v * derivative p).natDegree
        ≤ max (Differential.mapCoeffs p).natDegree (v * derivative p).natDegree :=
          natDegree_add_le _ _
      _ ≤ max p.natDegree (v.natDegree + (p.natDegree - 1)) := max_le_max h1 h2
      _ ≤ p.natDegree + max 0 (v.natDegree - 1) := by omega

open Polynomial in
/-- Nonlinear degree equality: over char `0`, for `deg v ≥ 2` and `deg p ≥ 1`,
`(implicitDeriv v p).natDegree = deg p + deg v − 1`. -/
theorem natDegree_implicitDeriv_eq {F : Type*} [Field F] [CharZero F] [Differential F]
    (v p : F[X]) (hv : 2 ≤ v.natDegree) (hp : 1 ≤ p.natDegree) :
    (Differential.implicitDeriv v p).natDegree = p.natDegree + (v.natDegree - 1) := by
  have happly : Differential.implicitDeriv v p = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have h1 : (Differential.mapCoeffs p).natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    rw [Differential.coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt hN]; simp
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hdp : derivative p ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hmul : (v * derivative p).natDegree = v.natDegree + (p.natDegree - 1) := by
    rw [natDegree_mul hv0 hdp, natDegree_derivative p]
  have hlt : (Differential.mapCoeffs p).natDegree < (v * derivative p).natDegree := by
    rw [hmul]; omega
  rw [happly, natDegree_add_eq_right_of_natDegree_lt hlt, hmul]; omega

end DeepWiki.SymbolicIntegration
