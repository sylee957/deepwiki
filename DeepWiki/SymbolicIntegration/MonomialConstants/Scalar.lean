import DeepWiki.SymbolicIntegration.MonomialConstants.Basic

/-! # Scalar monomial constants

Special polynomial criteria for scalar monomial derivations. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {k : Type*} [Field k] [Differential k]

section ScalarMonomial
variable (w : k)

/-- A scalar monomial derivation does not increase polynomial `natDegree`. -/
theorem natDegree_implicitDeriv_C_le (p : k[X]) :
    (Differential.implicitDeriv (C w) p).natDegree ≤ p.natDegree := by
  refine (natDegree_implicitDeriv_le (C w) p).trans ?_
  rw [natDegree_C]; simp

/-- In a scalar monomial derivation, the top coefficient of `implicitDeriv (C w) p` is `(p.leadingCoeff)′`. -/
theorem coeff_natDegree_implicitDeriv_C (p : k[X]) :
    (Differential.implicitDeriv (C w) p).coeff p.natDegree = (p.coeff p.natDegree)′ := by
  have happly : Differential.implicitDeriv (C w) p
      = Differential.mapCoeffs p + C w * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  rw [happly, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul]
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
  · rw [h0, eq_C_of_natDegree_eq_zero h0, derivative_C, coeff_zero, mul_zero, add_zero, coeff_C,
      if_pos rfl]
  · have hd : (derivative p).coeff p.natDegree = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_derivative_le p) (by omega))
    rw [hd, mul_zero, add_zero]

end ScalarMonomial

/-- A monic polynomial under a scalar monomial derivation either differentiates to zero or drops `natDegree`. -/
theorem deriv_monic_eq_zero_or_natDegree_lt {w : k} {q : k[X]} (hq : q.Monic) :
    Differential.implicitDeriv (C w) q = 0
      ∨ (Differential.implicitDeriv (C w) q).natDegree < q.natDegree := by
  by_cases h0 : Differential.implicitDeriv (C w) q = 0
  · exact Or.inl h0
  · refine Or.inr (lt_of_le_of_ne (natDegree_implicitDeriv_C_le w q) ?_)
    intro heq
    have htop : (Differential.implicitDeriv (C w) q).coeff
        (Differential.implicitDeriv (C w) q).natDegree = 0 := by
      rw [heq, coeff_natDegree_implicitDeriv_C, hq.coeff_natDegree,
        (Differential.deriv : Derivation ℤ k k).map_one_eq_zero]
    exact (mt leadingCoeff_eq_zero.mp h0) htop

/-- A monic polynomial is special for a scalar monomial derivation iff its implicit derivative is zero. -/
theorem isSpecial_iff_deriv_eq_zero_of_monic {w : k} {q : k[X]} (hq : q.Monic) :
    q ∣ Differential.implicitDeriv (C w) q ↔ Differential.implicitDeriv (C w) q = 0 := by
  constructor
  · intro hdvd
    rcases deriv_monic_eq_zero_or_natDegree_lt hq with h | hlt
    · exact h
    · by_contra hne
      exact absurd (natDegree_le_of_dvd hdvd hne) (by omega)
  · intro h; rw [h]; exact dvd_zero q

omit [Differential k] in
/-- The monic normalization `p/lc(p)` of a nonzero `p` is an associate of `p` and monic. -/
theorem associated_mul_C_inv_leadingCoeff {p : k[X]} (hp : p ≠ 0) :
    Associated p (p * C p.leadingCoeff⁻¹) ∧ (p * C p.leadingCoeff⁻¹).Monic := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  refine ⟨(associated_mul_unit_right p _ (isUnit_C.mpr (Ne.isUnit (inv_ne_zero hlc)))),
    monic_mul_C_of_leadingCoeff_mul_eq_one (mul_inv_cancel₀ hlc)⟩

/-- A nonzero polynomial is special for a scalar monomial derivation iff its monic normalization has zero implicit derivative. -/
theorem isSpecial_iff_deriv_normalize_eq_zero {w : k} {p : k[X]} (hp : p ≠ 0) :
    p ∣ Differential.implicitDeriv (C w) p
      ↔ Differential.implicitDeriv (C w) (p * C p.leadingCoeff⁻¹) = 0 := by
  letI : Differential k[X] := ⟨Differential.implicitDeriv (C w)⟩
  obtain ⟨hassoc, hmonic⟩ := associated_mul_C_inv_leadingCoeff hp
  rw [← isSpecial_iff_deriv_eq_zero_of_monic hmonic]
  exact ⟨fun h => IsSpecial.of_associated hassoc h, fun h => IsSpecial.of_associated hassoc.symm h⟩

end DeepWiki.SymbolicIntegration
