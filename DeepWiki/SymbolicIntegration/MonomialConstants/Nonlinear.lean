import DeepWiki.SymbolicIntegration.MonomialConstants.Basic

/-! # Nonlinear monomial constants

Degree and leading-coefficient constraints for constants of nonlinear monomial extensions. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section Nonlinear
variable {F : Type*} [Field F] [CharZero F] [Differential F]

/-- In a nonlinear monomial derivation, the leading coefficient of `implicitDeriv v p` is determined by `p` and `v`. -/
theorem leadingCoeff_implicitDeriv_nonlinear (v p : F[X]) (hv : 2 ≤ v.natDegree)
    (hp : 1 ≤ p.natDegree) :
    (Differential.implicitDeriv v p).leadingCoeff
      = (p.natDegree : F) * p.leadingCoeff * v.leadingCoeff := by
  have happly : Differential.implicitDeriv v p
      = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hdp : derivative p ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hmul : (v * derivative p).natDegree = p.natDegree + (v.natDegree - 1) := by
    rw [natDegree_mul hv0 hdp, natDegree_derivative]; omega
  have h1 : (Differential.mapCoeffs p).natDegree ≤ p.natDegree := by
    refine natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => ?_)
    rw [Differential.coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt hN]; simp
  have hlt : (Differential.mapCoeffs p).natDegree < (v * derivative p).natDegree := by
    rw [hmul]; omega
  have hdeg : (Differential.implicitDeriv v p).natDegree = (v * derivative p).natDegree := by
    rw [happly, natDegree_add_eq_right_of_natDegree_lt hlt]
  rw [leadingCoeff, hdeg, happly, coeff_add, coeff_eq_zero_of_natDegree_lt (hlt.trans_le le_rfl),
    zero_add, ← leadingCoeff, leadingCoeff_mul, leadingCoeff_derivative]
  ring

/-- A special cofactor for a nonlinear monomial derivation has leading coefficient and degree controlled by `p.natDegree`. -/
theorem leadingCoeff_cofactor_nonlinear {v p g : F[X]} (hv : 2 ≤ v.natDegree) (hp0 : p ≠ 0)
    (hg : Differential.implicitDeriv v p = p * g) :
    (1 ≤ p.natDegree → g.leadingCoeff = (p.natDegree : F) * v.leadingCoeff
        ∧ g.natDegree = v.natDegree - 1)
      ∧ (p.natDegree = 0 → g.natDegree = 0) := by
  have hlcp : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hlcv : v.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hv)
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have hlc : (Differential.implicitDeriv v p).leadingCoeff
        = (p.natDegree : F) * p.leadingCoeff * v.leadingCoeff :=
      leadingCoeff_implicitDeriv_nonlinear v p hv hp
    have hdeg : (Differential.implicitDeriv v p).natDegree = p.natDegree + (v.natDegree - 1) :=
      natDegree_implicitDeriv_eq v p hv hp
    have hgne : g ≠ 0 := by
      rintro rfl; rw [mul_zero] at hg; rw [hg] at hdeg; simp at hdeg; omega
    have hlcg : p.leadingCoeff * g.leadingCoeff = (p.natDegree : F) * p.leadingCoeff * v.leadingCoeff := by
      rw [← leadingCoeff_mul, ← hg, hlc]
    have hdegg : g.natDegree = v.natDegree - 1 := by
      rw [hg, natDegree_mul hp0 hgne] at hdeg; omega
    refine ⟨?_, hdegg⟩
    have := mul_left_cancel₀ hlcp (by rw [hlcg]; ring :
      p.leadingCoeff * g.leadingCoeff = p.leadingCoeff * ((p.natDegree : F) * v.leadingCoeff))
    exact this
  · rcases eq_or_ne g 0 with hg0 | hgne
    · rw [hg0]; simp
    · obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨p.coeff 0, eq_C_of_natDegree_eq_zero hp⟩
      have hDp0 : (Differential.implicitDeriv v (C c)).natDegree = 0 := by
        rw [Differential.implicitDeriv_C]; exact natDegree_C _
      rw [hg, natDegree_mul hp0 hgne, natDegree_C] at hDp0
      omega

/-- Nonzero special polynomials with zero quotient-derivative numerator have equal `natDegree` in a nonlinear monomial derivation. -/
theorem natDegree_eq_of_special_of_deriv_quotient_num_eq_zero {v a b : F[X]} (hv : 2 ≤ v.natDegree)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hsa : a ∣ Differential.implicitDeriv v a) (hsb : b ∣ Differential.implicitDeriv v b)
    (h : b * Differential.implicitDeriv v a = a * Differential.implicitDeriv v b) :
    a.natDegree = b.natDegree := by
  obtain ⟨g, hg⟩ := hsa
  obtain ⟨h', hh⟩ := hsb
  have hgh : g = h' := by
    have hcancel : a * b * g = a * b * h' := by
      rw [show a * b * g = b * (a * g) from by ring, show a * b * h' = a * (b * h') from by ring,
        ← hg, ← hh, h]
    exact mul_left_cancel₀ (mul_ne_zero ha0 hb0) hcancel
  subst hgh
  obtain ⟨hga, hg0a⟩ := leadingCoeff_cofactor_nonlinear hv ha0 hg
  obtain ⟨hgb, hg0b⟩ := leadingCoeff_cofactor_nonlinear hv hb0 hh
  have hlcv : v.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hv)
  rcases Nat.eq_zero_or_pos a.natDegree with hae | hap
  · rcases Nat.eq_zero_or_pos b.natDegree with hbe | hbp
    · rw [hae, hbe]
    · obtain ⟨_, hgdegb⟩ := hgb hbp
      rw [hg0a hae] at hgdegb
      omega
  · rcases Nat.eq_zero_or_pos b.natDegree with hbe | hbp
    · obtain ⟨_, hgdega⟩ := hga hap
      rw [hg0b hbe] at hgdega
      omega
    · obtain ⟨hlca, _⟩ := hga hap
      obtain ⟨hlcb, _⟩ := hgb hbp
      have : (a.natDegree : F) * v.leadingCoeff = (b.natDegree : F) * v.leadingCoeff := by
        rw [← hlca, ← hlcb]
      have hcast : (a.natDegree : F) = (b.natDegree : F) := mul_right_cancel₀ hlcv this
      exact_mod_cast hcast

/-- A constant quotient in a nonlinear monomial fraction field has special numerator and denominator of equal `natDegree`. -/
theorem isSpecial_and_natDegree_eq_of_const_quotient_nonlinear
    {K : Type*} [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
    {v a b : F[X]} (hv : 2 ≤ v.natDegree) (hco : IsCoprime a b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hder : ∀ p : F[X], (algebraMap F[X] K p)′ = algebraMap F[X] K (Differential.implicitDeriv v p))
    (hconst : (algebraMap F[X] K a / algebraMap F[X] K b)′ = 0) :
    a ∣ Differential.implicitDeriv v a ∧ b ∣ Differential.implicitDeriv v b
      ∧ a.natDegree = b.natDegree := by
  letI : Differential F[X] := ⟨Differential.implicitDeriv v⟩
  letI : DifferentialAlgebra F[X] K := ⟨hder⟩
  obtain ⟨hsa, hsb⟩ := isSpecial_num_denom_of_const_quotient hco hb0 hconst
  have hinj : Function.Injective (algebraMap F[X] K) := IsFractionRing.injective F[X] K
  have hbK : algebraMap F[X] K b ≠ 0 := fun hz => hb0 (hinj (by rw [hz, map_zero]))
  have hpoly : b * Differential.implicitDeriv v a = a * Differential.implicitDeriv v b := by
    apply hinj
    rw [deriv_div, div_eq_zero_iff] at hconst
    rcases hconst with hz | hz
    · rw [sub_eq_zero] at hz
      rw [map_mul, map_mul, ← hder, ← hder]; exact hz
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp hz) hbK
  exact ⟨hsa, hsb,
    natDegree_eq_of_special_of_deriv_quotient_num_eq_zero hv ha0 hb0 hsa hsb hpoly⟩

end Nonlinear

end DeepWiki.SymbolicIntegration
