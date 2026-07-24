import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtSubresultant
import DeepWiki.SymbolicIntegration.PseudoRemainderSequence
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.ResidueMultiplicity

/-! # Lazard–Rioboo–Trager correctness
The LRT log-part algorithm replaces the Rothstein-Trager per-residue gcds
`gcd(D, A - a * D')` by specializations of one subresultant PRS.

This file connects the subresultant-gcd engine to `lrtSubresultant`, including the
padding needed when `A - C a * derivative D` has smaller than formal degree. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- If the top coefficient does not cancel, `A - C a * derivative D` has degree
`D.natDegree - 1`. -/
theorem natDegree_sub_C_mul_derivative {K : Type*} [Field K] (A D : K[X]) (a : K)
    (hA : A.natDegree < D.natDegree)
    (hne : A.coeff (D.natDegree - 1) ≠ a * ((D.natDegree : K) * D.leadingCoeff)) :
    (A - C a * derivative D).natDegree = D.natDegree - 1 := by
  have hle : (A - C a * derivative D).natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le D)))
  refine le_antisymm hle (le_natDegree_of_ne_zero ?_)
  have hcast : ((D.natDegree - 1 : ℕ) : K) + 1 = (D.natDegree : K) := by
    rw [Nat.cast_sub (by omega : 1 ≤ D.natDegree), Nat.cast_one]; ring
  rw [coeff_sub, coeff_C_mul, coeff_derivative, Nat.sub_add_cancel (by omega : 1 ≤ D.natDegree),
    hcast, ← leadingCoeff]
  intro h
  exact hne (by linear_combination h)

/-- The specialized LRT subresultant at the last nonzero Euclidean PRS degree is
similar to `gcd D (A - C a * derivative D)`. -/
theorem isSimilar_lrtSubresultant_eval_gcd {K : Type*} [Field K] [GCDMonoid K[X]]
    (A D : K[X]) (a : K) (hD : D ≠ 0) (hA : A.natDegree < D.natDegree)
    {k : ℕ} (hk2 : 2 ≤ k) (hk0 : euclideanPRS D (A - C a * derivative D) (k + 1) = 0)
    (hknz : ∀ j, 1 ≤ j → j ≤ k → euclideanPRS D (A - C a * derivative D) j ≠ 0) :
    IsSimilar
      ((lrtSubresultant A D (euclideanPRS D (A - C a * derivative D) k).natDegree).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  rw [lrtSubresultant_eval]
  set E := A - C a * derivative D with hE
  have hElt : E.natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le D)))
  have hjE : (euclideanPRS D E k).natDegree < E.natDegree := by
    have h := euclideanPRS_natDegree_strictAnti D E hknz 1 k (le_refl 1) (by omega) (le_refl k)
    rwa [euclideanPRS_one] at h
  have hengine := subresultant_euclideanPRS_isSimilar_gcd D E hD
    (le_trans hElt (Nat.sub_le _ _)) hk2 hk0 hknz
  exact (isSimilar_subresultant_padding D E D.natDegree E.natDegree
    (euclideanPRS D E k).natDegree hjE
    (le_trans (le_of_lt hjE) (le_trans hElt (Nat.sub_le _ _))) le_rfl le_rfl
    (leadingCoeff_ne_zero.mpr hD) hElt).trans hengine

/-- In the one-step PRS case, the specialized top LRT subresultant is similar to
`gcd D (A - C a * derivative D)`. -/
theorem isSimilar_lrtSubresultant_eval_gcd_top {K : Type*} [Field K] [GCDMonoid K[X]]
    (A D : K[X]) (a : K) (hD : D ≠ 0) (hA : A.natDegree < D.natDegree)
    (hE : A - C a * derivative D ≠ 0)
    (h0 : euclideanPRS D (A - C a * derivative D) 2 = 0) :
    IsSimilar
      ((lrtSubresultant A D (A - C a * derivative D).natDegree).map (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  rw [lrtSubresultant_eval]
  set E := A - C a * derivative D with hEdef
  have hElt : E.natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le D)))
  have hsim : IsSimilar (subresultant D E D.natDegree (D.natDegree - 1) E.natDegree) E := by
    rw [subresultant_deg_ge_normal D E D.natDegree (D.natDegree - 1) E.natDegree le_rfl
      (by omega) (Nat.sub_le _ _) hElt]
    exact ⟨1, (D.coeff D.natDegree) ^ (D.natDegree - 1 - E.natDegree)
        * E.coeff E.natDegree ^ (D.natDegree - E.natDegree - 1), one_ne_zero,
      mul_ne_zero (pow_ne_zero _ (by rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hD))
        (pow_ne_zero _ (by rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hE)),
      by rw [map_one, one_mul]⟩
  exact hsim.trans (isSimilar_gcd_right_of_euclideanPRS_two_eq_zero D E hE h0).symm

open scoped Classical in
/-- At any residue whose multiplicity is below `D.natDegree`, the specialized LRT
subresultant is similar to the Rothstein-Trager gcd. -/
theorem lazardRiobooTrager_isSimilar_gcd {K : Type*} [Field K] [IsAlgClosed K]
    (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (a : K)
    (hi : (rtResultant A D).rootMultiplicity a < D.natDegree) :
    IsSimilar
      ((lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  set E := A - C a * derivative D with hE
  have hDne : D ≠ 0 := fun h => by simp [h] at hA
  -- the multiplicity bridge: `i = deg gcd(D, E)`
  have hmul : (rtResultant A D).rootMultiplicity a = (gcd D E).natDegree :=
    rootMultiplicity_rtResultant_eq_natDegree_gcd A D hD hA a
  -- `E ≠ 0`: were `E = 0`, `gcd D 0 ~ D` would give `deg gcd = deg D`, contradicting `i < deg D`
  have hEne : E ≠ 0 := by
    intro h
    rw [h, (IsSimilar.of_associated
      (gcd_zero_right D ▸ normalize_associated D)).natDegree_eq] at hmul
    rw [hmul] at hi; exact absurd hi (lt_irrefl _)
  -- termination data for the Euclidean p.r.s. of `D, E`
  obtain ⟨k, hk1, hk0, hknz⟩ := exists_last_euclideanPRS_nonzero D E hEne
  -- the last nonzero p.r.s. element is similar to the gcd, so they share the degree
  have hsim : IsSimilar (euclideanPRS D E k) (gcd D E) :=
    (isPRS_euclideanPRS D E).isSimilar_gcd hk0 (fun j hj1 hjk => hknz j hj1 hjk)
  have hdeg : (euclideanPRS D E k).natDegree = (gcd D E).natDegree := hsim.natDegree_eq
  -- split on the number of p.r.s. steps
  rcases Nat.lt_or_ge k 2 with hk | hk2
  · -- `k = 1`: one-step termination, `E ∣ D`, the top p.r.s. index `i = deg E`
    have hk1' : k = 1 := by omega
    subst hk1'
    rw [euclideanPRS_one] at hdeg
    have h0 : euclideanPRS D E 2 = 0 := hk0
    rw [hmul, ← hdeg]
    exact isSimilar_lrtSubresultant_eval_gcd_top A D a hDne hA hEne h0
  · -- `k ≥ 2`: multi-step termination, the part-(ii) padding path
    rw [hmul, ← hdeg]
    exact isSimilar_lrtSubresultant_eval_gcd A D a hDne hA hk2 hk0 hknz

open scoped Classical in
open scoped Classical in
/-- The branch returned by the LRT algorithm at any residue is similar to
`gcd D (A - C a * derivative D)`. -/
theorem lazardRiobooTrager_output_isSimilar_gcd {K : Type*} [Field K] [IsAlgClosed K]
    (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (a : K) :
    IsSimilar
      ((if (rtResultant A D).rootMultiplicity a = D.natDegree then D.map (C : K →+* K[X])
        else lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  have hDne : D ≠ 0 := fun h => by simp [h] at hA
  set E := A - C a * derivative D with hE
  have hmul : (rtResultant A D).rootMultiplicity a = (gcd D E).natDegree :=
    rootMultiplicity_rtResultant_eq_natDegree_gcd A D hD hA a
  have hile : (rtResultant A D).rootMultiplicity a ≤ D.natDegree :=
    hmul.le.trans (natDegree_le_of_dvd (gcd_dvd_left D E) hDne)
  by_cases hcase : (rtResultant A D).rootMultiplicity a = D.natDegree
  · rw [if_pos hcase]
    have hmapid : (D.map (C : K →+* K[X])).map (Polynomial.evalRingHom a) = D := by
      rw [Polynomial.map_map,
        show (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K from by ext k; simp,
        Polynomial.map_id]
    rw [hmapid]
    exact (isSimilar_gcd_left_of_natDegree_eq hDne (hmul.symm.trans hcase)).symm
  · rw [if_neg hcase]
    exact lazardRiobooTrager_isSimilar_gcd A D hD hA a (lt_of_le_of_ne hile hcase)

end DeepWiki.SymbolicIntegration
