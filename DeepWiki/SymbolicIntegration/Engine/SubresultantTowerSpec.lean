import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtGeneralDerivation
import DeepWiki.ComputableAlgebra.PolySubresultantLawful
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.Engine.LogPartTowerSoundness

/-! # Connecting the computable parametric LRT subresultant to the abstract theory (G4c)

`CPolySubresultant.parametric Dstar A Dd n m j` is the engine's parametric LRT log argument `Sⱼ(z,t)`: its `k`-th
entry is the `z`-polynomial coefficient of `tᵏ`, computed by interpolation in `z` of the coefficient of
the selected subresultant of `Dstar` and `A − z·Dd`. This file connects it to the general-derivation abstract
subresultant `subresultant (toPoly Dstar) (toPoly A − C z · B) n m j` (`B = toPoly Dd`), building on
the L4b subresultant certification `CPolySubresultant.toPoly_default`. See `docs/generalize-lrt-derivation.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly

universe u v

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]
  [CPolySubresultant DensePoly] [LawfulCPolySubresultant.{u,v} DensePoly]

/-- **Per-value subresultant agreement.** The `k`-th `t`-coefficient of the selected computable
subresultant of `Dstar` and `A − c·Dd`, read through `toK`, equals the `k`-th `t`-coefficient of the
abstract subresultant of `(Dstar, A − c·B)` (`B = toPoly Dd`), for any value `c`. Immediate from the L4b
certification `CPolySubresultant.toPoly_default` plus the `csub`/`cscale` bridges — no interpolation needed (this is
the per-node fact the interpolation extends to all residues). -/
theorem toK_selectedSubresultant_getD_eq_coeff (Dstar A Dd : DensePoly α) (c : α) (n m j k : ℕ) :
    CFieldSpec.toK
        (((CPolySubresultant.compute Dstar (csub A (cscale c Dd)) n m j : DensePoly α) : List α).getD k
          CCommRing.zero)
      = (subresultant (toPoly Dstar)
          (toPoly A - C (CFieldSpec.toK c) * toPoly Dd) n m j).coeff k := by
  rw [← toR_eq_toK, ← toPolyG_coeff, ← toPoly_list_eq,
    LawfulCPolySubresultant.compute_spec']
  simp only [toPoly_list_eq, denote]

variable [CDiffField α] [CDiffFieldSpec α]

/-- The per-value subresultant agreement with the **tower derivation** `Dd = CPolyEngine.monomialDeriv Dt Dstar`, so
`B = implicitDeriv (toPoly Dt) (toPoly Dstar)` — the form used by `cLrtLogArg`. -/
theorem toK_selectedSubresultant_getD_eq_coeff_monomial (Dt Dstar A : DensePoly α) (c : α) (n m j k : ℕ) :
    CFieldSpec.toK
        (((CPolySubresultant.compute Dstar
            (csub A (cscale c (CPolyEngine.monomialDeriv Dt Dstar))) n m j : DensePoly α) :
            List α).getD k CCommRing.zero)
      = (subresultant (toPoly Dstar)
          (toPoly A - C (CFieldSpec.toK c)
            * Differential.implicitDeriv (toPoly Dt) (toPoly Dstar)) n m j).coeff k := by
  rw [toK_selectedSubresultant_getD_eq_coeff]
  simp only [denote]

omit [CDiffField α] [CDiffFieldSpec α] in
open scoped Classical in
/-- **The parametric-subresultant certification (G4c).** The `k`-th entry of the engine's parametric log
argument `CPolySubresultant.parametric Dstar A Dd (cdeg Dstar) (cdeg Dd) j` (a `z`-polynomial) equals the `k`-th
`t`-coefficient of the abstract `lrtSubresultantGen (toPoly A) (toPoly Dstar) (toPoly Dd) j`, when
`Dd`'s degree matches the formal degree `deg Dstar − 1`. Via interpolation uniqueness: both `z`-polynomials
have degree `< N = cdeg Dstar + cdeg Dd + 1` (`natDegree_coeff_lrtSubresultantGen_le` /
`degree_toPolyG_cinterpolateG_lt`) and agree at the `N` integer nodes (per-value agreement + coefficient/eval
commutation + `lrtSubresultantGen_eval`). So the engine's interpolated log argument IS the abstract
subresultant coefficient. -/
theorem CPolySubresultant.toPoly_parametric_getD [CharZero (CFieldSpec.K α)] (Dstar A Dd : DensePoly α) (j k : ℕ)
    (hm : cdeg Dd = cdeg Dstar - 1) :
    toPoly ((CPolySubresultant.parametric Dstar A Dd (cdeg Dstar) (cdeg Dd) j).getD k [])
      = (lrtSubresultantGen (toPoly A) (toPoly Dstar) (toPoly Dd) j).coeff k := by
  have hnm : cdeg Dstar = (toPoly Dstar).natDegree := cdegG_eq_natDegree Dstar
  have hmm : cdeg Dd = (toPoly Dd).natDegree := cdegG_eq_natDegree Dd
  have hdd : (toPoly Dd).natDegree = (toPoly Dstar).natDegree - 1 := by rw [← hmm, hm, hnm]
  have hcommute : ∀ (P : (CFieldSpec.K α)[X][X]) (z : CFieldSpec.K α),
      (P.coeff k).eval z = (P.map (Polynomial.evalRingHom z)).coeff k := by
    intro P z; rw [Polynomial.coeff_map]; rfl
  set N := cdeg Dstar + cdeg Dd + 1 with hN
  by_cases hk : k < j + 1
  · -- `k ≤ j`: the `k`-th entry is the interpolant of the `t`-power-`k` samples
    have hget : (CPolySubresultant.parametric Dstar A Dd (cdeg Dstar) (cdeg Dd) j).getD k []
        = cinterpolate ((List.range N).map (fun jj =>
            (CField.natCast jj, ((CPolySubresultant.compute Dstar (csub A (cscale (CField.natCast jj) Dd))
              (cdeg Dstar) (cdeg Dd) j : DensePoly α) : List α).getD k CCommRing.zero))) := by
      rw [CPolySubresultant.parametric]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
      rfl
    set pts : List (α × α) := (List.range N).map (fun jj =>
      (CField.natCast jj, ((CPolySubresultant.compute Dstar (csub A (cscale (CField.natCast jj) Dd))
        (cdeg Dstar) (cdeg Dd) j : DensePoly α) : List α).getD k CCommRing.zero)) with hpts
    have hlen : pts.length = N := by rw [hpts, List.length_map, List.length_range]
    have hne : pts ≠ [] := by rw [hpts]; simp [hN]
    have hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup := by
      have : pts.map (fun p => CFieldSpec.toK p.1)
          = (List.range N).map (Nat.cast : ℕ → CFieldSpec.K α) := by
        rw [hpts, List.map_map]; apply List.map_congr_left; intro jj _
        simp only [Function.comp_apply, CFieldSpec.toK_natCast]
      rw [this]; exact (List.nodup_range).map Nat.cast_injective
    rw [hget]
    symm
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (R := CFieldSpec.K α) (ι := ℕ)
      (s := Finset.range N) (v := (Nat.cast : ℕ → CFieldSpec.K α))
      (f := (lrtSubresultantGen (toPoly A) (toPoly Dstar) (toPoly Dd) j).coeff k)
      (g := toPoly (cinterpolate pts)) ?_ ?_ ?_ ?_
    · intro x _ y _ h; exact Nat.cast_injective h
    · rw [Finset.card_range, Nat.cast_withBot]
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      rw [Nat.cast_withBot, WithBot.coe_lt_coe]
      have h1 := natDegree_coeff_lrtSubresultantGen_le (toPoly A) (toPoly Dstar) (toPoly Dd) j k
      omega
    · rw [Finset.card_range, Nat.cast_withBot]
      have := degree_toPolyG_cinterpolateG_lt pts hne
      rw [hlen] at this
      simpa [Nat.cast_withBot] using this
    · intro jj hjj
      rw [Finset.mem_range] at hjj
      have hmem : (CField.natCast jj, ((CPolySubresultant.compute Dstar
          (csub A (cscale (CField.natCast jj) Dd))
          (cdeg Dstar) (cdeg Dd) j : DensePoly α) : List α).getD k CCommRing.zero) ∈ pts := by
        rw [hpts, List.mem_map]; exact ⟨jj, List.mem_range.mpr hjj, rfl⟩
      rw [show (jj : CFieldSpec.K α) = CFieldSpec.toK (CField.natCast jj : α) from
          (CFieldSpec.toK_natCast jj).symm]
      rw [eval_toPolyG_cinterpolateG pts hnodup hmem, toK_selectedSubresultant_getD_eq_coeff, hcommute,
        lrtSubresultantGen_eval, hnm, hmm, ← hdd]
  · -- `k > j`: both are `0`
    have hget : (CPolySubresultant.parametric Dstar A Dd (cdeg Dstar) (cdeg Dd) j).getD k [] = [] := by
      rw [CPolySubresultant.parametric, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_none (by rw [List.length_range]; omega)]
      rfl
    rw [hget, toPolyG_nil]
    symm
    rw [lrtSubresultantGen, subresultant, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_range, hk, if_false]

end DeepWiki.SymbolicIntegration
