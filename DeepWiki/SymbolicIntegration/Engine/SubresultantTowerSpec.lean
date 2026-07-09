import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtGeneralDerivation
import DeepWiki.SymbolicIntegration.Engine.SubresultantSpec
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.Engine.LogPartTowerSoundness

/-! # Connecting the computable parametric LRT subresultant to the abstract theory (G4c)

`cSubresultantParam Dstar A Dd n m j` is the engine's parametric LRT log argument `Sⱼ(z,t)`: its `k`-th
entry is the `z`-polynomial coefficient of `tᵏ`, computed by interpolation in `z` of the coefficient of
`cSubresultant Dstar (A − z·Dd) n m j`. This file connects it to the general-derivation abstract
subresultant `subresultant (toPoly Dstar) (toPoly A − C z · B) n m j` (`B = toPoly Dd`), building on
the L4b subresultant certification `toPolyG_cSubresultantG`. See `docs/generalize-lrt-derivation.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **Per-value subresultant agreement.** The `k`-th `t`-coefficient of the computable subresultant
`cSubresultant Dstar (A − c·Dd) n m j`, read through `toK`, equals the `k`-th `t`-coefficient of the
abstract subresultant of `(Dstar, A − c·B)` (`B = toPoly Dd`), for any value `c`. Immediate from the L4b
certification `toPolyG_cSubresultantG` plus the `csub`/`cscale` bridges — no interpolation needed (this is
the per-node fact the interpolation extends to all residues). -/
theorem toK_cSubresultantG_getD_eq_coeff (Dstar A Dd : DensePoly α) (c : α) (n m j k : ℕ) :
    CFieldSpec.toK
        (((cSubresultant Dstar (csub A (cscale c Dd)) n m j : DensePoly α) : List α).getD k
          CField.zero)
      = (subresultant (toPoly Dstar)
          (toPoly A - C (CFieldSpec.toK c) * toPoly Dd) n m j).coeff k := by
  rw [← ccrZero_eq_cfield, ← toR_eq_toK, ← toPolyG_coeff]
  simp only [denote]

variable [CDiffField α] [CDiffFieldSpec α]

/-- The per-value subresultant agreement with the **tower derivation** `Dd = cmonomialDeriv Dt Dstar`, so
`B = implicitDeriv (toPoly Dt) (toPoly Dstar)` — the form used by `cLrtLogArg`. -/
theorem toK_cSubresultantG_getD_eq_coeff_monomial (Dt Dstar A : DensePoly α) (c : α) (n m j k : ℕ) :
    CFieldSpec.toK
        (((cSubresultant Dstar (csub A (cscale c (cmonomialDeriv Dt Dstar))) n m j : DensePoly α) :
            List α).getD k CField.zero)
      = (subresultant (toPoly Dstar)
          (toPoly A - C (CFieldSpec.toK c)
            * Differential.implicitDeriv (toPoly Dt) (toPoly Dstar)) n m j).coeff k := by
  rw [toK_cSubresultantG_getD_eq_coeff]
  simp only [denote]

omit [CDiffField α] [CDiffFieldSpec α] in
open scoped Classical in
/-- **The parametric-subresultant certification (G4c).** The `k`-th entry of the engine's parametric log
argument `cSubresultantParam Dstar A Dd (cdeg Dstar) (cdeg Dd) j` (a `z`-polynomial) equals the `k`-th
`t`-coefficient of the abstract `lrtSubresultantGen (toPoly A) (toPoly Dstar) (toPoly Dd) j`, when
`Dd`'s degree matches the formal degree `deg Dstar − 1`. Via interpolation uniqueness: both `z`-polynomials
have degree `< N = cdeg Dstar + cdeg Dd + 1` (`natDegree_coeff_lrtSubresultantGen_le` /
`degree_toPolyG_cinterpolateG_lt`) and agree at the `N` integer nodes (per-value agreement + coefficient/eval
commutation + `lrtSubresultantGen_eval`). So the engine's interpolated log argument IS the abstract
subresultant coefficient. -/
theorem toPolyG_cSubresultantParam_getD [CharZero (CFieldSpec.K α)] (Dstar A Dd : DensePoly α) (j k : ℕ)
    (hm : cdeg Dd = cdeg Dstar - 1) :
    toPoly ((cSubresultantParam Dstar A Dd (cdeg Dstar) (cdeg Dd) j).getD k [])
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
    have hget : (cSubresultantParam Dstar A Dd (cdeg Dstar) (cdeg Dd) j).getD k []
        = cinterpolate ((List.range N).map (fun jj =>
            (cnatCast jj, ((cSubresultant Dstar (csub A (cscale (cnatCast jj) Dd))
              (cdeg Dstar) (cdeg Dd) j : DensePoly α) : List α).getD k CField.zero))) := by
      rw [cSubresultantParam]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
      rfl
    set pts : List (α × α) := (List.range N).map (fun jj =>
      (cnatCast jj, ((cSubresultant Dstar (csub A (cscale (cnatCast jj) Dd))
        (cdeg Dstar) (cdeg Dd) j : DensePoly α) : List α).getD k CField.zero)) with hpts
    have hlen : pts.length = N := by rw [hpts, List.length_map, List.length_range]
    have hne : pts ≠ [] := by rw [hpts]; simp [hN]
    have hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup := by
      have : pts.map (fun p => CFieldSpec.toK p.1)
          = (List.range N).map (Nat.cast : ℕ → CFieldSpec.K α) := by
        rw [hpts, List.map_map]; apply List.map_congr_left; intro jj _
        simp only [Function.comp_apply, DensePoly.toK_cnatCastG]
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
      have hmem : (cnatCast jj, ((cSubresultant Dstar (csub A (cscale (cnatCast jj) Dd))
          (cdeg Dstar) (cdeg Dd) j : DensePoly α) : List α).getD k CField.zero) ∈ pts := by
        rw [hpts, List.mem_map]; exact ⟨jj, List.mem_range.mpr hjj, rfl⟩
      rw [show (jj : CFieldSpec.K α) = CFieldSpec.toK (cnatCast jj : α) from
          (DensePoly.toK_cnatCastG jj).symm]
      rw [eval_toPolyG_cinterpolateG pts hnodup hmem, toK_cSubresultantG_getD_eq_coeff, hcommute,
        lrtSubresultantGen_eval, hnm, hmm, ← hdd]
  · -- `k > j`: both are `0`
    have hget : (cSubresultantParam Dstar A Dd (cdeg Dstar) (cdeg Dd) j).getD k [] = [] := by
      rw [cSubresultantParam, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_none (by rw [List.length_range]; omega)]
      rfl
    rw [hget, toPolyG_nil]
    symm
    rw [lrtSubresultantGen, subresultant, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_range, hk, if_false]

end DeepWiki.SymbolicIntegration
