import DeepWiki.SymbolicIntegration.Engine.LaurentSoundness

/-! # Laurent special-part soundness

The special-denominator bridge from `cHyperexpSpecialNeg` to the general Laurent integrator.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `b / ds` has a nonzero proper special denominator. -/
structure IsProperSpecialPart (b ds : DensePoly α) : Prop where
  /-- `ds` is nonzero according to `cisZero`. -/
  nz : cisZero ds = false
  /-- The special denominator has positive degree. -/
  mpos : 0 < cdeg ds
  /-- The leading coefficient of `ds` denotes a nonzero field element. -/
  lc_nz : CFieldSpec.toK (clead ds) ≠ 0
  /-- The numerator `b` has no coefficients at or above `cdeg ds`. -/
  proper : ∀ j, cdeg ds ≤ j → (b : List α).getD j CCommRing.zero = CCommRing.zero

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `ds` is the monomial denominator of a proper special part `b / ds`. -/
structure IsSpecialDenominator (b ds : DensePoly α) : Prop extends IsProperSpecialPart b ds where
  /-- `ds` denotes its leading coefficient times `X ^ cdeg ds`. -/
  mono : toPoly ds = Polynomial.C (CFieldSpec.toK (clead ds)) * Polynomial.X ^ cdeg ds

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **`cHyperexpSpecialNeg` correctness (polynomial identity).** For a special denominator `dₛ = c·tᵐ`
(read via `clead`/`cdeg`) with `c ≠ 0` and a proper numerator `b` (degree `< m`),
`C(c) · toPoly (cHyperexpSpecialNeg b dₛ).reverse = toPoly b`. -/
theorem cHyperexpSpecialNegG_reverse_smul [CRischField α] (b ds : DensePoly α)
    (hsp : IsProperSpecialPart b ds) :
    Polynomial.C (CFieldSpec.toK (clead ds)) * toPoly (cHyperexpSpecialNeg b ds).reverse
      = toPoly b := by
  have hunfold : cHyperexpSpecialNeg b ds
      = (List.range (cdeg ds)).map (fun i =>
          CCommRing.mul ((b : List α).getD (cdeg ds - 1 - i) CCommRing.zero) (CField.inv (clead ds))) := by
    rw [cHyperexpSpecialNeg, if_neg (by simp [hsp.nz]), if_neg (Nat.ne_of_gt hsp.mpos)]
  have hlen : (cHyperexpSpecialNeg b ds).length = cdeg ds := by
    rw [hunfold, List.length_map, List.length_range]
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_C_mul, toPolyG_coeff, toPolyG_coeff]
  simp only [toR_eq_toK]
  by_cases hj : j < cdeg ds
  · have hget : (cHyperexpSpecialNeg b ds).reverse.getD j CCommRing.zero
        = CCommRing.mul ((b : List α).getD j CCommRing.zero) (CField.inv (clead ds)) := by
      rw [List.getD_eq_getElem?_getD, hunfold, List.getElem?_reverse
        (by rw [List.length_map, List.length_range]; exact hj),
        List.length_map, List.length_range, List.getElem?_map,
        List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      congr 2
      omega
    rw [hget, CFieldSpec.toK_mul, CFieldSpec.toK_inv]
    field_simp [hsp.lc_nz]
  · simp only [not_lt] at hj
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [List.length_reverse, hlen]; exact hj), Option.getD_none,
      CFieldSpec.toK_zero, mul_zero, hsp.proper j hj, CFieldSpec.toK_zero]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The special-part connector.** For a monomial special denominator `dₛ = c·tᵐ` with `c ≠ 0` and a
proper `b`, `⟦(cHyperexpSpecialNeg b dₛ).reverse⟧/⟦tᵐ⟧ = ⟦b/dₛ⟧` — the negative Laurent coefficients read
the special part `b/dₛ` faithfully. Cross-multiplies the polynomial identity through `am`. -/
theorem cHyperexpSpecialNegG_frac [CRischField α] (b ds : DensePoly α)
    (hds : IsSpecialDenominator b ds) :
    am α (toPoly (cHyperexpSpecialNeg b ds).reverse)
        / am α (toPoly (cshift (cHyperexpSpecialNeg b ds).length ([CCommRing.one] : DensePoly α)))
      = am α (toPoly b) / am α (toPoly ds) := by
  have hlen : (cHyperexpSpecialNeg b ds).length = cdeg ds := by
    rw [cHyperexpSpecialNeg, if_neg (by simp [hds.nz]), if_neg (Nat.ne_of_gt hds.mpos),
      List.length_map, List.length_range]
  have hpoly := cHyperexpSpecialNegG_reverse_smul b ds hds.toIsProperSpecialPart
  have hdenpow : toPoly (cshift (cHyperexpSpecialNeg b ds).length ([CCommRing.one] : DensePoly α))
      = (Polynomial.X : (CFieldSpec.K α)[X]) ^ cdeg ds := by
    rw [hlen]
    simp only [denote, mul_zero, add_zero, map_one, mul_one]
  have hXne : am α ((Polynomial.X : (CFieldSpec.K α)[X]) ^ cdeg ds) ≠ 0 :=
    (map_ne_zero_iff (am α) (RatFunc.algebraMap_injective _)).mpr (pow_ne_zero _ Polynomial.X_ne_zero)
  have hdsne : am α (toPoly ds) ≠ 0 := by
    rw [hds.mono]
    exact (map_ne_zero_iff (am α) (RatFunc.algebraMap_injective _)).mpr
      (mul_ne_zero (by simpa using hds.lc_nz) (pow_ne_zero _ Polynomial.X_ne_zero))
  rw [hdenpow, div_eq_div_iff hXne hdsne, hds.mono, map_mul, ← mul_assoc,
    mul_comm (am α (toPoly (cHyperexpSpecialNeg b ds).reverse)) (am α (Polynomial.C _)),
    ← map_mul, hpoly]

/-- **hLaurField discharged (special+polynomial hyperexp integrand).** For `Dt = η·t`, a monomial special
denominator `dₛ = c·tᵐ` (`c ≠ 0`) and proper `b`, if `cIntegrateHyperexpLaurent η fp (cHyperexpSpecialNeg
b dₛ) = some (lnum, lden)` then `D_tower(⟦lnum/lden⟧) = ⟦fp⟧ + ⟦b/dₛ⟧` — the Laurent integrator is a genuine
antiderivative of the full special+polynomial part `fp + b/dₛ`. Composes the general Laurent soundness with
the special-part connector. -/
theorem cIntegrateHyperexpLaurentG_special_sound [CRischField α] [CRischFieldSpec α]
    (Dt : DensePoly α) (η : α) (fp b ds lnum lden : DensePoly α)
    (hDt : IsHyperexpMonomial Dt η) (hds : IsSpecialDenominator b ds)
    (hsome : cIntegrateHyperexpLaurent η fp (cHyperexpSpecialNeg b ds) = some (lnum, lden)) :
    towerFractionFieldDeriv Dt (am α (toPoly lnum) / am α (toPoly lden))
      = am α (toPoly fp) + am α (toPoly b) / am α (toPoly ds) := by
  rw [cIntegrateHyperexpLaurentG_sound Dt η fp (cHyperexpSpecialNeg b ds) lnum lden hDt hsome,
    cHyperexpSpecialNegG_frac b ds hds]

end DeepWiki.SymbolicIntegration
