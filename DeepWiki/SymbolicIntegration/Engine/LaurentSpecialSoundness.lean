import DeepWiki.SymbolicIntegration.Engine.LaurentSoundness

/-! # Laurent special-part soundness

The special-denominator bridge from `cHyperexpSpecialNegG` to the general Laurent integrator.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `b / ds` has a nonzero proper special denominator. -/
structure IsProperSpecialPart (b ds : CPoly α) : Prop where
  /-- `ds` is nonzero according to `cisZeroG`. -/
  nz : cisZeroG ds = false
  /-- The special denominator has positive degree. -/
  mpos : 0 < cdegG ds
  /-- The leading coefficient of `ds` denotes a nonzero field element. -/
  clead : CFieldSpec.toK (cleadG ds) ≠ 0
  /-- The numerator `b` has no coefficients at or above `cdegG ds`. -/
  proper : ∀ j, cdegG ds ≤ j → (b : List α).getD j CField.zero = CField.zero

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `ds` is the monomial denominator of a proper special part `b / ds`. -/
structure IsSpecialDenominator (b ds : CPoly α) : Prop extends IsProperSpecialPart b ds where
  /-- `ds` denotes its leading coefficient times `X ^ cdegG ds`. -/
  mono : toPolyG ds = Polynomial.C (CFieldSpec.toK (cleadG ds)) * Polynomial.X ^ cdegG ds

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **`cHyperexpSpecialNegG` correctness (polynomial identity).** For a special denominator `dₛ = c·tᵐ`
(read via `cleadG`/`cdegG`) with `c ≠ 0` and a proper numerator `b` (degree `< m`),
`C(c) · toPolyG (cHyperexpSpecialNegG b dₛ).reverse = toPolyG b`. -/
theorem cHyperexpSpecialNegG_reverse_smul [CRischField α] (b ds : CPoly α)
    (hsp : IsProperSpecialPart b ds) :
    Polynomial.C (CFieldSpec.toK (cleadG ds)) * toPolyG (cHyperexpSpecialNegG b ds).reverse
      = toPolyG b := by
  have hunfold : cHyperexpSpecialNegG b ds
      = (List.range (cdegG ds)).map (fun i =>
          CField.mul ((b : List α).getD (cdegG ds - 1 - i) CField.zero) (CField.inv (cleadG ds))) := by
    rw [cHyperexpSpecialNegG, if_neg (by simp [hsp.nz]), if_neg (Nat.ne_of_gt hsp.mpos)]
  have hlen : (cHyperexpSpecialNegG b ds).length = cdegG ds := by
    rw [hunfold, List.length_map, List.length_range]
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_C_mul, toPolyG_coeff, toPolyG_coeff]
  by_cases hj : j < cdegG ds
  · have hget : (cHyperexpSpecialNegG b ds).reverse.getD j CField.zero
        = CField.mul ((b : List α).getD j CField.zero) (CField.inv (cleadG ds)) := by
      rw [List.getD_eq_getElem?_getD, hunfold, List.getElem?_reverse
        (by rw [List.length_map, List.length_range]; exact hj),
        List.length_map, List.length_range, List.getElem?_map,
        List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      congr 2
      omega
    rw [hget, CFieldSpec.toK_mul, CFieldSpec.toK_inv]
    field_simp [hsp.clead]
  · simp only [not_lt] at hj
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [List.length_reverse, hlen]; exact hj), Option.getD_none,
      CFieldSpec.toK_zero, mul_zero, hsp.proper j hj, CFieldSpec.toK_zero]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The special-part connector.** For a monomial special denominator `dₛ = c·tᵐ` with `c ≠ 0` and a
proper `b`, `⟦(cHyperexpSpecialNegG b dₛ).reverse⟧/⟦tᵐ⟧ = ⟦b/dₛ⟧` — the negative Laurent coefficients read
the special part `b/dₛ` faithfully. Cross-multiplies the polynomial identity through `amG`. -/
theorem cHyperexpSpecialNegG_frac [CRischField α] (b ds : CPoly α)
    (hds : IsSpecialDenominator b ds) :
    amG α (toPolyG (cHyperexpSpecialNegG b ds).reverse)
        / amG α (toPolyG (cshiftG (cHyperexpSpecialNegG b ds).length ([CField.one] : CPoly α)))
      = amG α (toPolyG b) / amG α (toPolyG ds) := by
  have hlen : (cHyperexpSpecialNegG b ds).length = cdegG ds := by
    rw [cHyperexpSpecialNegG, if_neg (by simp [hds.nz]), if_neg (Nat.ne_of_gt hds.mpos),
      List.length_map, List.length_range]
  have hpoly := cHyperexpSpecialNegG_reverse_smul b ds hds.toIsProperSpecialPart
  have hdenpow : toPolyG (cshiftG (cHyperexpSpecialNegG b ds).length ([CField.one] : CPoly α))
      = (Polynomial.X : (CFieldSpec.K α)[X]) ^ cdegG ds := by
    rw [hlen]
    simp only [denote, mul_zero, add_zero, map_one, mul_one]
  have hXne : amG α ((Polynomial.X : (CFieldSpec.K α)[X]) ^ cdegG ds) ≠ 0 :=
    (map_ne_zero_iff (amG α) (RatFunc.algebraMap_injective _)).mpr (pow_ne_zero _ Polynomial.X_ne_zero)
  have hdsne : amG α (toPolyG ds) ≠ 0 := by
    rw [hds.mono]
    exact (map_ne_zero_iff (amG α) (RatFunc.algebraMap_injective _)).mpr
      (mul_ne_zero (by simpa using hds.clead) (pow_ne_zero _ Polynomial.X_ne_zero))
  rw [hdenpow, div_eq_div_iff hXne hdsne, hds.mono, map_mul, ← mul_assoc,
    mul_comm (amG α (toPolyG (cHyperexpSpecialNegG b ds).reverse)) (amG α (Polynomial.C _)),
    ← map_mul, hpoly]

/-- **hLaurField discharged (special+polynomial hyperexp integrand).** For `Dt = η·t`, a monomial special
denominator `dₛ = c·tᵐ` (`c ≠ 0`) and proper `b`, if `cIntegrateHyperexpLaurentG η fp (cHyperexpSpecialNegG
b dₛ) = some (lnum, lden)` then `D_tower(⟦lnum/lden⟧) = ⟦fp⟧ + ⟦b/dₛ⟧` — the Laurent integrator is a genuine
antiderivative of the full special+polynomial part `fp + b/dₛ`. Composes the general Laurent soundness with
the special-part connector. -/
theorem cIntegrateHyperexpLaurentG_special_sound [CRischField α] [CRischFieldSpec α]
    (Dt : CPoly α) (η : α) (fp b ds lnum lden : CPoly α)
    (hDt : IsHyperexpMonomial Dt η) (hds : IsSpecialDenominator b ds)
    (hsome : cIntegrateHyperexpLaurentG η fp (cHyperexpSpecialNegG b ds) = some (lnum, lden)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG lnum) / amG α (toPolyG lden))
      = amG α (toPolyG fp) + amG α (toPolyG b) / amG α (toPolyG ds) := by
  rw [cIntegrateHyperexpLaurentG_sound Dt η fp (cHyperexpSpecialNegG b ds) lnum lden hDt hsome,
    cHyperexpSpecialNegG_frac b ds hds]

end DeepWiki.SymbolicIntegration
