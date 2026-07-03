import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.LaurentCore
import DeepWiki.SymbolicIntegration.Computable.RischFieldSpec

/-! # Laurent integrator soundness (M1: the derivation kernel)

Toward discharging the hyperexp assembler's `hLaurField`: the base↔tower derivation bridge on polynomial
images and the hyperexponential power rule `D(tᵏ) = k·η·tᵏ`. See `docs/laurent-soundness.md`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **The tower derivative of a polynomial image is the image of `cmonomialDeriv`**:
`D_tower(⟦p⟧) = ⟦cmonomialDeriv Dt p⟧`. Grounds every Laurent-term computation at the polynomial level
(`extendDeriv_algebraMap` + `toPolyG_cmonomialDeriv`). -/
theorem towerFractionFieldDerivG_amG_poly (Dt p : CPolyG α) :
    towerFractionFieldDerivG Dt (amG α (toPolyG p)) = amG α (toPolyG (cmonomialDeriv Dt p)) := by
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap, toPolyG_cmonomialDeriv]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `toK (cnatCastG k) = (k : K)` (inline; the `k`-fold `CField.one` sum reads as the natural cast). -/
theorem toK_cnatCastG_laurent (k : ℕ) :
    CFieldSpec.toK (CPolyG.cnatCastG k : α) = (k : CFieldSpec.K α) := by
  induction k with
  | zero => rw [CPolyG.cnatCastG, CFieldSpec.toK_zero, Nat.cast_zero]
  | succ n ih => rw [CPolyG.cnatCastG, CFieldSpec.toK_add, CFieldSpec.toK_one, ih, Nat.cast_succ,
      add_comm]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `toK (cLaurentShiftG η k) = k · toK η` for a non-negative shift `k : ℕ`. -/
theorem toK_cLaurentShiftG_natCast [CRischField α] (η : α) (k : ℕ) :
    CFieldSpec.toK (cLaurentShiftG η (k : ℤ)) = (k : CFieldSpec.K α) * CFieldSpec.toK η := by
  rw [cLaurentShiftG, Int.natAbs_natCast, if_neg (Int.not_lt.mpr (Int.natCast_nonneg k)),
    CFieldSpec.toK_mul, toK_cnatCastG_laurent]

/-- **M2 (non-negative power): one Laurent term is an antiderivative.** For a hyperexponential monomial
`Dt = η·t` and a solved coefficient `cLaurentIntCoeffG η k aₖ = some qₖ` (`k : ℕ`),
`D_tower(⟦qₖ·tᵏ⟧) = ⟦aₖ·tᵏ⟧`. Product/power rule + `crischDESolve` soundness collapse `(qₖ)′ + k·η·qₖ` to
`aₖ`. -/
theorem cIntegrateHyperexpLaurent_pos_term [CRischField α] [CRischFieldSpec α]
    (Dt : CPolyG α) (η : α) (k : ℕ) (ak qk : α)
    (hDt : toPolyG Dt = Polynomial.C (CFieldSpec.toK η) * Polynomial.X)
    (hsolve : cLaurentIntCoeffG η (k : ℤ) ak = some qk) :
    towerFractionFieldDerivG Dt (amG α (toPolyG (cshiftG k ([qk] : CPolyG α))))
      = amG α (toPolyG (cshiftG k ([ak] : CPolyG α))) := by
  rw [towerFractionFieldDerivG_amG_poly]
  congr 1
  have hspec := CRischFieldSpec.crischDESolve_spec (cLaurentShiftG η (k : ℤ)) ak qk hsolve
  rw [toK_cLaurentShiftG_natCast] at hspec
  rw [toPolyG_cmonomialDeriv, hDt]
  simp only [toPolyG_cshiftG, toPolyG_cons, toPolyG_nil, mul_zero, add_zero]
  rw [show (Polynomial.X ^ k * Polynomial.C (CFieldSpec.toK qk) : (CFieldSpec.K α)[X])
      = Polynomial.C (CFieldSpec.toK qk) * Polynomial.X ^ k from by ring,
    Derivation.leibniz, Derivation.leibniz_pow, Differential.implicitDeriv_X,
    Differential.implicitDeriv_C]
  rw [← hspec, map_add, map_mul, map_mul]
  simp only [smul_eq_mul, nsmul_eq_mul, map_natCast]
  cases k with
  | zero => simp
  | succ m => rw [Nat.succ_sub_one, pow_succ]; push_cast; ring

end DeepWiki.SymbolicIntegration
