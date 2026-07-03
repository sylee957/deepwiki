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
open scoped Differential

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

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `toK (cLaurentShiftG η (-(i+1))) = -(i+1) · toK η` for a negative shift. -/
theorem toK_cLaurentShiftG_negCast [CRischField α] (η : α) (i : ℕ) :
    CFieldSpec.toK (cLaurentShiftG η (-(i + 1 : ℤ)))
      = -((i : CFieldSpec.K α) + 1) * CFieldSpec.toK η := by
  have hnat : (-(i + 1 : ℤ)).natAbs = i + 1 := by omega
  rw [cLaurentShiftG, hnat, if_pos (by omega), CFieldSpec.toK_mul, CFieldSpec.toK_neg,
    toK_cnatCastG_laurent]
  push_cast; ring

/-- **M2 (negative power): one Laurent term is an antiderivative.** For `Dt = η·t` and a solved
coefficient `cLaurentIntCoeffG η (-(i+1)) a = some q`, `D_tower(⟦q·t^{-(i+1)}⟧) = ⟦a·t^{-(i+1)}⟧`. Quotient
rule + `crischDESolve` soundness on the negative shift. -/
theorem cIntegrateHyperexpLaurent_neg_term [CRischField α] [CRischFieldSpec α]
    (Dt : CPolyG α) (η : α) (i : ℕ) (a q : α)
    (hDt : toPolyG Dt = Polynomial.C (CFieldSpec.toK η) * Polynomial.X)
    (hsolve : cLaurentIntCoeffG η (-(i + 1 : ℤ)) a = some q) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG ([q] : CPolyG α)) / amG α (toPolyG (cshiftG (i + 1) ([CField.one] : CPolyG α))))
      = amG α (toPolyG ([a] : CPolyG α))
        / amG α (toPolyG (cshiftG (i + 1) ([CField.one] : CPolyG α))) := by
  have hspec := CRischFieldSpec.crischDESolve_spec (cLaurentShiftG η (-(i + 1 : ℤ))) a q hsolve
  rw [toK_cLaurentShiftG_negCast] at hspec
  simp only [toPolyG_cshiftG, toPolyG_cons, toPolyG_nil, mul_zero, add_zero, CFieldSpec.toK_one,
    map_one, mul_one]
  rw [towerFractionFieldDerivG_div, hDt]
  have hXpow : (Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η) * Polynomial.X)
      (Polynomial.X ^ (i + 1)) : (CFieldSpec.K α)[X])
      = ((i + 1 : ℕ) : (CFieldSpec.K α)[X]) * Polynomial.C (CFieldSpec.toK η) * Polynomial.X ^ (i + 1) := by
    rw [Derivation.leibniz_pow, Differential.implicitDeriv_X, nsmul_eq_mul, Nat.add_sub_cancel]
    push_cast; ring
  have hqC : Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η) * Polynomial.X)
      (Polynomial.C (CFieldSpec.toK q)) = Polynomial.C ((CFieldSpec.toK q)′) :=
    Differential.implicitDeriv_C _ _
  rw [hqC, hXpow]
  have hAXne : amG α (Polynomial.X ^ (i + 1) : (CFieldSpec.K α)[X]) ≠ 0 :=
    (map_ne_zero_iff (amG α) (RatFunc.algebraMap_injective _)).mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [show CFieldSpec.toK a = (CFieldSpec.toK q)′ + -((i : CFieldSpec.K α) + 1) * CFieldSpec.toK η
      * CFieldSpec.toK q from hspec.symm]
  simp only [map_add, map_mul, map_natCast, map_pow, map_neg, map_one]
  field_simp
  push_cast
  ring

/-! ### M3 (sum assembly): `D_tower` distributes over a list of solved Laurent terms -/

/-- **The non-negative Laurent sum is an antiderivative.** For a list `l` of `(k, aₖ, qₖ)` where each `qₖ`
solves the shift-`k` RDE, `D_tower(∑ₖ ⟦qₖ·tᵏ⟧) = ∑ₖ ⟦aₖ·tᵏ⟧`. The additive assembly of
`cIntegrateHyperexpLaurent_pos_term` over the term list (`map_list_sum` + per-term M2). -/
theorem towerFractionFieldDerivG_laurent_pos_sum [CRischField α] [CRischFieldSpec α]
    (Dt : CPolyG α) (η : α) (l : List (ℕ × α × α))
    (hDt : toPolyG Dt = Polynomial.C (CFieldSpec.toK η) * Polynomial.X)
    (hall : ∀ t ∈ l, cLaurentIntCoeffG η (t.1 : ℤ) t.2.1 = some t.2.2) :
    towerFractionFieldDerivG Dt
        ((l.map (fun t => amG α (toPolyG (cshiftG t.1 ([t.2.2] : CPolyG α))))).sum)
      = (l.map (fun t => amG α (toPolyG (cshiftG t.1 ([t.2.1] : CPolyG α))))).sum := by
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  exact cIntegrateHyperexpLaurent_pos_term Dt η t.1 t.2.1 t.2.2 hDt (hall t ht)

/-- **The non-negative Laurent solve loop is sound (offset-generalized).** If the `posQ` foldr over
`pos.zipIdx s` (shifts `s, s+1, …`) returns `coeffs`, then `D_tower(⟦tˢ·coeffs⟧) = ⟦tˢ·pos⟧`. Direct
induction on `pos`, splitting the Horner list off the head and applying the single-term M2 identity plus
the induction hypothesis at offset `s+1`. -/
theorem laurentPosGo_sound [CRischField α] [CRischFieldSpec α] (Dt : CPolyG α) (η : α)
    (hDt : toPolyG Dt = Polynomial.C (CFieldSpec.toK η) * Polynomial.X) :
    ∀ (pos coeffs : CPolyG α) (s : ℕ),
      ((pos.zipIdx s).foldr (fun ck acc =>
          match acc with
          | none => none
          | some tail =>
            match cLaurentIntCoeffG η (ck.2 : ℤ) ck.1 with
            | none => none
            | some q => some (q :: tail))
        (some []) = some coeffs) →
      towerFractionFieldDerivG Dt (amG α (toPolyG (cshiftG s coeffs)))
        = amG α (toPolyG (cshiftG s pos)) := by
  intro pos
  induction pos with
  | nil =>
    intro coeffs s h
    simp only [List.zipIdx_nil, List.foldr_nil, Option.some.injEq] at h
    subst h; simp [toPolyG_cshiftG]
  | cons a as ih =>
    intro coeffs s h
    rw [List.zipIdx_cons, List.foldr_cons] at h
    cases hrest : (as.zipIdx (s + 1)).foldr (fun ck acc =>
        match acc with
        | none => none
        | some tail =>
          match cLaurentIntCoeffG η (ck.2 : ℤ) ck.1 with
          | none => none
          | some q => some (q :: tail)) (some []) with
    | none => rw [hrest] at h; simp at h
    | some restCoeffs =>
      rw [hrest] at h
      cases hq : cLaurentIntCoeffG η (s : ℤ) a with
      | none => rw [hq] at h; simp at h
      | some q =>
        rw [hq] at h
        rw [Option.some.injEq] at h
        subst h
        have hsplit1 : toPolyG (cshiftG s (q :: restCoeffs))
            = toPolyG (cshiftG s ([q] : CPolyG α)) + toPolyG (cshiftG (s + 1) restCoeffs) := by
          simp only [toPolyG_cshiftG, toPolyG_cons, toPolyG_nil, mul_zero, add_zero, pow_succ]; ring
        have hsplit2 : toPolyG (cshiftG s (a :: as))
            = toPolyG (cshiftG s ([a] : CPolyG α)) + toPolyG (cshiftG (s + 1) as) := by
          simp only [toPolyG_cshiftG, toPolyG_cons, toPolyG_nil, mul_zero, add_zero, pow_succ]; ring
        rw [hsplit1, map_add, map_add, hsplit2, map_add,
          cIntegrateHyperexpLaurent_pos_term Dt η s a q hDt hq, ih restCoeffs (s + 1) hrest]

/-- **Laurent soundness, polynomial case (`neg = []`).** For `Dt = η·t`, if
`cIntegrateHyperexpLaurentG η pos [] = some (num, den)`, then `D_tower(⟦num/den⟧) = ⟦pos⟧` — the antiderivative
identity for a purely non-negative hyperexponential Laurent integrand (`den = 1`). -/
theorem cIntegrateHyperexpLaurentG_pos_sound [CRischField α] [CRischFieldSpec α]
    (Dt : CPolyG α) (η : α) (pos num den : CPolyG α)
    (hDt : toPolyG Dt = Polynomial.C (CFieldSpec.toK η) * Polynomial.X)
    (hsome : cIntegrateHyperexpLaurentG η pos [] = some (num, den)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG num) / amG α (toPolyG den))
      = amG α (toPolyG pos) := by
  rw [cIntegrateHyperexpLaurentG] at hsome
  simp only [List.length_nil, List.zipIdx_nil, List.foldr_nil] at hsome
  split at hsome
  · rename_i negC posCoeffs hnegeq hp
    simp only [Option.some.injEq] at hnegeq
    subst hnegeq
    simp only [List.reverse_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨hnum, hden⟩ := hsome
    subst hnum; subst hden
    have hden1 : toPolyG (cshiftG (0 : ℕ) ([CField.one] : CPolyG α)) = 1 := by
      show toPolyG ([CField.one] : CPolyG α) = 1
      rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
    rw [hden1, map_one, div_one]
    simpa using laurentPosGo_sound Dt η hDt pos posCoeffs 0 hp
  · simp at hsome

end DeepWiki.SymbolicIntegration
