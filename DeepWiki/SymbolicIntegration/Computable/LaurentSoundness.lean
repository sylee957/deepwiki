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

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `Dt` is the monomial hyperexponential derivative `η * t`. -/
abbrev IsHyperexpMonomial (Dt : CPolyG α) (η : α) : Prop :=
  toPolyG Dt = Polynomial.C (CFieldSpec.toK η) * Polynomial.X

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `b / ds` has a nonzero proper special denominator. -/
structure IsProperSpecialPart (b ds : CPolyG α) : Prop where
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
structure IsSpecialDenominator (b ds : CPolyG α) : Prop extends IsProperSpecialPart b ds where
  /-- `ds` denotes its leading coefficient times `X ^ cdegG ds`. -/
  mono : toPolyG ds = Polynomial.C (CFieldSpec.toK (cleadG ds)) * Polynomial.X ^ cdegG ds

/-- **The tower derivative of a polynomial image is the image of `cmonomialDeriv`**:
`D_tower(⟦p⟧) = ⟦cmonomialDeriv Dt p⟧`. Grounds every Laurent-term computation at the polynomial level
(`extendDeriv_algebraMap` + `toPolyG_cmonomialDeriv`). -/
theorem towerFractionFieldDerivG_amG_poly (Dt p : CPolyG α) :
    towerFractionFieldDerivG Dt (amG α (toPolyG p)) = amG α (toPolyG (cmonomialDeriv Dt p)) := by
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap]
  simp only [denote]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `toK (cLaurentShiftG η k) = k · toK η` for a non-negative shift `k : ℕ`. -/
theorem toK_cLaurentShiftG_natCast [CRischField α] (η : α) (k : ℕ) :
    CFieldSpec.toK (cLaurentShiftG η (k : ℤ)) = (k : CFieldSpec.K α) * CFieldSpec.toK η := by
  rw [cLaurentShiftG, Int.natAbs_natCast, if_neg (Int.not_lt.mpr (Int.natCast_nonneg k)),
    CFieldSpec.toK_mul, CPolyG.toK_cnatCastG]

/-- **M2 (non-negative power): one Laurent term is an antiderivative.** For a hyperexponential monomial
`Dt = η·t` and a solved coefficient `cLaurentIntCoeffG η k aₖ = some qₖ` (`k : ℕ`),
`D_tower(⟦qₖ·tᵏ⟧) = ⟦aₖ·tᵏ⟧`. Product/power rule + `crischDESolve` soundness collapse `(qₖ)′ + k·η·qₖ` to
`aₖ`. -/
theorem cIntegrateHyperexpLaurent_pos_term [CRischField α] [CRischFieldSpec α]
    (Dt : CPolyG α) (η : α) (k : ℕ) (ak qk : α)
    (hDt : IsHyperexpMonomial Dt η)
    (hsolve : cLaurentIntCoeffG η (k : ℤ) ak = some qk) :
    towerFractionFieldDerivG Dt (amG α (toPolyG (cshiftG k ([qk] : CPolyG α))))
      = amG α (toPolyG (cshiftG k ([ak] : CPolyG α))) := by
  rw [towerFractionFieldDerivG_amG_poly]
  congr 1
  have hspec := CRischFieldSpec.crischDESolve_spec (cLaurentShiftG η (k : ℤ)) ak qk hsolve
  rw [toK_cLaurentShiftG_natCast] at hspec
  rw [toPolyG_cmonomialDeriv, hDt]
  simp only [denote, mul_zero, add_zero]
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
    CPolyG.toK_cnatCastG]
  push_cast; ring

/-- **M2 (negative power): one Laurent term is an antiderivative.** For `Dt = η·t` and a solved
coefficient `cLaurentIntCoeffG η (-(i+1)) a = some q`, `D_tower(⟦q·t^{-(i+1)}⟧) = ⟦a·t^{-(i+1)}⟧`. Quotient
rule + `crischDESolve` soundness on the negative shift. -/
theorem cIntegrateHyperexpLaurent_neg_term [CRischField α] [CRischFieldSpec α]
    (Dt : CPolyG α) (η : α) (i : ℕ) (a q : α)
    (hDt : IsHyperexpMonomial Dt η)
    (hsolve : cLaurentIntCoeffG η (-(i + 1 : ℤ)) a = some q) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG ([q] : CPolyG α)) / amG α (toPolyG (cshiftG (i + 1) ([CField.one] : CPolyG α))))
      = amG α (toPolyG ([a] : CPolyG α))
        / amG α (toPolyG (cshiftG (i + 1) ([CField.one] : CPolyG α))) := by
  have hspec := CRischFieldSpec.crischDESolve_spec (cLaurentShiftG η (-(i + 1 : ℤ))) a q hsolve
  rw [toK_cLaurentShiftG_negCast] at hspec
  simp only [denote, mul_zero, add_zero, map_one, mul_one]
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
    (hDt : IsHyperexpMonomial Dt η)
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
    (hDt : IsHyperexpMonomial Dt η) :
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
          simp only [denote, mul_zero, add_zero, pow_succ]; ring
        have hsplit2 : toPolyG (cshiftG s (a :: as))
            = toPolyG (cshiftG s ([a] : CPolyG α)) + toPolyG (cshiftG (s + 1) as) := by
          simp only [denote, mul_zero, add_zero, pow_succ]; ring
        rw [hsplit1, map_add, map_add, hsplit2, map_add,
          cIntegrateHyperexpLaurent_pos_term Dt η s a q hDt hq, ih restCoeffs (s + 1) hrest]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Top-coefficient split through `toPolyG`: `toPolyG (p ++ q) = toPolyG p + Xᵖ·ˡᵉⁿ · toPolyG q`. -/
theorem toPolyG_append_laurent (p q : CPolyG α) :
    toPolyG (p ++ q) = toPolyG p + Polynomial.X ^ (p : List α).length * toPolyG q := by
  induction p with
  | nil => simp
  | cons a as ih =>
    show toPolyG (a :: (as ++ q)) = _
    rw [toPolyG_cons, ih, toPolyG_cons, List.length_cons, pow_succ]; ring

omit [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The solve-loop preserves length: a successful `Laurent` foldr returns as many coefficients as inputs. -/
theorem laurentGo_length [CRischField α] (η : α) (sh : ℕ → ℤ) :
    ∀ (l coeffs : List α) (s : ℕ),
      ((l.zipIdx s).foldr (fun ck acc =>
          match acc with
          | none => none
          | some tail =>
            match cLaurentIntCoeffG η (sh ck.2) ck.1 with
            | none => none
            | some q => some (q :: tail)) (some []) = some coeffs) →
      coeffs.length = l.length := by
  intro l
  induction l with
  | nil => intro coeffs s h; simp only [List.zipIdx_nil, List.foldr_nil, Option.some.injEq] at h;
           subst h; rfl
  | cons a as ih =>
    intro coeffs s h
    rw [List.zipIdx_cons, List.foldr_cons] at h
    cases hrest : (as.zipIdx (s + 1)).foldr (fun ck acc =>
        match acc with
        | none => none
        | some tail =>
          match cLaurentIntCoeffG η (sh ck.2) ck.1 with
          | none => none
          | some q => some (q :: tail)) (some []) with
    | none => rw [hrest] at h; simp at h
    | some restCoeffs =>
      rw [hrest] at h
      cases hq : cLaurentIntCoeffG η (sh s) a with
      | none => rw [hq] at h; simp at h
      | some q =>
        rw [hq, Option.some.injEq] at h
        subst h
        simp only [List.length_cons, ih restCoeffs (s + 1) hrest]

/-- **The negative Laurent solve loop is sound (offset-generalized).** If the `negQ` foldr over
`neg.zipIdx s` (shifts `-(s+1), -(s+2), …`) returns `negCoeffs`, then over the fixed denominator
`t^(s+neg.length)`, `D_tower(⟦negCoeffs.reverse⟧/⟦t^(s+len)⟧) = ⟦neg.reverse⟧/⟦t^(s+len)⟧`. The head splits
off the reversed list as `⟦q⟧/t^(s+1)` (neg-term M2) plus the tail at offset `s+1` (same denominator, IH). -/
theorem laurentNegGo_sound [CRischField α] [CRischFieldSpec α] (Dt : CPolyG α) (η : α)
    (hDt : IsHyperexpMonomial Dt η) :
    ∀ (neg negCoeffs : List α) (s : ℕ),
      ((neg.zipIdx s).foldr (fun ck acc =>
          match acc with
          | none => none
          | some tail =>
            match cLaurentIntCoeffG η (-(ck.2 + 1 : ℤ)) ck.1 with
            | none => none
            | some q => some (q :: tail)) (some []) = some negCoeffs) →
      towerFractionFieldDerivG Dt
          (amG α (toPolyG negCoeffs.reverse)
            / amG α (toPolyG (cshiftG (s + neg.length) ([CField.one] : CPolyG α))))
        = amG α (toPolyG neg.reverse)
          / amG α (toPolyG (cshiftG (s + neg.length) ([CField.one] : CPolyG α))) := by
  intro neg
  induction neg with
  | nil =>
    intro negCoeffs s h
    simp only [List.zipIdx_nil, List.foldr_nil, Option.some.injEq] at h
    subst h; simp
  | cons a as ih =>
    intro negCoeffs s h
    rw [List.zipIdx_cons, List.foldr_cons] at h
    cases hrest : (as.zipIdx (s + 1)).foldr (fun ck acc =>
        match acc with
        | none => none
        | some tail =>
          match cLaurentIntCoeffG η (-(ck.2 + 1 : ℤ)) ck.1 with
          | none => none
          | some q => some (q :: tail)) (some []) with
    | none => rw [hrest] at h; simp at h
    | some restCoeffs =>
      rw [hrest] at h
      cases hq : cLaurentIntCoeffG η (-(s + 1 : ℤ)) a with
      | none => rw [hq] at h; simp at h
      | some q =>
        rw [hq, Option.some.injEq] at h
        subst h
        have hlen : restCoeffs.length = as.length := laurentGo_length η _ as restCoeffs (s + 1) hrest
        have hXne : amG α (Polynomial.X : (CFieldSpec.K α)[X]) ≠ 0 :=
          (map_ne_zero_iff (amG α) (RatFunc.algebraMap_injective _)).mpr Polynomial.X_ne_zero
        have hden : ∀ k, toPolyG (cshiftG k ([CField.one] : CPolyG α)) = (Polynomial.X : (CFieldSpec.K α)[X]) ^ k := by
          intro k
          simp only [denote, mul_zero, add_zero, map_one, mul_one]
        have hqsingle : toPolyG ([q] : CPolyG α) = Polynomial.C (CFieldSpec.toK q) := by
          simp only [denote, mul_zero, add_zero]
        have hasingle : toPolyG ([a] : CPolyG α) = Polynomial.C (CFieldSpec.toK a) := by
          simp only [denote, mul_zero, add_zero]
        have hnumL : toPolyG (q :: restCoeffs).reverse
            = toPolyG restCoeffs.reverse
              + Polynomial.X ^ as.length * Polynomial.C (CFieldSpec.toK q) := by
          rw [List.reverse_cons, toPolyG_append_laurent, List.length_reverse, hlen, hqsingle]
        have hnumR : toPolyG (a :: as).reverse
            = toPolyG as.reverse + Polynomial.X ^ as.length * Polynomial.C (CFieldSpec.toK a) := by
          rw [List.reverse_cons, toPolyG_append_laurent, List.length_reverse, hasingle]
        have hmeq : s + (a :: as).length = (s + 1) + as.length := by
          rw [List.length_cons]; ring
        have hfrac : ∀ c : α,
            amG α (Polynomial.X ^ as.length * Polynomial.C (CFieldSpec.toK c))
                / amG α (toPolyG (cshiftG (s + (a :: as).length) ([CField.one] : CPolyG α)))
              = amG α (toPolyG ([c] : CPolyG α))
                / amG α (toPolyG (cshiftG (s + 1) ([CField.one] : CPolyG α))) := by
          intro c
          rw [hden, hden,
            show s + (a :: as).length = as.length + (s + 1) from by rw [List.length_cons]; ring,
            pow_add]
          simp only [denote, mul_zero, add_zero, map_mul, map_pow]
          exact mul_div_mul_left _ _ (pow_ne_zero as.length hXne)
        rw [hnumL, hnumR, map_add, map_add, add_div, add_div, map_add, hfrac, hfrac,
          cIntegrateHyperexpLaurent_neg_term Dt η s a q hDt hq]
        congr 1
        have hih := ih restCoeffs (s + 1) hrest
        rw [← hmeq] at hih
        exact hih

/-- **Laurent soundness (general).** For `Dt = η·t`, if `cIntegrateHyperexpLaurentG η pos neg =
some (num, den)`, then `D_tower(⟦num/den⟧) = ⟦pos⟧ + ⟦neg.reverse⟧/⟦t^(neg.length)⟧` — the antiderivative
identity for the full hyperexponential Laurent integrand (non-negative part `pos`, negative part
`neg` read as `∑ᵢ neg[i]·t^{-(i+1)} = ⟦neg.reverse⟧/tᵐ`). -/
theorem cIntegrateHyperexpLaurentG_sound [CRischField α] [CRischFieldSpec α]
    (Dt : CPolyG α) (η : α) (pos : CPolyG α) (neg : List α) (num den : CPolyG α)
    (hDt : IsHyperexpMonomial Dt η)
    (hsome : cIntegrateHyperexpLaurentG η pos neg = some (num, den)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG num) / amG α (toPolyG den))
      = amG α (toPolyG pos)
        + amG α (toPolyG neg.reverse)
          / amG α (toPolyG (cshiftG neg.length ([CField.one] : CPolyG α))) := by
  have hXne : amG α (Polynomial.X : (CFieldSpec.K α)[X]) ≠ 0 :=
    (map_ne_zero_iff (amG α) (RatFunc.algebraMap_injective _)).mpr Polynomial.X_ne_zero
  have hdenpow : toPolyG (cshiftG neg.length ([CField.one] : CPolyG α))
      = (Polynomial.X : (CFieldSpec.K α)[X]) ^ neg.length := by
    simp only [denote, mul_zero, add_zero, map_one, mul_one]
  rw [cIntegrateHyperexpLaurentG] at hsome
  split at hsome
  · rename_i negCoeffs posCoeffs hnegeq hposeq
    simp only [Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨hnum, hden⟩ := hsome
    subst hnum; subst hden
    have hlen : negCoeffs.length = neg.length := laurentGo_length η _ neg negCoeffs 0 hnegeq
    have hsplit : toPolyG (negCoeffs.reverse ++ posCoeffs)
        = toPolyG negCoeffs.reverse
          + Polynomial.X ^ neg.length * toPolyG posCoeffs := by
      rw [toPolyG_append_laurent, List.length_reverse, hlen]
    rw [hsplit, map_add, add_div, map_add, add_comm (amG α (toPolyG pos))]
    congr 1
    · have hneg := laurentNegGo_sound Dt η hDt neg negCoeffs 0 hnegeq
      simpa using hneg
    · have hpos := laurentPosGo_sound Dt η hDt pos posCoeffs 0 hposeq
      rw [hdenpow, map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero neg.length hXne)]
      simpa using hpos
  all_goals simp at hsome

/-- **Laurent soundness, polynomial case (`neg = []`).** For `Dt = η·t`, if
`cIntegrateHyperexpLaurentG η pos [] = some (num, den)`, then `D_tower(⟦num/den⟧) = ⟦pos⟧` — the antiderivative
identity for a purely non-negative hyperexponential Laurent integrand (`den = 1`). -/
theorem cIntegrateHyperexpLaurentG_pos_sound [CRischField α] [CRischFieldSpec α]
    (Dt : CPolyG α) (η : α) (pos num den : CPolyG α)
    (hDt : IsHyperexpMonomial Dt η)
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
      simp only [denote, mul_zero, add_zero, map_one]
    rw [hden1, map_one, div_one]
    simpa using laurentPosGo_sound Dt η hDt pos posCoeffs 0 hp
  · simp at hsome

/-! ### The special-part connector: `cHyperexpSpecialNegG` reads `b/dₛ` faithfully -/

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **`cHyperexpSpecialNegG` correctness (polynomial identity).** For a special denominator `dₛ = c·tᵐ`
(read via `cleadG`/`cdegG`) with `c ≠ 0` and a proper numerator `b` (degree `< m`),
`C(c) · toPolyG (cHyperexpSpecialNegG b dₛ).reverse = toPolyG b`. -/
theorem cHyperexpSpecialNegG_reverse_smul [CRischField α] (b ds : CPolyG α)
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
theorem cHyperexpSpecialNegG_frac [CRischField α] (b ds : CPolyG α)
    (hds : IsSpecialDenominator b ds) :
    amG α (toPolyG (cHyperexpSpecialNegG b ds).reverse)
        / amG α (toPolyG (cshiftG (cHyperexpSpecialNegG b ds).length ([CField.one] : CPolyG α)))
      = amG α (toPolyG b) / amG α (toPolyG ds) := by
  have hlen : (cHyperexpSpecialNegG b ds).length = cdegG ds := by
    rw [cHyperexpSpecialNegG, if_neg (by simp [hds.nz]), if_neg (Nat.ne_of_gt hds.mpos),
      List.length_map, List.length_range]
  have hpoly := cHyperexpSpecialNegG_reverse_smul b ds hds.toIsProperSpecialPart
  have hdenpow : toPolyG (cshiftG (cHyperexpSpecialNegG b ds).length ([CField.one] : CPolyG α))
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
    (Dt : CPolyG α) (η : α) (fp b ds lnum lden : CPolyG α)
    (hDt : IsHyperexpMonomial Dt η) (hds : IsSpecialDenominator b ds)
    (hsome : cIntegrateHyperexpLaurentG η fp (cHyperexpSpecialNegG b ds) = some (lnum, lden)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG lnum) / amG α (toPolyG lden))
      = amG α (toPolyG fp) + amG α (toPolyG b) / amG α (toPolyG ds) := by
  rw [cIntegrateHyperexpLaurentG_sound Dt η fp (cHyperexpSpecialNegG b ds) lnum lden hDt hsome,
    cHyperexpSpecialNegG_frac b ds hds]

end DeepWiki.SymbolicIntegration
