import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.LaurentCore
import DeepWiki.SymbolicIntegration.Engine.RischFieldSpec

/-! # Laurent integrator soundness

Soundness lemmas for Laurent-term integration in a monomial hyperexponential tower.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly CFrac
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `Dt` is the monomial hyperexponential derivative `η * t`. -/
abbrev IsHyperexpMonomial (Dt : CPoly α) (η : α) : Prop :=
  toPoly Dt = Polynomial.C (CFieldSpec.toK η) * Polynomial.X

/-- **The tower derivative of a polynomial image is the image of `cmonomialDeriv`**:
`D_tower(⟦p⟧) = ⟦cmonomialDeriv Dt p⟧`. Grounds every Laurent-term computation at the polynomial level
(`extendDeriv_algebraMap` + `toPolyG_cmonomialDeriv`). -/
theorem towerFractionFieldDerivG_amG_poly (Dt p : CPoly α) :
    towerFractionFieldDeriv Dt (am α (toPoly p)) = am α (toPoly (cmonomialDeriv Dt p)) := by
  rw [towerFractionFieldDeriv, extendDeriv_algebraMap]
  simp only [denote]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `toK (cLaurentShift η k) = k · toK η` for a non-negative shift `k : ℕ`. -/
theorem toK_cLaurentShiftG_natCast [CRischField α] (η : α) (k : ℕ) :
    CFieldSpec.toK (cLaurentShift η (k : ℤ)) = (k : CFieldSpec.K α) * CFieldSpec.toK η := by
  rw [cLaurentShift, Int.natAbs_natCast, if_neg (Int.not_lt.mpr (Int.natCast_nonneg k)),
    CFieldSpec.toK_mul, CPoly.toK_cnatCastG]

/-- **A non-negative Laurent term is an antiderivative.** For a hyperexponential monomial
`Dt = η·t` and a solved coefficient `cLaurentIntCoeff η k aₖ = some qₖ` (`k : ℕ`),
`D_tower(⟦qₖ·tᵏ⟧) = ⟦aₖ·tᵏ⟧`. Product/power rule + `crischDESolve` soundness collapse `(qₖ)′ + k·η·qₖ` to
`aₖ`. -/
theorem cIntegrateHyperexpLaurent_pos_term [CRischField α] [CRischFieldSpec α]
    (Dt : CPoly α) (η : α) (k : ℕ) (ak qk : α)
    (hDt : IsHyperexpMonomial Dt η)
    (hsolve : cLaurentIntCoeff η (k : ℤ) ak = some qk) :
    towerFractionFieldDeriv Dt (am α (toPoly (cshift k ([qk] : CPoly α))))
      = am α (toPoly (cshift k ([ak] : CPoly α))) := by
  rw [towerFractionFieldDerivG_amG_poly]
  congr 1
  have hspec := CRischFieldSpec.crischDESolve_spec (cLaurentShift η (k : ℤ)) ak qk hsolve
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
/-- `toK (cLaurentShift η (-(i+1))) = -(i+1) · toK η` for a negative shift. -/
theorem toK_cLaurentShiftG_negCast [CRischField α] (η : α) (i : ℕ) :
    CFieldSpec.toK (cLaurentShift η (-(i + 1 : ℤ)))
      = -((i : CFieldSpec.K α) + 1) * CFieldSpec.toK η := by
  have hnat : (-(i + 1 : ℤ)).natAbs = i + 1 := by omega
  rw [cLaurentShift, hnat, if_pos (by omega), CFieldSpec.toK_mul, CFieldSpec.toK_neg,
    CPoly.toK_cnatCastG]
  push_cast; ring

/-- **A negative Laurent term is an antiderivative.** For `Dt = η·t` and a solved
coefficient `cLaurentIntCoeff η (-(i+1)) a = some q`, `D_tower(⟦q·t^{-(i+1)}⟧) = ⟦a·t^{-(i+1)}⟧`. Quotient
rule + `crischDESolve` soundness on the negative shift. -/
theorem cIntegrateHyperexpLaurent_neg_term [CRischField α] [CRischFieldSpec α]
    (Dt : CPoly α) (η : α) (i : ℕ) (a q : α)
    (hDt : IsHyperexpMonomial Dt η)
    (hsolve : cLaurentIntCoeff η (-(i + 1 : ℤ)) a = some q) :
    towerFractionFieldDeriv Dt
        (am α (toPoly ([q] : CPoly α)) / am α (toPoly (cshift (i + 1) ([CField.one] : CPoly α))))
      = am α (toPoly ([a] : CPoly α))
        / am α (toPoly (cshift (i + 1) ([CField.one] : CPoly α))) := by
  have hspec := CRischFieldSpec.crischDESolve_spec (cLaurentShift η (-(i + 1 : ℤ))) a q hsolve
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
  have hAXne : am α (Polynomial.X ^ (i + 1) : (CFieldSpec.K α)[X]) ≠ 0 :=
    (map_ne_zero_iff (am α) (RatFunc.algebraMap_injective _)).mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [show CFieldSpec.toK a = (CFieldSpec.toK q)′ + -((i : CFieldSpec.K α) + 1) * CFieldSpec.toK η
      * CFieldSpec.toK q from hspec.symm]
  simp only [map_add, map_mul, map_natCast, map_pow, map_neg, map_one]
  field_simp
  push_cast
  ring

/-! ### Laurent sum assembly -/

/-- **The non-negative Laurent sum is an antiderivative.** For a list `l` of `(k, aₖ, qₖ)` where each `qₖ`
solves the shift-`k` RDE, `D_tower(∑ₖ ⟦qₖ·tᵏ⟧) = ∑ₖ ⟦aₖ·tᵏ⟧`. The additive assembly of
`cIntegrateHyperexpLaurent_pos_term` over the term list. -/
theorem towerFractionFieldDerivG_laurent_pos_sum [CRischField α] [CRischFieldSpec α]
    (Dt : CPoly α) (η : α) (l : List (ℕ × α × α))
    (hDt : IsHyperexpMonomial Dt η)
    (hall : ∀ t ∈ l, cLaurentIntCoeff η (t.1 : ℤ) t.2.1 = some t.2.2) :
    towerFractionFieldDeriv Dt
        ((l.map (fun t => am α (toPoly (cshift t.1 ([t.2.2] : CPoly α))))).sum)
      = (l.map (fun t => am α (toPoly (cshift t.1 ([t.2.1] : CPoly α))))).sum := by
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  exact cIntegrateHyperexpLaurent_pos_term Dt η t.1 t.2.1 t.2.2 hDt (hall t ht)

/-- **The non-negative Laurent solve loop is sound (offset-generalized).** If the `posQ` foldr over
`pos.zipIdx s` (shifts `s, s+1, …`) returns `coeffs`, then `D_tower(⟦tˢ·coeffs⟧) = ⟦tˢ·pos⟧`. Direct
induction on `pos`, splitting the Horner list off the head and applying the single-term identity plus the
induction hypothesis at offset `s+1`. -/
theorem laurentPosGo_sound [CRischField α] [CRischFieldSpec α] (Dt : CPoly α) (η : α)
    (hDt : IsHyperexpMonomial Dt η) :
    ∀ (pos coeffs : CPoly α) (s : ℕ),
      ((pos.zipIdx s).foldr (fun ck acc =>
          match acc with
          | none => none
          | some tail =>
            match cLaurentIntCoeff η (ck.2 : ℤ) ck.1 with
            | none => none
            | some q => some (q :: tail))
        (some []) = some coeffs) →
      towerFractionFieldDeriv Dt (am α (toPoly (cshift s coeffs)))
        = am α (toPoly (cshift s pos)) := by
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
          match cLaurentIntCoeff η (ck.2 : ℤ) ck.1 with
          | none => none
          | some q => some (q :: tail)) (some []) with
    | none => rw [hrest] at h; simp at h
    | some restCoeffs =>
      rw [hrest] at h
      cases hq : cLaurentIntCoeff η (s : ℤ) a with
      | none => rw [hq] at h; simp at h
      | some q =>
        rw [hq] at h
        rw [Option.some.injEq] at h
        subst h
        have hsplit1 : toPoly (cshift s (q :: restCoeffs))
            = toPoly (cshift s ([q] : CPoly α)) + toPoly (cshift (s + 1) restCoeffs) := by
          simp only [denote, mul_zero, add_zero, pow_succ]; ring
        have hsplit2 : toPoly (cshift s (a :: as))
            = toPoly (cshift s ([a] : CPoly α)) + toPoly (cshift (s + 1) as) := by
          simp only [denote, mul_zero, add_zero, pow_succ]; ring
        rw [hsplit1, map_add, map_add, hsplit2, map_add,
          cIntegrateHyperexpLaurent_pos_term Dt η s a q hDt hq, ih restCoeffs (s + 1) hrest]

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Top-coefficient split through `toPoly`: `toPoly (p ++ q) = toPoly p + Xᵖ·ˡᵉⁿ · toPoly q`. -/
theorem toPolyG_append_laurent (p q : CPoly α) :
    toPoly (p ++ q) = toPoly p + Polynomial.X ^ (p : List α).length * toPoly q := by
  induction p with
  | nil => simp
  | cons a as ih =>
    show toPoly (a :: (as ++ q)) = _
    rw [toPolyG_cons, ih, toPolyG_cons, List.length_cons, pow_succ]; ring

omit [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The solve-loop preserves length: a successful `Laurent` foldr returns as many coefficients as inputs. -/
theorem laurentGo_length [CRischField α] (η : α) (sh : ℕ → ℤ) :
    ∀ (l coeffs : List α) (s : ℕ),
      ((l.zipIdx s).foldr (fun ck acc =>
          match acc with
          | none => none
          | some tail =>
            match cLaurentIntCoeff η (sh ck.2) ck.1 with
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
          match cLaurentIntCoeff η (sh ck.2) ck.1 with
          | none => none
          | some q => some (q :: tail)) (some []) with
    | none => rw [hrest] at h; simp at h
    | some restCoeffs =>
      rw [hrest] at h
      cases hq : cLaurentIntCoeff η (sh s) a with
      | none => rw [hq] at h; simp at h
      | some q =>
        rw [hq, Option.some.injEq] at h
        subst h
        simp only [List.length_cons, ih restCoeffs (s + 1) hrest]

/-- **The negative Laurent solve loop is sound (offset-generalized).** If the `negQ` foldr over
`neg.zipIdx s` (shifts `-(s+1), -(s+2), …`) returns `negCoeffs`, then over the fixed denominator
`t^(s+neg.length)`, `D_tower(⟦negCoeffs.reverse⟧/⟦t^(s+len)⟧) = ⟦neg.reverse⟧/⟦t^(s+len)⟧`. The head splits
off the reversed list as `⟦q⟧/t^(s+1)` plus the tail at offset `s+1` (same denominator, IH). -/
theorem laurentNegGo_sound [CRischField α] [CRischFieldSpec α] (Dt : CPoly α) (η : α)
    (hDt : IsHyperexpMonomial Dt η) :
    ∀ (neg negCoeffs : List α) (s : ℕ),
      ((neg.zipIdx s).foldr (fun ck acc =>
          match acc with
          | none => none
          | some tail =>
            match cLaurentIntCoeff η (-(ck.2 + 1 : ℤ)) ck.1 with
            | none => none
            | some q => some (q :: tail)) (some []) = some negCoeffs) →
      towerFractionFieldDeriv Dt
          (am α (toPoly negCoeffs.reverse)
            / am α (toPoly (cshift (s + neg.length) ([CField.one] : CPoly α))))
        = am α (toPoly neg.reverse)
          / am α (toPoly (cshift (s + neg.length) ([CField.one] : CPoly α))) := by
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
          match cLaurentIntCoeff η (-(ck.2 + 1 : ℤ)) ck.1 with
          | none => none
          | some q => some (q :: tail)) (some []) with
    | none => rw [hrest] at h; simp at h
    | some restCoeffs =>
      rw [hrest] at h
      cases hq : cLaurentIntCoeff η (-(s + 1 : ℤ)) a with
      | none => rw [hq] at h; simp at h
      | some q =>
        rw [hq, Option.some.injEq] at h
        subst h
        have hlen : restCoeffs.length = as.length := laurentGo_length η _ as restCoeffs (s + 1) hrest
        have hXne : am α (Polynomial.X : (CFieldSpec.K α)[X]) ≠ 0 :=
          (map_ne_zero_iff (am α) (RatFunc.algebraMap_injective _)).mpr Polynomial.X_ne_zero
        have hden : ∀ k, toPoly (cshift k ([CField.one] : CPoly α)) = (Polynomial.X : (CFieldSpec.K α)[X]) ^ k := by
          intro k
          simp only [denote, mul_zero, add_zero, map_one, mul_one]
        have hqsingle : toPoly ([q] : CPoly α) = Polynomial.C (CFieldSpec.toK q) := by
          simp only [denote, mul_zero, add_zero]
        have hasingle : toPoly ([a] : CPoly α) = Polynomial.C (CFieldSpec.toK a) := by
          simp only [denote, mul_zero, add_zero]
        have hnumL : toPoly (q :: restCoeffs).reverse
            = toPoly restCoeffs.reverse
              + Polynomial.X ^ as.length * Polynomial.C (CFieldSpec.toK q) := by
          rw [List.reverse_cons, toPolyG_append_laurent, List.length_reverse, hlen, hqsingle]
        have hnumR : toPoly (a :: as).reverse
            = toPoly as.reverse + Polynomial.X ^ as.length * Polynomial.C (CFieldSpec.toK a) := by
          rw [List.reverse_cons, toPolyG_append_laurent, List.length_reverse, hasingle]
        have hmeq : s + (a :: as).length = (s + 1) + as.length := by
          rw [List.length_cons]; ring
        have hfrac : ∀ c : α,
            am α (Polynomial.X ^ as.length * Polynomial.C (CFieldSpec.toK c))
                / am α (toPoly (cshift (s + (a :: as).length) ([CField.one] : CPoly α)))
              = am α (toPoly ([c] : CPoly α))
                / am α (toPoly (cshift (s + 1) ([CField.one] : CPoly α))) := by
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

/-- **Laurent soundness (general).** For `Dt = η·t`, if `cIntegrateHyperexpLaurent η pos neg =
some (num, den)`, then `D_tower(⟦num/den⟧) = ⟦pos⟧ + ⟦neg.reverse⟧/⟦t^(neg.length)⟧` — the antiderivative
identity for the full hyperexponential Laurent integrand (non-negative part `pos`, negative part
`neg` read as `∑ᵢ neg[i]·t^{-(i+1)} = ⟦neg.reverse⟧/tᵐ`). -/
theorem cIntegrateHyperexpLaurentG_sound [CRischField α] [CRischFieldSpec α]
    (Dt : CPoly α) (η : α) (pos : CPoly α) (neg : List α) (num den : CPoly α)
    (hDt : IsHyperexpMonomial Dt η)
    (hsome : cIntegrateHyperexpLaurent η pos neg = some (num, den)) :
    towerFractionFieldDeriv Dt (am α (toPoly num) / am α (toPoly den))
      = am α (toPoly pos)
        + am α (toPoly neg.reverse)
          / am α (toPoly (cshift neg.length ([CField.one] : CPoly α))) := by
  have hXne : am α (Polynomial.X : (CFieldSpec.K α)[X]) ≠ 0 :=
    (map_ne_zero_iff (am α) (RatFunc.algebraMap_injective _)).mpr Polynomial.X_ne_zero
  have hdenpow : toPoly (cshift neg.length ([CField.one] : CPoly α))
      = (Polynomial.X : (CFieldSpec.K α)[X]) ^ neg.length := by
    simp only [denote, mul_zero, add_zero, map_one, mul_one]
  rw [cIntegrateHyperexpLaurent] at hsome
  split at hsome
  · rename_i negCoeffs posCoeffs hnegeq hposeq
    simp only [Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨hnum, hden⟩ := hsome
    subst hnum; subst hden
    have hlen : negCoeffs.length = neg.length := laurentGo_length η _ neg negCoeffs 0 hnegeq
    have hsplit : toPoly (negCoeffs.reverse ++ posCoeffs)
        = toPoly negCoeffs.reverse
          + Polynomial.X ^ neg.length * toPoly posCoeffs := by
      rw [toPolyG_append_laurent, List.length_reverse, hlen]
    rw [hsplit, map_add, add_div, map_add, add_comm (am α (toPoly pos))]
    congr 1
    · have hneg := laurentNegGo_sound Dt η hDt neg negCoeffs 0 hnegeq
      simpa using hneg
    · have hpos := laurentPosGo_sound Dt η hDt pos posCoeffs 0 hposeq
      rw [hdenpow, map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero neg.length hXne)]
      simpa using hpos
  all_goals simp at hsome

/-- **Laurent soundness, polynomial case (`neg = []`).** For `Dt = η·t`, if
`cIntegrateHyperexpLaurent η pos [] = some (num, den)`, then `D_tower(⟦num/den⟧) = ⟦pos⟧` — the antiderivative
identity for a purely non-negative hyperexponential Laurent integrand (`den = 1`). -/
theorem cIntegrateHyperexpLaurentG_pos_sound [CRischField α] [CRischFieldSpec α]
    (Dt : CPoly α) (η : α) (pos num den : CPoly α)
    (hDt : IsHyperexpMonomial Dt η)
    (hsome : cIntegrateHyperexpLaurent η pos [] = some (num, den)) :
    towerFractionFieldDeriv Dt (am α (toPoly num) / am α (toPoly den))
      = am α (toPoly pos) := by
  rw [cIntegrateHyperexpLaurent] at hsome
  simp only [List.length_nil, List.zipIdx_nil, List.foldr_nil] at hsome
  split at hsome
  · rename_i negC posCoeffs hnegeq hp
    simp only [Option.some.injEq] at hnegeq
    subst hnegeq
    simp only [List.reverse_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨hnum, hden⟩ := hsome
    subst hnum; subst hden
    have hden1 : toPoly (cshift (0 : ℕ) ([CField.one] : CPoly α)) = 1 := by
      show toPoly ([CField.one] : CPoly α) = 1
      simp only [denote, mul_zero, add_zero, map_one]
    rw [hden1, map_one, div_one]
    simpa using laurentPosGo_sound Dt η hDt pos posCoeffs 0 hp
  · simp at hsome

end DeepWiki.SymbolicIntegration
