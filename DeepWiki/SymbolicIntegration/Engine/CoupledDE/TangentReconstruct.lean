import DeepWiki.SymbolicIntegration.Engine.CoupledDE.Assembly
import DeepWiki.SymbolicIntegration.Engine.CoupledDE.Bivariate
import Mathlib.RingTheory.AdjoinRoot

/-! # Tangent telescoping reconstruction for the hypertangent coupled system

`cCoupledDECancelTan` solves the hypertangent coupled `t`-polynomial system degree-by-degree,
each level a base `cCoupledDESystem` solve reduced by synthetic division by `t − √−1`. This file
verifies the telescoping in the Gaussian extension `S = AdjoinRoot (X²+1)` over `ℚ[x]`
(`iU = √−1`), proving the assembled `(q₁, q₂)` solve the coupled system over `ℚ[x][t]` and so
discharge `cancelTanClearedCheck`. -/

namespace DeepWiki.SymbolicIntegration.DensePoly
open Polynomial DensePoly

abbrev SGauss := AdjoinRoot (X ^ 2 + 1 : (Polynomial ℚ)[X])
noncomputable def iU : SGauss := AdjoinRoot.root _

theorem iU_sq : (iU : SGauss)^2 = -1 := by
  unfold iU
  have h : (X ^ 2 + 1 : (Polynomial ℚ)[X]).eval₂ (AdjoinRoot.of _) (AdjoinRoot.root _) = 0 :=
    AdjoinRoot.eval₂_root _
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  linear_combination h

noncomputable def toS (p : DensePoly ℚ) : SGauss := AdjoinRoot.of _ (toPoly p)
noncomputable def pairToS (x : DensePoly ℚ × DensePoly ℚ) : SGauss := toS x.1 + toS x.2 * iU
noncomputable def toGBCoeffPolyS (p : List (DensePoly ℚ)) : SGauss[X] := (DensePoly.toPoly p).map (AdjoinRoot.of _)
noncomputable def pairListToS : List (DensePoly ℚ × DensePoly ℚ) → SGauss[X]
  | [] => 0
  | a :: as => C (pairToS a) + X * pairListToS as

theorem toS_add (p q : DensePoly ℚ) : toS (cadd p q) = toS p + toS q := by
  simp only [toS, denote, map_add]
theorem toS_sub (p q : DensePoly ℚ) : toS (csub p q) = toS p - toS q := by
  simp only [toS, denote, map_sub]
theorem toS_scale (c : ℚ) (p : DensePoly ℚ) : toS (cscale c p) = AdjoinRoot.of _ (C c) * toS p := by
  simp only [toS, denote, map_mul]
  rfl
theorem toS_nil : toS ([] : DensePoly ℚ) = 0 := by unfold toS; rw [toPolyG_nil, map_zero]
theorem toS_scale_neg_one (p : DensePoly ℚ) : toS (cscale (-1) p) = - toS p := by
  rw [toS_scale]; simp [map_neg, map_one]

theorem toGBCoeffPolyS_nil : toGBCoeffPolyS [] = 0 := by simp [toGBCoeffPolyS]
theorem toGBCoeffPolyS_cons (a : DensePoly ℚ) (as : List (DensePoly ℚ)) :
    toGBCoeffPolyS (a :: as) = C (toS a) + X * toGBCoeffPolyS as := by
  unfold toGBCoeffPolyS toS
  rw [DensePoly.toPolyG_cons_dense, Polynomial.map_add, Polynomial.map_mul, map_C, Polynomial.map_X]

theorem evalAtI_spec (p : List (DensePoly ℚ)) :
    (toGBCoeffPolyS p).eval iU = pairToS (evalAtI p) := by
  induction p with
  | nil => simp [toGBCoeffPolyS_nil, evalAtI, pairToS, CPolyEngine.czero_dense_eq, toS_nil]
  | cons a as ih =>
    rw [toGBCoeffPolyS_cons, eval_add, eval_C, eval_mul, eval_X, ih]
    rw [show evalAtI (a :: as)
        = (cadd a (cscale (-1) (evalAtI as).2), (evalAtI as).1) from by
      rw [evalAtI, List.foldr_cons]; rfl]
    rw [pairToS, pairToS]
    simp only [toS_add, toS_scale_neg_one]
    have hsq : iU * (toS (evalAtI as).2 * iU) = - toS (evalAtI as).2 := by
      rw [show iU * (toS (evalAtI as).2 * iU) = toS (evalAtI as).2 * iU^2 from by ring, iU_sq]; ring
    rw [mul_add, hsq]; ring

theorem pairListToS_append_singleton (Q : List (DensePoly ℚ × DensePoly ℚ)) (c : DensePoly ℚ × DensePoly ℚ) :
    pairListToS (Q ++ [c]) = pairListToS Q + C (pairToS c) * X ^ Q.length := by
  induction Q with
  | nil => simp [pairListToS]
  | cons a as ih =>
    simp only [List.cons_append, pairListToS, ih, List.length_cons]; ring

theorem go_append (L : List (DensePoly ℚ × DensePoly ℚ)) (carry : DensePoly ℚ × DensePoly ℚ)
    (acc : List (DensePoly ℚ × DensePoly ℚ)) :
    divByTminusI.go ([], [CCommRing.one]) L carry acc
      = divByTminusI.go ([], [CCommRing.one]) L carry [] ++ acc := by
  induction L generalizing carry acc with
  | nil => simp [divByTminusI.go]
  | cons a L ih =>
    rw [divByTminusI.go]
    conv_rhs => rw [divByTminusI.go]
    rw [ih (divByTminusI.cadd' a (cmulI ([], [CCommRing.one]) carry)) (carry :: acc)]
    conv_rhs => rw [ih (divByTminusI.cadd' a (cmulI ([], [CCommRing.one]) carry)) [carry]]
    simp

theorem pairToS_caddG' (x y : DensePoly ℚ × DensePoly ℚ) :
  pairToS (divByTminusI.cadd' x y) = pairToS x + pairToS y := by
  unfold divByTminusI.cadd' pairToS
  simp only [CPolyEngine.add_dense_eq, toS_add]
  ring
theorem pairToS_cmulI (x y : DensePoly ℚ × DensePoly ℚ) :
  pairToS (cmulI x y) = pairToS x * pairToS y := by
  unfold cmulI pairToS
  simp only [CPolyEngine.sub_dense_eq, CPolyEngine.mul_dense_eq,
    CPolyEngine.add_dense_eq, toS_sub, toS_add]
  have hmul : ∀ a b : DensePoly ℚ, toS (cmul a b) = toS a * toS b := by
    intro a b
    simp only [toS, denote, map_mul]
  rw [hmul, hmul, hmul, hmul]
  linear_combination (- (toS x.2 * toS y.2)) * iU_sq
theorem pairToS_I : pairToS (([], [CCommRing.one]) : DensePoly ℚ × DensePoly ℚ) = iU := by
  unfold pairToS
  simp only [toS_nil, zero_add]
  rw [show toS ([CCommRing.one] : DensePoly ℚ) = 1 from by
    unfold toS
    rw [show ([CCommRing.one] : DensePoly ℚ) = (CCommRing.one : ℚ) :: ([] : DensePoly ℚ) from rfl,
      toPolyG_cons, toPolyG_nil]
    rw [show CRingSpec.toR (CCommRing.one : ℚ) = 1 from rfl]
    simp]
  ring

theorem quotOf_cons (a : DensePoly ℚ × DensePoly ℚ) (L : List (DensePoly ℚ × DensePoly ℚ))
    (carry : DensePoly ℚ × DensePoly ℚ) :
    divByTminusI.go ([], [CCommRing.one]) (a :: L) carry []
      = divByTminusI.go ([], [CCommRing.one]) L
          (divByTminusI.cadd' a (cmulI ([], [CCommRing.one]) carry)) [] ++ [carry] := by
  rw [divByTminusI.go, go_append]
theorem quotOf_length (L : List (DensePoly ℚ × DensePoly ℚ)) (carry : DensePoly ℚ × DensePoly ℚ) :
    (divByTminusI.go ([], [CCommRing.one]) L carry []).length = L.length := by
  induction L generalizing carry with
  | nil => simp [divByTminusI.go]
  | cons a L ih => rw [quotOf_cons]; simp [ih]

-- Master existential division invariant.
theorem go_div_master (L : List (DensePoly ℚ × DensePoly ℚ)) (carry : DensePoly ℚ × DensePoly ℚ) :
    ∃ r : SGauss, pairListToS L.reverse + C (pairToS carry) * X ^ L.length
      = (X - C iU) * pairListToS (divByTminusI.go ([], [CCommRing.one]) L carry []) + C r := by
  induction L generalizing carry with
  | nil =>
    refine ⟨pairToS carry, ?_⟩
    simp [pairListToS, divByTminusI.go]
  | cons a L ih =>
    obtain ⟨r, hr⟩ := ih (divByTminusI.cadd' a (cmulI ([], [CCommRing.one]) carry))
    refine ⟨r, ?_⟩
    rw [quotOf_cons, pairListToS_append_singleton, quotOf_length]
    rw [List.reverse_cons, pairListToS_append_singleton]
    rw [List.length_reverse, List.length_cons]
    -- expand the carry's pairToS via the recurrence
    rw [pairToS_caddG', pairToS_cmulI, pairToS_I] at hr
    -- substitute hr (solve for pairListToS L.reverse) — use linear_combination
    have hexp : pairListToS L.reverse
        = (X - C iU) * pairListToS (divByTminusI.go ([], [CCommRing.one]) L
            (divByTminusI.cadd' a (cmulI ([], [CCommRing.one]) carry)) []) + C r
          - C (pairToS a + iU * pairToS carry) * X ^ L.length := by
      linear_combination hr
    rw [hexp]
    rw [map_add, map_mul]
    ring

theorem divByTminusI_spec (p : List (DensePoly ℚ × DensePoly ℚ)) :
    pairListToS p
      = (X - C iU) * pairListToS (divByTminusI p) + C ((pairListToS p).eval iU) := by
  obtain ⟨r, hr⟩ := go_div_master p.reverse ([], [])
  rw [List.reverse_reverse, List.length_reverse] at hr
  have hpair0 : pairToS (([], []) : DensePoly ℚ × DensePoly ℚ) = 0 := by
    unfold pairToS; simp [toS_nil]
  rw [hpair0, map_zero, zero_mul, add_zero] at hr
  -- divByTminusI p = go I p.reverse ([],[]) []
  have hdef : divByTminusI p = divByTminusI.go ([], [CCommRing.one]) p.reverse ([], []) [] := by
    rw [divByTminusI]; simp
  rw [hdef]
  -- evaluate hr at iU to pin r
  have heval : (pairListToS p).eval iU = r := by
    rw [hr]
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C]
    ring
  rw [heval]; exact hr

/-! ### `toGBCoeffPolyS` as a ring hom: operations lifted to `S[t]` -/

theorem toGBCoeffPolyS_eq_map (p : List (DensePoly ℚ)) :
    toGBCoeffPolyS p = (DensePoly.toPoly p).map (AdjoinRoot.of (X ^ 2 + 1 : (Polynomial ℚ)[X])) := rfl

theorem toGBCoeffPolyS_cadd (p q : List (DensePoly ℚ)) :
    toGBCoeffPolyS (DensePoly.cadd p q) = toGBCoeffPolyS p + toGBCoeffPolyS q := by
  rw [toGBCoeffPolyS_eq_map, DensePoly.toPolyG_caddG, Polynomial.map_add]; rfl
theorem toGBCoeffPolyS_csub (p q : List (DensePoly ℚ)) :
    toGBCoeffPolyS (DensePoly.csub p q) = toGBCoeffPolyS p - toGBCoeffPolyS q := by
  rw [toGBCoeffPolyS_eq_map, DensePoly.toPolyG_csubG, Polynomial.map_sub]; rfl
/-- `DensePoly.toPoly` of `cscaleListQ` (scale every ℚ[x]-coeff by `s : ℚ`) is mult by `C (C s)`. -/
theorem toPolyG_cscaleListQ (s : ℚ) (p : List (DensePoly ℚ)) :
    DensePoly.toPoly (cscaleListQ s p) = C (C s) * DensePoly.toPoly p := by
  apply Polynomial.ext; intro k
  rw [cscaleListQ, DensePoly.toPolyG_coeff_dense]
  by_cases hk : k < p.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [show p[k]? = some p[k] from List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    simp only [CPolyEngine.scale_dense_eq, denote]
    rw [Polynomial.coeff_C_mul, DensePoly.toPolyG_coeff_dense,
      List.getD_eq_getElem?_getD, show p[k]? = some p[k] from List.getElem?_eq_getElem hk]
    simp only [Option.getD_some, CFieldSpec.toK, id_eq]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      show p[k]? = none from List.getElem?_eq_none (by omega)]
    simp only [Option.map_none, Option.getD_none, toPolyG_nil]
    rw [Polynomial.coeff_C_mul, DensePoly.toPolyG_coeff_dense,
      List.getD_eq_getElem?_getD, show p[k]? = none from List.getElem?_eq_none (by omega)]
    simp
theorem toGBCoeffPolyS_cscaleListQ (s : ℚ) (p : List (DensePoly ℚ)) :
    toGBCoeffPolyS (cscaleListQ s p) = C (AdjoinRoot.of _ (C s)) * toGBCoeffPolyS p := by
  rw [toGBCoeffPolyS_eq_map, toPolyG_cscaleListQ, Polynomial.map_mul, map_C, toGBCoeffPolyS_eq_map]

/-! ### tanDeriv lifted to S[t]; the complex/real bridges -/

theorem toGBCoeffPolyS_tanDeriv (p : List (DensePoly ℚ)) :
    toGBCoeffPolyS (tanDeriv p)
      = toGBCoeffPolyS (p.map cderiv) + (X ^ 2 + 1) * Polynomial.derivative (toGBCoeffPolyS p) := by
  rw [toGBCoeffPolyS_eq_map, toPolyG_tanDeriv, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    ← derivative_map]
  rfl

/-- `pairListToS` coefficient reader. -/
theorem pairListToS_coeff (L : List (DensePoly ℚ × DensePoly ℚ)) (k : ℕ) :
    (pairListToS L).coeff k = pairToS (L.getD k ([], [])) := by
  induction L generalizing k with
  | nil => simp [pairListToS, pairToS, toS_nil]
  | cons a as ih =>
    rw [pairListToS, Polynomial.coeff_add]
    cases k with
    | zero => simp [Polynomial.coeff_C]
    | succ m => rw [List.getD_cons_succ, Polynomial.coeff_X_mul, ih m]; simp

/-- `toGBCoeffPolyS` coefficient reader. -/
theorem toGBCoeffPolyS_coeff (p : List (DensePoly ℚ)) (k : ℕ) :
    (toGBCoeffPolyS p).coeff k = toS (p.getD k []) := by
  rw [toGBCoeffPolyS_eq_map, Polynomial.coeff_map, DensePoly.toPolyG_coeff_dense]; rfl

/-- The zipped real/imag pair-list reads as the complexification. -/
theorem pairListToS_zip (a b : List (DensePoly ℚ)) (N : ℕ) (ha : a.length ≤ N) (hb : b.length ≤ N) :
    pairListToS ((List.range N).map (fun k => (a.getD k [], b.getD k [])))
      = toGBCoeffPolyS a + C iU * toGBCoeffPolyS b := by
  apply Polynomial.ext; intro k
  rw [pairListToS_coeff, Polynomial.coeff_add, Polynomial.coeff_C_mul, toGBCoeffPolyS_coeff,
    toGBCoeffPolyS_coeff]
  by_cases hk : k < N
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    simp only [Option.map_some, Option.getD_some, pairToS]
    ring
  · rw [List.getD_eq_getElem?_getD,
      show ((List.range N).map (fun k => (a.getD k [], b.getD k [])))[k]? = none from
        List.getElem?_eq_none (by rw [List.length_map, List.length_range]; omega)]
    rw [getD_out a k (by omega), getD_out b k (by omega)]
    simp only [Option.getD_none, pairToS, toS_nil, mul_zero, zero_mul, add_zero]

/-- A quotient pair-list splits as the complexification of its real/imag parts. -/
theorem cplx_quot (quot : List (DensePoly ℚ × DensePoly ℚ)) :
    toGBCoeffPolyS (quot.map Prod.fst) + C iU * toGBCoeffPolyS (quot.map Prod.snd) = pairListToS quot := by
  apply Polynomial.ext; intro k
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, toGBCoeffPolyS_coeff, toGBCoeffPolyS_coeff,
    pairListToS_coeff]
  by_cases hk : k < quot.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      show quot[k]? = some quot[k] from List.getElem?_eq_getElem hk]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      show quot[k]? = some quot[k] from List.getElem?_eq_getElem hk]
    rw [List.getD_eq_getElem?_getD, show quot[k]? = some quot[k] from List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some, pairToS]
    ring
  · have hk' : quot.length ≤ k := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      show quot[k]? = none from List.getElem?_eq_none hk']
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      show quot[k]? = none from List.getElem?_eq_none hk']
    rw [List.getD_eq_getElem?_getD, show quot[k]? = none from List.getElem?_eq_none hk']
    simp only [Option.map_none, Option.getD_none, toS_nil, mul_zero, zero_mul, add_zero, pairToS]

/-! ### The complexification `cplx` and the tangent derivation on S[t] -/

/-- Complexify a real pair `(q₁,q₂)` of `t`-polys into `S[t]`: `Q₁ + i·Q₂`. -/
noncomputable def cplx (q1 q2 : List (DensePoly ℚ)) : SGauss[X] :=
  toGBCoeffPolyS q1 + C iU * toGBCoeffPolyS q2

theorem cplx_cadd (p q r s : List (DensePoly ℚ)) :
    cplx (DensePoly.cadd p r) (DensePoly.cadd q s) = cplx p q + cplx r s := by
  unfold cplx; rw [toGBCoeffPolyS_cadd, toGBCoeffPolyS_cadd]; ring
theorem cplx_csub (p q r s : List (DensePoly ℚ)) :
    cplx (DensePoly.csub p r) (DensePoly.csub q s) = cplx p q - cplx r s := by
  unfold cplx; rw [toGBCoeffPolyS_csub, toGBCoeffPolyS_csub]; ring

/-- The tangent derivation on the complexification. -/
noncomputable def Dtan (q1 q2 : List (DensePoly ℚ)) : SGauss[X] :=
  cplx (q1.map cderiv) (q2.map cderiv) + (X ^ 2 + 1) * derivative (cplx q1 q2)

theorem Dtan_eq (q1 q2 : List (DensePoly ℚ)) :
    Dtan q1 q2 = toGBCoeffPolyS (tanDeriv q1) + C iU * toGBCoeffPolyS (tanDeriv q2) := by
  unfold Dtan cplx
  rw [toGBCoeffPolyS_tanDeriv, toGBCoeffPolyS_tanDeriv, derivative_add, derivative_C_mul]
  ring


/-! ### Real/imaginary extraction from an S[t] identity -/

/-- In `S`, `of a + i·of b = 0` (a,b ∈ ℚ[x]) forces `a = 0` and `b = 0`. -/
theorem of_add_iU_eq_zero (a b : Polynomial ℚ)
    (h : AdjoinRoot.of (X ^ 2 + 1 : (Polynomial ℚ)[X]) a
        + AdjoinRoot.of _ b * iU = 0) : a = 0 ∧ b = 0 := by
  -- of a + (of b)·root = mk (C a + C b * X); = 0 ↔ (X²+1) ∣ (C a + C b X) ↔ C a + C b X = 0.
  have hmk : AdjoinRoot.of (X ^ 2 + 1 : (Polynomial ℚ)[X]) a + AdjoinRoot.of _ b * iU
      = AdjoinRoot.mk _ (C a + C b * X) := by
    rw [map_add, map_mul]
    unfold AdjoinRoot.of iU
    rw [AdjoinRoot.mk_X]
    rfl
  rw [hmk, AdjoinRoot.mk_eq_zero] at h
  -- degree (C a + C b X) ≤ 1 < 2, so dvd ⟹ = 0.
  have hdeg : (C a + C b * X : (Polynomial ℚ)[X]).degree < (X ^ 2 + 1 : (Polynomial ℚ)[X]).degree := by
    have h1 : (C a + C b * X : (Polynomial ℚ)[X]).degree ≤ 1 := by
      apply le_trans (Polynomial.degree_add_le _ _)
      exact max_le (le_trans Polynomial.degree_C_le (by norm_num)) (Polynomial.degree_C_mul_X_le b)
    have h2 : (X ^ 2 + 1 : (Polynomial ℚ)[X]).degree = 2 := by
      compute_degree!
    rw [h2]; exact lt_of_le_of_lt h1 (by norm_num)
  have hzero : (C a + C b * X : (Polynomial ℚ)[X]) = 0 := by
    by_contra hne
    have := Polynomial.degree_le_of_dvd h (by exact hne)
    exact absurd (lt_of_le_of_lt this hdeg) (lt_irrefl _)
  -- C a + C b X = 0 ⟹ a = 0 ∧ b = 0 (coeff 0 and 1)
  constructor
  · have := congrArg (fun p => Polynomial.coeff p 0) hzero
    simpa using this
  · have := congrArg (fun p => Polynomial.coeff p 1) hzero
    simpa using this

/-- `map of` is injective on `ℚ[x][t]` (degree of `X²+1` ≠ 0). -/
theorem map_of_injective : Function.Injective
    (Polynomial.map (AdjoinRoot.of (X ^ 2 + 1 : (Polynomial ℚ)[X]))) := by
  apply Polynomial.map_injective
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  rw [show (X ^ 2 + 1 : (Polynomial ℚ)[X]).degree = 2 from by compute_degree!]
  decide

/-- An `S[t]`-equality of complexifications gives both real `ℚ[x][t]` parts. -/
theorem cplx_eq_imp (p q r s : List (DensePoly ℚ)) (h : cplx p q = cplx r s) :
    DensePoly.toPoly p = DensePoly.toPoly r ∧ DensePoly.toPoly q = DensePoly.toPoly s := by
  -- map_of (DensePoly.toPoly p − DensePoly.toPoly r) + C iU * map_of (DensePoly.toPoly q − DensePoly.toPoly s) = 0
  have hz : Polynomial.map (AdjoinRoot.of _) (DensePoly.toPoly p - DensePoly.toPoly r)
      + C iU * Polynomial.map (AdjoinRoot.of _) (DensePoly.toPoly q - DensePoly.toPoly s) = 0 := by
    unfold cplx toGBCoeffPolyS at h
    rw [Polynomial.map_sub, Polynomial.map_sub]
    linear_combination h
  -- coefficient-wise apply of_add_iU_eq_zero, then map_of injective
  have hcoeff : ∀ k, (DensePoly.toPoly p - DensePoly.toPoly r).coeff k = 0 ∧ (DensePoly.toPoly q - DensePoly.toPoly s).coeff k = 0 := by
    intro k
    have := congrArg (fun P => Polynomial.coeff P k) hz
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_zero] at this
    exact of_add_iU_eq_zero _ _ (by rw [mul_comm] at this ⊢; linear_combination this)
  constructor
  · have : DensePoly.toPoly p - DensePoly.toPoly r = 0 := by
      apply Polynomial.ext; intro k; rw [Polynomial.coeff_zero]; exact (hcoeff k).1
    exact sub_eq_zero.mp this
  · have : DensePoly.toPoly q - DensePoly.toPoly s = 0 := by
      apply Polynomial.ext; intro k; rw [Polynomial.coeff_zero]; exact (hcoeff k).2
    exact sub_eq_zero.mp this

/-! ### Coefficient-`∂x` part: `DensePoly.toPoly (·.map cderiv)` -/

/-- The κ (coefficient-`d/dx`) part reads coefficientwise as `derivative` on `ℚ[x]`. -/
theorem mapDeriv_coeff (p : List (DensePoly ℚ)) (k : ℕ) :
    (DensePoly.toPoly (p.map cderiv)).coeff k = derivative ((DensePoly.toPoly p).coeff k) := by
  rw [DensePoly.toPolyG_coeff_dense, DensePoly.toPolyG_coeff_dense]
  by_cases hk : k < p.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      show p[k]? = some p[k] from List.getElem?_eq_getElem hk]
    rw [List.getD_eq_getElem?_getD, show p[k]? = some p[k] from List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    simp only [denote]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      show p[k]? = none from List.getElem?_eq_none (by omega)]
    rw [List.getD_eq_getElem?_getD, show p[k]? = none from List.getElem?_eq_none (by omega)]
    simp only [Option.map_none, Option.getD_none, toPolyG_nil, derivative_zero]

/-- κ-part additive over `DensePoly.cadd`. -/
theorem mapDeriv_cadd (a b : List (DensePoly ℚ)) :
    DensePoly.toPoly ((DensePoly.cadd a b).map cderiv)
      = DensePoly.toPoly (a.map cderiv) + DensePoly.toPoly (b.map cderiv) := by
  apply Polynomial.ext; intro k
  rw [mapDeriv_coeff, DensePoly.toPolyG_caddG, Polynomial.coeff_add, derivative_add,
    Polynomial.coeff_add, mapDeriv_coeff, mapDeriv_coeff]
/-- κ-part subtractive over `DensePoly.csub`. -/
theorem mapDeriv_csub (a b : List (DensePoly ℚ)) :
    DensePoly.toPoly ((DensePoly.csub a b).map cderiv)
      = DensePoly.toPoly (a.map cderiv) - DensePoly.toPoly (b.map cderiv) := by
  apply Polynomial.ext; intro k
  rw [mapDeriv_coeff, DensePoly.toPolyG_csubG, Polynomial.coeff_sub, derivative_sub,
    Polynomial.coeff_sub, mapDeriv_coeff, mapDeriv_coeff]

/-- `tanDeriv` additive over `DensePoly.cadd` (at the `DensePoly.toPoly` level). -/
theorem toPolyG_tanDeriv_cadd (a b : List (DensePoly ℚ)) :
    DensePoly.toPoly (tanDeriv (DensePoly.cadd a b)) = DensePoly.toPoly (tanDeriv a) + DensePoly.toPoly (tanDeriv b) := by
  rw [toPolyG_tanDeriv, toPolyG_tanDeriv, toPolyG_tanDeriv, mapDeriv_cadd, DensePoly.toPolyG_caddG,
    derivative_add]
  ring
/-- `tanDeriv` subtractive over `DensePoly.csub`. -/
theorem toPolyG_tanDeriv_csub (a b : List (DensePoly ℚ)) :
    DensePoly.toPoly (tanDeriv (DensePoly.csub a b)) = DensePoly.toPoly (tanDeriv a) - DensePoly.toPoly (tanDeriv b) := by
  rw [toPolyG_tanDeriv, toPolyG_tanDeriv, toPolyG_tanDeriv, mapDeriv_csub, DensePoly.toPolyG_csubG,
    derivative_sub]
  ring

/-- κ of a shift: `DensePoly.toPoly (([]::h).map cderiv) = X * DensePoly.toPoly (h.map cderiv)`. -/
theorem mapDeriv_shift (h : List (DensePoly ℚ)) :
    DensePoly.toPoly (([] :: h).map cderiv) = X * DensePoly.toPoly (h.map cderiv) := by
  rw [List.map_cons, DensePoly.toPolyG_cons_dense]
  rw [show toPoly (cderiv ([] : DensePoly ℚ)) = 0 from by
    simp only [denote, toPolyG_nil, derivative_zero]]
  rw [map_zero, zero_add]

theorem toPolyG_tanDeriv_shift (h : List (DensePoly ℚ)) :
    DensePoly.toPoly (tanDeriv ([] :: h)) = X * DensePoly.toPoly (tanDeriv h) + (X ^ 2 + 1) * DensePoly.toPoly h := by
  rw [toPolyG_tanDeriv, mapDeriv_shift, DensePoly.toPolyG_cons_dense, toPolyG_nil,
    map_zero, zero_add, derivative_mul, derivative_X, one_mul, toPolyG_tanDeriv]
  ring

theorem toPolyG_tanDeriv_singleton (s : DensePoly ℚ) :
    DensePoly.toPoly (tanDeriv [s]) = C (toPoly (cderiv s)) := by
  rw [toPolyG_tanDeriv, show ([s] : List (DensePoly ℚ)) = s :: [] from rfl,
    DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_nil, mul_zero, add_zero, derivative_C,
    List.map_cons, List.map_nil, DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_nil, mul_zero,
    add_zero]
  ring

/-! ### The numerator vanishes at `t = i` -/

theorem eval_toGBCoeffPolyS_singleton (s : DensePoly ℚ) : (toGBCoeffPolyS [s]).eval iU = toS s := by
  rw [show toGBCoeffPolyS [s] = C (toS s) from by
    rw [toGBCoeffPolyS_eq_map, DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_nil,
      mul_zero, add_zero, map_C]; rfl, eval_C]
theorem eval_toGBCoeffPolyS_shift (h : List (DensePoly ℚ)) :
    (toGBCoeffPolyS ([] :: h)).eval iU = iU * (toGBCoeffPolyS h).eval iU := by
  rw [toGBCoeffPolyS_eq_map, DensePoly.toPolyG_cons_dense, toPolyG_nil, map_zero,
    zero_add, Polynomial.map_mul, Polynomial.map_X, eval_mul, eval_X]
  rfl

/-- The numerator `realNum + i·imagNum` vanishes at `t = i` (since `z = c(i)`). -/
theorem numerator_eval_zero (c1 c2 : List (DensePoly ℚ)) (s1 s2 : DensePoly ℚ) (nN : ℚ) :
    (cplx
        (DensePoly.cadd (DensePoly.csub c1 [csub (evalAtI c1).1 (evalAtI c2).2])
          (cscaleListQ nN (DensePoly.cadd [[], s1] [s2])))
        (DensePoly.cadd (DensePoly.csub c2 [cadd (evalAtI c1).2 (evalAtI c2).1])
          (cscaleListQ nN (DensePoly.csub [[], s2] [s1])))).eval iU = 0 := by
  unfold cplx
  rw [eval_add, eval_mul, eval_C]
  rw [toGBCoeffPolyS_cadd, toGBCoeffPolyS_cadd, toGBCoeffPolyS_csub, toGBCoeffPolyS_csub, toGBCoeffPolyS_cscaleListQ,
    toGBCoeffPolyS_cscaleListQ, toGBCoeffPolyS_cadd, toGBCoeffPolyS_csub]
  simp only [eval_add, eval_sub, eval_mul, eval_C]
  rw [evalAtI_spec c1, evalAtI_spec c2, eval_toGBCoeffPolyS_singleton, eval_toGBCoeffPolyS_singleton,
    eval_toGBCoeffPolyS_singleton, eval_toGBCoeffPolyS_singleton, eval_toGBCoeffPolyS_shift, eval_toGBCoeffPolyS_shift,
    eval_toGBCoeffPolyS_singleton, eval_toGBCoeffPolyS_singleton]
  -- now everything is in terms of toS of evalAtI parts and s1,s2
  rw [pairToS, pairToS]
  simp only [toS_sub, toS_add]
  linear_combination ((evalAtI c2).2.toS + (AdjoinRoot.of (X ^ 2 + 1 : (Polynomial ℚ)[X]) (C nN)) * s2.toS) * iU_sq
/-! ### The `divByTminusI` reduction, projected to two real `ℚ[x][t]` identities -/

theorem toGBCoeffPolyS_shift (h : List (DensePoly ℚ)) : toGBCoeffPolyS ([] :: h) = X * toGBCoeffPolyS h := by
  rw [toGBCoeffPolyS_eq_map, DensePoly.toPolyG_cons_dense, toPolyG_nil, map_zero,
    zero_add, Polynomial.map_mul, Polynomial.map_X]; rfl

/-- `(t − i)·(D₁ + i·D₂) = cplx (t·D₁ + D₂) (t·D₂ − D₁)`. -/
theorem mul_X_sub_iU_cplx (d1 d2 : List (DensePoly ℚ)) :
    (X - C iU) * cplx d1 d2 = cplx (DensePoly.cadd ([] :: d1) d2) (DensePoly.csub ([] :: d2) d1) := by
  unfold cplx
  rw [toGBCoeffPolyS_cadd, toGBCoeffPolyS_csub, toGBCoeffPolyS_shift, toGBCoeffPolyS_shift]
  have hii : (C iU : SGauss[X]) ^ 2 = -1 := by
    rw [← map_pow, iU_sq, map_neg, map_one]
  linear_combination (-(toGBCoeffPolyS d2)) * hii

/-- The reduction step, real form: for `quot = divByTminusI (zip realNum imagNum)`, the two
`ℚ[x][t]` identities relating `realNum`/`imagNum` to `quot` hold. -/
theorem reduction_real (c1 c2 : List (DensePoly ℚ)) (s1 s2 : DensePoly ℚ) (nN : ℚ)
    (realNum imagNum : List (DensePoly ℚ))
    (hr : realNum = DensePoly.cadd (DensePoly.csub c1 [csub (evalAtI c1).1 (evalAtI c2).2])
      (cscaleListQ nN (DensePoly.cadd [[], s1] [s2])))
    (hi : imagNum = DensePoly.cadd (DensePoly.csub c2 [cadd (evalAtI c1).2 (evalAtI c2).1])
      (cscaleListQ nN (DensePoly.csub [[], s2] [s1])))
    (cpairs : List (DensePoly ℚ × DensePoly ℚ))
    (hcp : cpairs = (List.range (max realNum.length imagNum.length)).map
      (fun k => (realNum.getD k [], imagNum.getD k [])))
    (quot : List (DensePoly ℚ × DensePoly ℚ)) (hq : quot = divByTminusI cpairs) :
    DensePoly.toPoly realNum = DensePoly.toPoly (DensePoly.cadd ([] :: quot.map Prod.fst) (quot.map Prod.snd)) ∧
      DensePoly.toPoly imagNum = DensePoly.toPoly (DensePoly.csub ([] :: quot.map Prod.snd) (quot.map Prod.fst)) := by
  have hzip : pairListToS cpairs = cplx realNum imagNum := by
    rw [hcp, pairListToS_zip realNum imagNum _ (le_max_left _ _) (le_max_right _ _)]; rfl
  have hspec := divByTminusI_spec cpairs
  rw [hzip] at hspec
  have hev : (cplx realNum imagNum).eval iU = 0 := by
    rw [hr, hi]; exact numerator_eval_zero c1 c2 s1 s2 nN
  rw [hev, map_zero, add_zero, ← hq] at hspec
  have hquot : pairListToS quot = cplx (quot.map Prod.fst) (quot.map Prod.snd) := (cplx_quot quot).symm
  rw [hquot, mul_X_sub_iU_cplx] at hspec
  exact cplx_eq_imp _ _ _ _ hspec

/-! ### The telescoping induction -/

/-- The coupled `t`-polynomial system at level `n` over `ℚ[x][t]` (`a = −1`, `η = 1`):
`D q₁ + (b₀ − n·t)·q₁ − b₂·q₂ = c₁` and `D q₂ + b₂·q₁ + (b₀ − n·t)·q₂ = c₂`. -/
def TanSolves (b0 b2 : DensePoly ℚ) (n : ℕ) (c1 c2 q1 q2 : List (DensePoly ℚ)) : Prop :=
  DensePoly.toPoly (tanDeriv q1)
      + (C (toPoly b0) - C (C ((n : ℚ))) * X) * DensePoly.toPoly q1
      - C (toPoly b2) * DensePoly.toPoly q2 = DensePoly.toPoly c1
    ∧ DensePoly.toPoly (tanDeriv q2)
      + C (toPoly b2) * DensePoly.toPoly q1
      + (C (toPoly b0) - C (C ((n : ℚ))) * X) * DensePoly.toPoly q2 = DensePoly.toPoly c2

/-- Base case (`n = 0`, `q = [s]`): the singleton solution solves the level-0 coupled `t`-system. -/
theorem reconstruct_base [CLinearSolve ℚ] [LawfulCLinearSolve ℚ]
    (dbound : ℕ) (b0 b2 : DensePoly ℚ) (c1 c2 : List (DensePoly ℚ))
    (s1 s2 : DensePoly ℚ) (hd1 : cdeg c1 = 0) (hd2 : cdeg c2 = 0)
    (hsolve : cCoupledDESystem (-1) b0 b2 (c1.getD 0 []) (c2.getD 0 []) dbound = some (s1, s2)) :
    TanSolves b0 b2 0 c1 c2 [s1] [s2] := by
  obtain ⟨hb1, hb2⟩ := cCoupledDESystem_sound (-1) b0 b2 (c1.getD 0 []) (c2.getD 0 [])
    dbound s1 s2 hsolve
  refine ⟨?_, ?_⟩
  · rw [toPolyG_tanDeriv_singleton, DensePoly.toPolyG_cons_dense,
      DensePoly.toPolyG_nil, mul_zero, add_zero, DensePoly.toPolyG_cons_dense,
      DensePoly.toPolyG_nil, mul_zero, add_zero,
      DensePoly.toPolyG_eq_C_of_cdeg_eq_zero c1 hd1, DensePoly.toR_densePoly]
    simp only [Nat.cast_zero, map_zero, zero_mul, sub_zero]
    rw [show C (toPoly (cderiv s1)) = C (derivative (toPoly s1)) from by
        simp only [denote]]
    have h := congrArg (Polynomial.C (R := Polynomial ℚ)) hb1
    rw [map_add, map_add, map_mul, map_mul, map_mul] at h
    simp only [map_neg, map_one] at h
    linear_combination h
  · rw [toPolyG_tanDeriv_singleton, DensePoly.toPolyG_cons_dense,
      DensePoly.toPolyG_nil, mul_zero, add_zero, DensePoly.toPolyG_cons_dense,
      DensePoly.toPolyG_nil, mul_zero, add_zero,
      DensePoly.toPolyG_eq_C_of_cdeg_eq_zero c2 hd2, DensePoly.toR_densePoly]
    simp only [Nat.cast_zero, map_zero, zero_mul, sub_zero]
    rw [show C (toPoly (cderiv s2)) = C (derivative (toPoly s2)) from by
        simp only [denote]]
    have h := congrArg (Polynomial.C (R := Polynomial ℚ)) hb2
    rw [map_add, map_add, map_mul, map_mul] at h
    linear_combination h

/-- Telescoping reconstruction: a returned `cCoupledDECancelTan` solution solves the coupled system
at the `ℚ[x][t]` level (`D = ∂x + (t²+1)∂t`), by induction on `n`. -/
theorem reconstruct [CLinearSolve ℚ] [LawfulCLinearSolve ℚ]
    (dbound : ℕ) (b0 : DensePoly ℚ) :
    ∀ (n : ℕ) (b2 : DensePoly ℚ) (c1 c2 q1 q2 : List (DensePoly ℚ)),
      cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2) →
      TanSolves b0 b2 n c1 c2 q1 q2 := by
  intro n
  induction n with
  | zero =>
    intro b2 c1 c2 q1 q2 hsome
    rw [cCoupledDECancelTan] at hsome
    by_cases hd : (decide (cdeg c1 = 0) && decide (cdeg c2 = 0)) = true
    · rw [hd, if_pos rfl] at hsome
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hd
      rcases hm : cCoupledDESystem (-1) b0 b2 (c1.getD 0 []) (c2.getD 0 []) dbound
        with _ | ⟨s1, s2⟩
      · rw [hm] at hsome; simp at hsome
      · rw [hm, Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨hq1, hq2⟩ := hsome; subst hq1 hq2
        exact reconstruct_base dbound b0 b2 c1 c2 s1 s2 hd.1 hd.2 hm
    · rw [Bool.not_eq_true] at hd; rw [hd] at hsome; simp at hsome
  | succ m ih =>
    intro b2 c1 c2 q1 q2 hsome
    rw [cCoupledDECancelTan] at hsome
    set nN : ℚ := ((m : ℚ) + 1) with hnN
    set z1 := csub (evalAtI c1).1 (evalAtI c2).2 with hz1
    set z2 := cadd (evalAtI c1).2 (evalAtI c2).1 with hz2
    set b2shift := csub b2 (cscale nN [CCommRing.one]) with hb2shift
    rcases hbase : cCoupledDESystem (-1) b0 b2shift z1 z2 dbound with _ | ⟨s1, s2⟩
    · rw [hbase] at hsome; simp at hsome
    · rw [hbase] at hsome
      simp only at hsome
      set realNum := DensePoly.cadd (DensePoly.csub c1 [z1]) (cscaleListQ nN (DensePoly.cadd [[], s1] [s2])) with hrN
      set imagNum := DensePoly.cadd (DensePoly.csub c2 [z2]) (cscaleListQ nN (DensePoly.csub [[], s2] [s1])) with hiN
      set cpairs := (List.range (max realNum.length imagNum.length)).map
        (fun k => (realNum.getD k [], imagNum.getD k [])) with hcp
      set quot := divByTminusI cpairs with hquot
      rcases hrec : cCoupledDECancelTan dbound b0 (cadd b2 [CCommRing.one])
        (quot.map Prod.fst) (quot.map Prod.snd) m with _ | ⟨h1, h2⟩
      · rw [hrec] at hsome; simp at hsome
      · rw [hrec] at hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨hq1, hq2⟩ := hsome; subst hq1 hq2
        have hih := ih (cadd b2 [CCommRing.one]) (quot.map Prod.fst) (quot.map Prod.snd) h1 h2 hrec
        have hred := reduction_real c1 c2 s1 s2 nN realNum imagNum hrN hiN cpairs hcp quot hquot
        obtain ⟨hb1, hb2⟩ := cCoupledDESystem_sound (-1) b0 b2shift z1 z2 dbound s1 s2 hbase
        -- Abbreviate.
        set H1 := DensePoly.toPoly h1; set H2 := DensePoly.toPoly h2
        set D1 := DensePoly.toPoly (quot.map Prod.fst) with hD1; set D2 := DensePoly.toPoly (quot.map Prod.snd) with hD2
        set DH1 := DensePoly.toPoly (tanDeriv h1); set DH2 := DensePoly.toPoly (tanDeriv h2)
        -- b2+1 in ℚ[X].
        have hb2p1 : toPoly (cadd b2 [CCommRing.one]) = toPoly b2 + 1 := by
          simp [show CFieldSpec.toK (CCommRing.one:ℚ) = 1 from rfl]
        -- IH conjuncts in DensePoly.toPoly form.
        rw [TanSolves, hb2p1] at hih
        obtain ⟨hI1, hI2⟩ := hih
        -- reduction: DensePoly.toPoly realNum = X*D1 + D2 ; DensePoly.toPoly imagNum = X*D2 - D1.
        rw [show DensePoly.toPoly (DensePoly.cadd ([] :: quot.map Prod.fst) (quot.map Prod.snd)) = X * D1 + D2 from by
              rw [DensePoly.toPolyG_caddG, DensePoly.toPolyG_cons_dense, toPolyG_nil,
                map_zero, zero_add],
            show DensePoly.toPoly (DensePoly.csub ([] :: quot.map Prod.snd) (quot.map Prod.fst)) = X * D2 - D1 from by
              rw [DensePoly.toPolyG_csubG, DensePoly.toPolyG_cons_dense, toPolyG_nil,
                map_zero, zero_add]] at hred
        obtain ⟨hR1, hR2⟩ := hred
        -- expand DensePoly.toPoly of realNum / imagNum (as ℚ[x][t]).
        have hRexp : DensePoly.toPoly realNum
            = (DensePoly.toPoly c1 - C (toPoly z1)) + C (C nN) * (X * C (toPoly s1) + C (toPoly s2)) := by
          rw [hrN, DensePoly.toPolyG_caddG, DensePoly.toPolyG_csubG,
            DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_nil, mul_zero, add_zero,
            toPolyG_cscaleListQ, DensePoly.toPolyG_caddG, DensePoly.toPolyG_cons_dense,
            toPolyG_nil, map_zero, zero_add, DensePoly.toPolyG_cons_dense,
            DensePoly.toPolyG_nil, mul_zero, add_zero, DensePoly.toPolyG_cons_dense,
            DensePoly.toPolyG_nil, mul_zero, add_zero]
        have hIexp : DensePoly.toPoly imagNum
            = (DensePoly.toPoly c2 - C (toPoly z2)) + C (C nN) * (X * C (toPoly s2) - C (toPoly s1)) := by
          rw [hiN, DensePoly.toPolyG_caddG, DensePoly.toPolyG_csubG,
            DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_nil, mul_zero, add_zero,
            toPolyG_cscaleListQ, DensePoly.toPolyG_csubG, DensePoly.toPolyG_cons_dense,
            toPolyG_nil, map_zero, zero_add, DensePoly.toPolyG_cons_dense,
            DensePoly.toPolyG_nil, mul_zero, add_zero, DensePoly.toPolyG_cons_dense,
            DensePoly.toPolyG_nil, mul_zero, add_zero]
        rw [hRexp] at hR1; rw [hIexp] at hR2
        -- base solve identities, mapped C : ℚ[x] → ℚ[x][t].
        have hB2shift : toPoly b2shift = toPoly b2 - C nN := by
          rw [hb2shift]
          simp only [denote, CFieldSpec.toK, id_eq, mul_zero, add_zero]
          rw [show (CCommRing.one : ℚ) = 1 from rfl, map_one, mul_one]
        rw [hB2shift] at hb1 hb2
        have hCB1 := congrArg (Polynomial.C (R := Polynomial ℚ)) hb1
        have hCB2 := congrArg (Polynomial.C (R := Polynomial ℚ)) hb2
        simp only [map_add, map_sub, map_mul, map_neg, map_one] at hCB1 hCB2
        have hsh1 : ([[]] ++ h1 : List (DensePoly ℚ)) = [] :: h1 := rfl
        have hsh2 : ([[]] ++ h2 : List (DensePoly ℚ)) = [] :: h2 := rfl
        -- expand DensePoly.toPoly / DensePoly.toPoly∘tanDeriv of the assembled q1, q2.
        have hQ1 : DensePoly.toPoly (DensePoly.cadd (DensePoly.cadd ([[]] ++ h1) h2) [s1]) = X * H1 + H2 + C (toPoly s1) := by
          rw [hsh1, DensePoly.toPolyG_caddG, DensePoly.toPolyG_caddG,
            DensePoly.toPolyG_cons_dense, toPolyG_nil, map_zero, zero_add,
            DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_nil, mul_zero, add_zero]
        have hQ2 : DensePoly.toPoly (DensePoly.csub (DensePoly.cadd ([[]] ++ h2) [s2]) h1) = X * H2 + C (toPoly s2) - H1 := by
          rw [hsh2, DensePoly.toPolyG_csubG, DensePoly.toPolyG_caddG,
            DensePoly.toPolyG_cons_dense, toPolyG_nil, map_zero, zero_add,
            DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_nil, mul_zero, add_zero]
        have hDQ1 : DensePoly.toPoly (tanDeriv (DensePoly.cadd (DensePoly.cadd ([[]] ++ h1) h2) [s1]))
            = (X * DH1 + (X ^ 2 + 1) * H1) + DH2 + C (derivative (toPoly s1)) := by
          rw [hsh1, toPolyG_tanDeriv_cadd, toPolyG_tanDeriv_cadd, toPolyG_tanDeriv_shift,
            toPolyG_tanDeriv_singleton, toPolyG_cderivG]
        have hDQ2 : DensePoly.toPoly (tanDeriv (DensePoly.csub (DensePoly.cadd ([[]] ++ h2) [s2]) h1))
            = (X * DH2 + (X ^ 2 + 1) * H2) + C (derivative (toPoly s2)) - DH1 := by
          rw [hsh2, toPolyG_tanDeriv_csub, toPolyG_tanDeriv_cadd, toPolyG_tanDeriv_shift,
            toPolyG_tanDeriv_singleton, toPolyG_cderivG]
        rw [hnN] at hR1 hR2 hCB1 hCB2
        simp only [map_add, map_one] at hI1 hI2 hR1 hR2 hCB1 hCB2
        rw [TanSolves, hQ1, hQ2, hDQ1, hDQ2]
        push_cast
        simp only [map_add, map_one]
        constructor
        · linear_combination X * hI1 + hI2 + hCB1 - hR1
        · linear_combination X * hI2 - hI1 + hCB2 - hR2

/-- A successful `cCoupledDECancelTan … 2` solve satisfies `cancelTanClearedCheck … = true`,
since `reconstruct` makes the residual `t`-polynomials `DensePoly.toPoly = 0` at level `n = 2`. -/
theorem cancelTanClearedCheck_of_reconstruct [CLinearSolve ℚ] [LawfulCLinearSolve ℚ]
    (dbound : ℕ) (b0 b2 : DensePoly ℚ)
    (c1 c2 q1 q2 : List (DensePoly ℚ))
    (hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 2 = some (q1, q2)) :
    cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true := by
  obtain ⟨hG1, hG2⟩ := reconstruct dbound b0 2 b2 c1 c2 q1 q2 hsome
  rw [cancelTanClearedCheck, Bool.and_eq_true]
  constructor
  · rw [DensePoly.cisZeroG_iff]
    -- residual r1 = DensePoly.csub (DensePoly.cadd (tanDeriv q1) row1) c1, row1 = (b0 - 2t)q1 - b2 q2.
    rw [DensePoly.toPolyG_csubG, DensePoly.toPolyG_caddG, toPolyG_tanDeriv, DensePoly.toPolyG_caddG, DensePoly.toPolyG_csubG,
      toPolyG_map_cmulG, toPolyG_map_cmulG, toPolyG_mulT, toPolyG_twoT]
    -- hG1 (n=2): tanDeriv-part + (C b0 - C(C 2) X) Q1 - C b2 Q2 = C1.
    rw [toPolyG_tanDeriv] at hG1
    simp only [Nat.cast_ofNat] at hG1
    simp only [denote, CFieldSpec.toK, id_eq, map_mul, map_neg, map_one]
    linear_combination hG1
  · rw [DensePoly.cisZeroG_iff]
    rw [DensePoly.toPolyG_csubG, DensePoly.toPolyG_caddG, toPolyG_tanDeriv, DensePoly.toPolyG_caddG, toPolyG_map_cmulG, DensePoly.toPolyG_csubG,
      toPolyG_map_cmulG, toPolyG_mulT, toPolyG_twoT]
    rw [toPolyG_tanDeriv] at hG2
    simp only [Nat.cast_ofNat] at hG2
    linear_combination hG2

end DeepWiki.SymbolicIntegration.DensePoly

namespace DeepWiki.SymbolicIntegration
open DensePoly Polynomial

/-- Tangent RDE cancellation soundness: a successful `cCoupledDECancelTan dbound b0 b2 c1 c2 2` solve
`(q₁, q₂)` solves the tangent coupled `t`-polynomial system at the `ℚ[x][t]` level
(`D = ∂x + (t²+1)∂t`, diagonal shift `−2t`). -/
theorem cCoupledDECancelTan_sound [CLinearSolve ℚ] [LawfulCLinearSolve ℚ]
    (dbound : ℕ) (b0 b2 : DensePoly ℚ)
    (c1 c2 q1 q2 : List (DensePoly ℚ))
    (hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 2 = some (q1, q2)) :
    (DensePoly.toPoly (q1.map cderiv) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (DensePoly.toPoly q1))
        + (Polynomial.C (toPoly b0) * DensePoly.toPoly q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * DensePoly.toPoly q1)
        + Polynomial.C (toPoly (cscale (-1) b2)) * DensePoly.toPoly q2
      = DensePoly.toPoly c1 ∧
      (DensePoly.toPoly (q2.map cderiv) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (DensePoly.toPoly q2))
        + Polynomial.C (toPoly b2) * DensePoly.toPoly q1
        + (Polynomial.C (toPoly b0) * DensePoly.toPoly q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * DensePoly.toPoly q2)
      = DensePoly.toPoly c2 :=
  cancelTanClearedCheck_sound b0 b2 c1 c2 q1 q2
    (DensePoly.cancelTanClearedCheck_of_reconstruct dbound b0 b2 c1 c2 q1 q2 hsome)

-- ★ Restatement against the intended wording.
example [CLinearSolve ℚ] [LawfulCLinearSolve ℚ]
    (dbound : ℕ) (b0 b2 : DensePoly ℚ) (c1 c2 q1 q2 : List (DensePoly ℚ))
    (hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 2 = some (q1, q2)) :
    (DensePoly.toPoly (q1.map cderiv) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (DensePoly.toPoly q1))
        + (Polynomial.C (toPoly b0) * DensePoly.toPoly q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * DensePoly.toPoly q1)
        + Polynomial.C (toPoly (cscale (-1) b2)) * DensePoly.toPoly q2
      = DensePoly.toPoly c1 ∧
      (DensePoly.toPoly (q2.map cderiv) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (DensePoly.toPoly q2))
        + Polynomial.C (toPoly b2) * DensePoly.toPoly q1
        + (Polynomial.C (toPoly b0) * DensePoly.toPoly q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * DensePoly.toPoly q2)
      = DensePoly.toPoly c2 :=
  cCoupledDECancelTan_sound dbound b0 b2 c1 c2 q1 q2 hsome

#print axioms cCoupledDECancelTan_sound

end DeepWiki.SymbolicIntegration
