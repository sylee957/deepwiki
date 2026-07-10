import DeepWiki.SymbolicIntegration.Engine.CoupledDE.Tangent
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect

/-! # Bivariate semantics for tangent coupled systems

The generic `GBPolyCore.toGBCoeffPoly` denotation reads `t`-polynomial lists into `ℚ[x][t]`;
this file proves that tangent cleared checks imply genuine bivariate polynomial identities.
-/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-! ## The generic `t`-polynomial bivariate denotation -/

/-- `toGBCoeffPoly_eq_sum_getD`: `GBPolyCore.toGBCoeffPoly p = Σ_{k<N} C(toPoly (p.getD k []))·Xᵏ` for any `N ≥ p.length`. -/
theorem toGBCoeffPoly_eq_sum_getD (p : List (DensePoly ℚ)) (N : ℕ) (hN : p.length ≤ N) :
    GBPolyCore.toGBCoeffPoly p = ∑ k ∈ Finset.range N,
      Polynomial.C (toPoly (p.getD k [])) * Polynomial.X ^ k := by
  induction p generalizing N with
  | nil =>
    simp only [GBPolyCore.toGBCoeffPoly_nil, List.getD_nil, toPolyG_nil, map_zero, zero_mul, Finset.sum_const_zero]
  | cons c cs ih =>
    cases N with
    | zero => simp at hN
    | succ M =>
      rw [GBPolyCore.toGBCoeffPoly_cons, Finset.sum_range_succ', ih M (by simpa using hN), Finset.mul_sum]
      simp only [List.getD_cons_succ, pow_succ, List.getD_cons_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- `getD_range_map`: `((List.range n).map f).getD k [] = f k` for `k < n`. -/
theorem getD_range_map (f : ℕ → DensePoly ℚ) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f).getD k [] = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- `getD_out`: `p.getD k [] = []` for `p.length ≤ k`. -/
theorem getD_out (p : List (DensePoly ℚ)) (k : ℕ) (hk : p.length ≤ k) : p.getD k [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl

open DensePoly in
/-- `toGBCoeffPoly_eq_zero_of_tisZero`: `tisZero p = true ⟹ GBPolyCore.toGBCoeffPoly p = 0`. -/
theorem toGBCoeffPoly_eq_zero_of_tisZero (p : List (DensePoly ℚ)) (h : tisZero p = true) :
    GBPolyCore.toGBCoeffPoly p = 0 := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    rw [tisZero, List.all_cons, Bool.and_eq_true] at h
    rw [GBPolyCore.toGBCoeffPoly_cons, (cisZeroG_iff c).mp h.1, map_zero, ih h.2, mul_zero, add_zero]

open DensePoly in
/-- `toGBCoeffPoly_map_cmulG`: `GBPolyCore.toGBCoeffPoly (p.map (cmul s)) = C(toPoly s) · GBPolyCore.toGBCoeffPoly p`. -/
theorem toGBCoeffPoly_map_cmulG (s : DensePoly ℚ) (p : List (DensePoly ℚ)) :
    GBPolyCore.toGBCoeffPoly (p.map (cmul s)) = Polynomial.C (toPoly s) * GBPolyCore.toGBCoeffPoly p := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, GBPolyCore.toGBCoeffPoly_cons, GBPolyCore.toGBCoeffPoly_cons, ih]
    simp only [denote, map_mul]
    ring

open DensePoly in
/-- `toPolyG_foldl_caddG`: `toPoly ((List.range n).foldl (fun acc i => cadd acc (g i)) init)
= toPoly init + Σ_{i<n} toPoly (g i)`. -/
theorem toPolyG_foldl_caddG (g : ℕ → DensePoly ℚ) :
    ∀ (n : ℕ) (init : DensePoly ℚ),
      toPoly ((List.range n).foldl (fun acc i => cadd acc (g i)) init)
        = toPoly init + ∑ i ∈ Finset.range n, toPoly (g i) := by
  intro n
  induction n with
  | zero => intro init; simp
  | succ m ih =>
    intro init
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ]
    simp only [denote]
    rw [ih]
    ring

open DensePoly in
/-- `toGBCoeffPoly_mulT`: `GBPolyCore.toGBCoeffPoly (mulT p q) = GBPolyCore.toGBCoeffPoly p · GBPolyCore.toGBCoeffPoly q`, where `mulT` is the Cauchy-product
`(mulT p q)_k = Σ_{i≤k} p_i·q_{k−i}`. -/
theorem toGBCoeffPoly_mulT (p q : List (DensePoly ℚ)) :
    GBPolyCore.toGBCoeffPoly ((List.range (p.length + q.length)).map (fun k =>
        (List.range (k + 1)).foldl (fun acc i =>
          cadd acc (cmul (p.getD i []) (q.getD (k - i) []))) []))
      = GBPolyCore.toGBCoeffPoly p * GBPolyCore.toGBCoeffPoly q := by
  apply Polynomial.ext
  intro k
  rw [GBPolyCore.toGBCoeffPoly_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  by_cases hk : k < p.length + q.length
  · rw [getD_range_map _ _ _ hk, toPolyG_foldl_caddG, toPolyG_nil, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    simp only [denote, GBPolyCore.toGBCoeffPoly_coeff]
  · rw [getD_out _ _ (by rw [List.length_map, List.length_range]; omega), toPolyG_nil]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [GBPolyCore.toGBCoeffPoly_coeff, GBPolyCore.toGBCoeffPoly_coeff]
    rcases le_or_gt p.length i with hip | hip
    · rw [getD_out p _ hip, toPolyG_nil, zero_mul]
    · rw [getD_out q (k - i) (by omega), toPolyG_nil, mul_zero]

open DensePoly in
/-- `tanDeriv_dpdt_getD`: the formal `t`-derivative reads coefficientwise,
`dpdt.getD k [] = cscale ((k:ℚ)+1) (p.getD (k+1) [])`. -/
theorem tanDeriv_dpdt_getD (p : List (DensePoly ℚ)) (k : ℕ) :
    ((p.drop 1).zipIdx.map (fun x => cscale ((x.2 : ℚ) + 1) x.1)).getD k []
      = cscale ((k : ℚ) + 1) (p.getD (k + 1) []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_drop,
    List.getD_eq_getElem?_getD, show (0 + k) = k from by ring, show (1 + k) = (k + 1) from by ring]
  cases p[k + 1]? with
  | none => simp [cscale]
  | some a => simp

open DensePoly in
/-- `toGBCoeffPoly_dpdt`: `GBPolyCore.toGBCoeffPoly dpdt = D_t (GBPolyCore.toGBCoeffPoly p)` (`Polynomial.derivative`) for `dpdt` the formal
`dp/dt` list. -/
theorem toGBCoeffPoly_dpdt (p : List (DensePoly ℚ)) :
    GBPolyCore.toGBCoeffPoly ((p.drop 1).zipIdx.map (fun x => cscale ((x.2 : ℚ) + 1) x.1))
      = Polynomial.derivative (GBPolyCore.toGBCoeffPoly p) := by
  apply Polynomial.ext
  intro k
  rw [GBPolyCore.toGBCoeffPoly_coeff, tanDeriv_dpdt_getD]
  simp only [denote]
  rw [Polynomial.coeff_derivative, GBPolyCore.toGBCoeffPoly_coeff]
  simp only [CFieldSpec.toK, id_eq]
  rw [map_add, map_one, Polynomial.C_eq_natCast]
  ring

open DensePoly in
/-- `toGBCoeffPoly_mulDt`: `GBPolyCore.toGBCoeffPoly mulDt = (X²+1)·GBPolyCore.toGBCoeffPoly dpdt` for `mulDt` the `(t²+1)·dpdt` list. -/
theorem toGBCoeffPoly_mulDt (dpdt : List (DensePoly ℚ)) :
    GBPolyCore.toGBCoeffPoly ((List.range (dpdt.length + 2)).map (fun k =>
        cadd (if k ≥ 2 then dpdt.getD (k - 2) [] else []) (dpdt.getD k [])))
      = (Polynomial.X ^ 2 + 1) * GBPolyCore.toGBCoeffPoly dpdt := by
  apply Polynomial.ext
  intro k
  rw [GBPolyCore.toGBCoeffPoly_coeff, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
  by_cases hk : k < dpdt.length + 2
  · rw [getD_range_map _ _ _ hk]
    simp only [denote]
    rw [GBPolyCore.toGBCoeffPoly_coeff, apply_ite toPoly, toPolyG_nil]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, GBPolyCore.toGBCoeffPoly_coeff]
    · rw [if_neg h2, GBPolyCore.toGBCoeffPoly_coeff]
  · have hcoeffk : (GBPolyCore.toGBCoeffPoly dpdt).coeff k = 0 := by
      rw [GBPolyCore.toGBCoeffPoly_coeff, getD_out _ _ (by omega), toPolyG_nil]
    rw [getD_out _ _ (by rw [List.length_map, List.length_range]; omega), toPolyG_nil, hcoeffk]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, GBPolyCore.toGBCoeffPoly_coeff, getD_out _ _ (by omega), toPolyG_nil, add_zero]
    · rw [if_neg h2, add_zero]

open DensePoly in
/-- `toGBCoeffPoly_tanDeriv`: the tangent derivation is bivariate `D = ∂/∂x + (t²+1)·∂/∂t`,
`GBPolyCore.toGBCoeffPoly (tanDeriv p) = GBPolyCore.toGBCoeffPoly (p.map cderivQ) + (X²+1)·D_t(GBPolyCore.toGBCoeffPoly p)` over `ℚ[x][t]`. -/
theorem toGBCoeffPoly_tanDeriv (p : List (DensePoly ℚ)) :
    GBPolyCore.toGBCoeffPoly (tanDeriv p)
      = GBPolyCore.toGBCoeffPoly (p.map cderivQ)
        + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (GBPolyCore.toGBCoeffPoly p) := by
  show GBPolyCore.toGBCoeffPoly (DensePoly.cadd (p.map cderivQ)
      ((List.range (((p.drop 1).zipIdx.map (fun x => cscale ((x.2 : ℚ) + 1) x.1)).length + 2)).map
        (fun k => cadd
          (if k ≥ 2 then ((p.drop 1).zipIdx.map (fun x => cscale ((x.2 : ℚ) + 1) x.1)).getD (k - 2) []
            else [])
          (((p.drop 1).zipIdx.map (fun x => cscale ((x.2 : ℚ) + 1) x.1)).getD k [])))) = _
  rw [GBPolyCore.toGBCoeffPoly_cadd, toGBCoeffPoly_mulDt, toGBCoeffPoly_dpdt]

/-! ## Tangent cleared checks -/

/-- `cancelTanC1 = −t²+2t−8x²+1` as a `t`-polynomial (`t⁰ ↦ 1−8x²`, `t¹ ↦ 2`, `t² ↦ −1`). -/
def cancelTanC1 : List (DensePoly ℚ) := [[1, 0, -8], [2], [-1]]
/-- `cancelTanC2 = 2−4x` as a `t`-polynomial (constant in `t`). -/
def cancelTanC2 : List (DensePoly ℚ) := [[2, -4]]

/-- `cancelTanClearedCheck b0 b2 c1 c2 q1 q2`: `true` iff `(q₁, q₂)` solves the tangent `t`-polynomial
system `(Dq₁; Dq₂) + [[b₀−2t, −b₂],[b₂, b₀−2t]](q₁; q₂) = (c₁; c₂)` (`a = −1`, `n = 2`, `D = tanDeriv`),
checked as both cleared residuals being `tisZero`. -/
def cancelTanClearedCheck (b0 b2 : DensePoly ℚ) (c1 c2 q1 q2 : List (DensePoly ℚ)) : Bool :=
  -- diagonal shift `±2t`: as a t-polynomial, `2t = [0, 2]` (ℚ[x]-coefficients [0] then [2]).
  let twoT : List (DensePoly ℚ) := [[], [2]]
  -- matrix·(q₁;q₂): row1 = (b₀−2t)q₁ + (−b₂)q₂; row2 = b₂q₁ + (b₀+2t)q₂  (as t-polynomials).
  let mulConst : DensePoly ℚ → List (DensePoly ℚ) → List (DensePoly ℚ) := fun s p => p.map (cmul s)
  let mulT : List (DensePoly ℚ) → List (DensePoly ℚ) → List (DensePoly ℚ) := fun p q =>
    let n := p.length + q.length
    (List.range n).map (fun k =>
      (List.range (k + 1)).foldl (fun acc i =>
        cadd acc (cmul (p.getD i []) (q.getD (k - i) []))) [])
  let row1 := DensePoly.cadd (DensePoly.csub (mulConst b0 q1) (mulT twoT q1)) (mulConst (cscale (-1) b2) q2)
  let row2 := DensePoly.cadd (mulConst b2 q1) (DensePoly.csub (mulConst b0 q2) (mulT twoT q2))
  let r1 := DensePoly.csub (DensePoly.cadd (tanDeriv q1) row1) c1
  let r2 := DensePoly.csub (DensePoly.cadd (tanDeriv q2) row2) c2
  tisZero r1 && tisZero r2

open DensePoly in
/-- `toGBCoeffPoly_twoT`: `GBPolyCore.toGBCoeffPoly [[],[2]] = C(C 2)·X` (the diagonal `2t` as a `ℚ[x][t]` polynomial). -/
theorem toGBCoeffPoly_twoT :
    GBPolyCore.toGBCoeffPoly ([[], [2]] : List (DensePoly ℚ)) = Polynomial.C (Polynomial.C 2) * Polynomial.X := by
  show GBPolyCore.toGBCoeffPoly ([[], [2]] : List (DensePoly ℚ)) = _
  rw [GBPolyCore.toGBCoeffPoly_cons, GBPolyCore.toGBCoeffPoly_cons, GBPolyCore.toGBCoeffPoly_nil]
  simp only [toPolyG_nil, map_zero, mul_zero, add_zero, zero_add]
  rw [show toPoly ([2] : DensePoly ℚ) = Polynomial.C 2 by
    simp only [denote]
    simp [CFieldSpec.toK]]
  ring

open DensePoly in
/-- `cancelTanClearedCheck_sound`: if `cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true` then `(q₁, q₂)`
solves the tangent `t`-polynomial system at the `ℚ[x][t]` level — both rows of
`(Dq; …) + [[b₀−2t, −b₂],[b₂, b₀−2t]]·q = c`, `D = ∂/∂x + (t²+1)·∂/∂t`. -/
theorem cancelTanClearedCheck_sound (b0 b2 : DensePoly ℚ) (c1 c2 q1 q2 : List (DensePoly ℚ))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
    (GBPolyCore.toGBCoeffPoly (q1.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (GBPolyCore.toGBCoeffPoly q1))
        + (Polynomial.C (toPoly b0) * GBPolyCore.toGBCoeffPoly q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * GBPolyCore.toGBCoeffPoly q1)
        + Polynomial.C (toPoly (cscale (-1) b2)) * GBPolyCore.toGBCoeffPoly q2
      = GBPolyCore.toGBCoeffPoly c1 ∧
      (GBPolyCore.toGBCoeffPoly (q2.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (GBPolyCore.toGBCoeffPoly q2))
        + Polynomial.C (toPoly b2) * GBPolyCore.toGBCoeffPoly q1
        + (Polynomial.C (toPoly b0) * GBPolyCore.toGBCoeffPoly q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * GBPolyCore.toGBCoeffPoly q2)
      = GBPolyCore.toGBCoeffPoly c2 := by
  rw [cancelTanClearedCheck, Bool.and_eq_true] at hcheck
  obtain ⟨h1, h2⟩ := hcheck
  have e1 := toGBCoeffPoly_eq_zero_of_tisZero _ h1
  have e2 := toGBCoeffPoly_eq_zero_of_tisZero _ h2
  simp only [GBPolyCore.toGBCoeffPoly_csub, GBPolyCore.toGBCoeffPoly_cadd, toGBCoeffPoly_tanDeriv, toGBCoeffPoly_map_cmulG, toGBCoeffPoly_mulT,
    toGBCoeffPoly_twoT, sub_eq_zero] at e1 e2
  exact ⟨by linear_combination e1, by linear_combination e2⟩

/-- `cCoupledDECancelTan_sound_of_check`: if `cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2)`
and the returned pair passes `cancelTanClearedCheck`, then `(q₁, q₂)` solves the tangent coupled
`t`-polynomial system at the `ℚ[x][t]` level (composition with `cancelTanClearedCheck_sound`). -/
theorem cCoupledDECancelTan_sound_of_check (dbound : ℕ) (b0 b2 : DensePoly ℚ)
    (c1 c2 q1 q2 : List (DensePoly ℚ)) (n : ℕ)
    (_hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
    (GBPolyCore.toGBCoeffPoly (q1.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (GBPolyCore.toGBCoeffPoly q1))
        + (Polynomial.C (toPoly b0) * GBPolyCore.toGBCoeffPoly q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * GBPolyCore.toGBCoeffPoly q1)
        + Polynomial.C (toPoly (cscale (-1) b2)) * GBPolyCore.toGBCoeffPoly q2
      = GBPolyCore.toGBCoeffPoly c1 ∧
      (GBPolyCore.toGBCoeffPoly (q2.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (GBPolyCore.toGBCoeffPoly q2))
        + Polynomial.C (toPoly b2) * GBPolyCore.toGBCoeffPoly q1
        + (Polynomial.C (toPoly b0) * GBPolyCore.toGBCoeffPoly q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * GBPolyCore.toGBCoeffPoly q2)
      = GBPolyCore.toGBCoeffPoly c2 :=
  cancelTanClearedCheck_sound b0 b2 c1 c2 q1 q2 hcheck

/-! ## Examples -/

/-- `rischDE_cancelTan_example`: the tangent coupled system over `t = tan(x)` (`b₀ = 0`, `b₂ = 4x`,
`c₁ = −t²+2t−8x²+1`, `c₂ = 2−4x`, degree bound `n = 2`) solves via `cCoupledDECancelTan` to
`q₁ = t − 1`, `q₂ = 2x`, verified by `cancelTanClearedCheck`. -/
theorem rischDE_cancelTan_example :
    (match cCoupledDECancelTan 1 ([] : DensePoly ℚ) [0, 4] cancelTanC1 cancelTanC2 2 with
      | some (q1, q2) =>
          cancelTanClearedCheck [] [0, 4] cancelTanC1 cancelTanC2 q1 q2
      | none => false) = true := by native_decide

/-! ## Restatement of tangent soundness -/

-- ★ Tangent RDE cancellation soundness, `native_decide`-free: a self-certifying `cCoupledDECancelTan` solve
-- gives both rows of the tangent coupled `t`-system over `ℚ[x][t]` (`D = ∂/∂x + (t²+1)∂/∂t`).
example (dbound : ℕ) (b0 b2 : DensePoly ℚ) (c1 c2 q1 q2 : List (DensePoly ℚ)) (n : ℕ)
    (hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
    (GBPolyCore.toGBCoeffPoly (q1.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (GBPolyCore.toGBCoeffPoly q1))
        + (Polynomial.C (toPoly b0) * GBPolyCore.toGBCoeffPoly q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * GBPolyCore.toGBCoeffPoly q1)
        + Polynomial.C (toPoly (cscale (-1) b2)) * GBPolyCore.toGBCoeffPoly q2
      = GBPolyCore.toGBCoeffPoly c1 ∧
      (GBPolyCore.toGBCoeffPoly (q2.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (GBPolyCore.toGBCoeffPoly q2))
        + Polynomial.C (toPoly b2) * GBPolyCore.toGBCoeffPoly q1
        + (Polynomial.C (toPoly b0) * GBPolyCore.toGBCoeffPoly q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * GBPolyCore.toGBCoeffPoly q2)
      = GBPolyCore.toGBCoeffPoly c2 :=
  cCoupledDECancelTan_sound_of_check dbound b0 b2 c1 c2 q1 q2 n hsome hcheck

end DeepWiki.SymbolicIntegration
