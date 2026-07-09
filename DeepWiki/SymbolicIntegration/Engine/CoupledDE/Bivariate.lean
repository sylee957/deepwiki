import DeepWiki.SymbolicIntegration.Engine.CoupledDE.Tangent

/-! # Bivariate bridge for tangent coupled systems

The `toPoly2` bridge reads `t`-polynomial lists into `ℚ[x][t]` and proves that tangent
cleared checks imply genuine bivariate polynomial identities. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ## The `t`-polynomial bivariate bridge `toPoly2 : ℚ[x][t]` -/

open CPolyG in
/-- `toPoly2 p`: bivariate bridge `List (CPolyG ℚ) → ℚ[x][t]`, Horner over `t`,
`toPoly2 (c :: cs) = C(toPolyG c) + X·toPoly2 cs`. -/
noncomputable def toPoly2 : List (CPolyG ℚ) → Polynomial (Polynomial ℚ)
  | [] => 0
  | c :: cs => Polynomial.C (toPolyG c) + Polynomial.X * toPoly2 cs

@[simp] theorem toPoly2_nil : toPoly2 [] = 0 := rfl

@[simp] theorem toPoly2_cons (c : CPolyG ℚ) (cs : List (CPolyG ℚ)) :
    toPoly2 (c :: cs) = Polynomial.C (toPolyG c) + Polynomial.X * toPoly2 cs := rfl

/-- `toPoly2_eq_sum_getD`: `toPoly2 p = Σ_{k<N} C(toPolyG (p.getD k []))·Xᵏ` for any `N ≥ p.length`. -/
theorem toPoly2_eq_sum_getD (p : List (CPolyG ℚ)) (N : ℕ) (hN : p.length ≤ N) :
    toPoly2 p = ∑ k ∈ Finset.range N,
      Polynomial.C (toPolyG (p.getD k [])) * Polynomial.X ^ k := by
  induction p generalizing N with
  | nil =>
    simp only [toPoly2_nil, List.getD_nil, toPolyG_nil, map_zero, zero_mul, Finset.sum_const_zero]
  | cons c cs ih =>
    cases N with
    | zero => simp at hN
    | succ M =>
      rw [toPoly2_cons, Finset.sum_range_succ', ih M (by simpa using hN), Finset.mul_sum]
      simp only [List.getD_cons_succ, pow_succ, List.getD_cons_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- `getD_range_map`: `((List.range n).map f).getD k [] = f k` for `k < n`. -/
theorem getD_range_map (f : ℕ → CPolyG ℚ) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f).getD k [] = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- `getD_out`: `p.getD k [] = []` for `p.length ≤ k`. -/
theorem getD_out (p : List (CPolyG ℚ)) (k : ℕ) (hk : p.length ≤ k) : p.getD k [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl

open CPolyG in
/-- `toPoly2_eq_zero_of_tisZero`: `tisZero p = true ⟹ toPoly2 p = 0`. -/
theorem toPoly2_eq_zero_of_tisZero (p : List (CPolyG ℚ)) (h : tisZero p = true) :
    toPoly2 p = 0 := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    rw [tisZero, List.all_cons, Bool.and_eq_true] at h
    rw [toPoly2_cons, (cisZeroG_iff c).mp h.1, map_zero, ih h.2, mul_zero, add_zero]

open CPolyG in
/-- `toPoly2_tadd`: `toPoly2 (tadd p q) = toPoly2 p + toPoly2 q`. -/
theorem toPoly2_tadd (p q : List (CPolyG ℚ)) :
    toPoly2 (tadd p q) = toPoly2 p + toPoly2 q := by
  set N := max p.length q.length with hN
  rw [toPoly2_eq_sum_getD (tadd p q) N (by rw [tadd]; simp [hN]),
    toPoly2_eq_sum_getD p N (le_max_left _ _), toPoly2_eq_sum_getD q N (le_max_right _ _),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [tadd, getD_range_map _ _ _ hk]
  simp only [denote, map_add]
  rw [add_mul]

open CPolyG in
/-- `toPoly2_tsub`: `toPoly2 (tsub p q) = toPoly2 p − toPoly2 q`. -/
theorem toPoly2_tsub (p q : List (CPolyG ℚ)) :
    toPoly2 (tsub p q) = toPoly2 p - toPoly2 q := by
  set N := max p.length q.length with hN
  rw [toPoly2_eq_sum_getD (tsub p q) N (by rw [tsub]; simp [hN]),
    toPoly2_eq_sum_getD p N (le_max_left _ _), toPoly2_eq_sum_getD q N (le_max_right _ _),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [tsub, getD_range_map _ _ _ hk]
  simp only [denote, map_sub]
  rw [sub_mul]

open CPolyG in
/-- `toPoly2_coeff`: `(toPoly2 p).coeff k = toPolyG (p.getD k [])`. -/
theorem toPoly2_coeff (p : List (CPolyG ℚ)) (k : ℕ) :
    (toPoly2 p).coeff k = toPolyG (p.getD k []) := by
  induction p generalizing k with
  | nil => simp
  | cons c cs ih =>
    rw [toPoly2_cons, Polynomial.coeff_add]
    cases k with
    | zero => simp
    | succ m =>
      rw [List.getD_cons_succ, Polynomial.coeff_X_mul, ih m]
      simp

open CPolyG in
/-- `toPoly2_map_cmulG`: `toPoly2 (p.map (cmulG s)) = C(toPolyG s) · toPoly2 p`. -/
theorem toPoly2_map_cmulG (s : CPolyG ℚ) (p : List (CPolyG ℚ)) :
    toPoly2 (p.map (cmulG s)) = Polynomial.C (toPolyG s) * toPoly2 p := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, toPoly2_cons, toPoly2_cons, ih]
    simp only [denote, map_mul]
    ring

open CPolyG in
/-- `toPolyG_foldl_caddG`: `toPolyG ((List.range n).foldl (fun acc i => caddG acc (g i)) init)
= toPolyG init + Σ_{i<n} toPolyG (g i)`. -/
theorem toPolyG_foldl_caddG (g : ℕ → CPolyG ℚ) :
    ∀ (n : ℕ) (init : CPolyG ℚ),
      toPolyG ((List.range n).foldl (fun acc i => caddG acc (g i)) init)
        = toPolyG init + ∑ i ∈ Finset.range n, toPolyG (g i) := by
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

open CPolyG in
/-- `toPoly2_mulT`: `toPoly2 (mulT p q) = toPoly2 p · toPoly2 q`, where `mulT` is the Cauchy-product
`(mulT p q)_k = Σ_{i≤k} p_i·q_{k−i}`. -/
theorem toPoly2_mulT (p q : List (CPolyG ℚ)) :
    toPoly2 ((List.range (p.length + q.length)).map (fun k =>
        (List.range (k + 1)).foldl (fun acc i =>
          caddG acc (cmulG (p.getD i []) (q.getD (k - i) []))) []))
      = toPoly2 p * toPoly2 q := by
  apply Polynomial.ext
  intro k
  rw [toPoly2_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  by_cases hk : k < p.length + q.length
  · rw [getD_range_map _ _ _ hk, toPolyG_foldl_caddG, toPolyG_nil, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    simp only [denote, toPoly2_coeff]
  · rw [getD_out _ _ (by rw [List.length_map, List.length_range]; omega), toPolyG_nil]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [toPoly2_coeff, toPoly2_coeff]
    rcases le_or_gt p.length i with hip | hip
    · rw [getD_out p _ hip, toPolyG_nil, zero_mul]
    · rw [getD_out q (k - i) (by omega), toPolyG_nil, mul_zero]

open CPolyG in
/-- `tanDeriv_dpdt_getD`: the formal `t`-derivative reads coefficientwise,
`dpdt.getD k [] = cscaleG ((k:ℚ)+1) (p.getD (k+1) [])`. -/
theorem tanDeriv_dpdt_getD (p : List (CPolyG ℚ)) (k : ℕ) :
    ((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1)).getD k []
      = cscaleG ((k : ℚ) + 1) (p.getD (k + 1) []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_drop,
    List.getD_eq_getElem?_getD, show (0 + k) = k from by ring, show (1 + k) = (k + 1) from by ring]
  cases p[k + 1]? with
  | none => simp [cscaleG]
  | some a => simp

open CPolyG in
/-- `toPoly2_dpdt`: `toPoly2 dpdt = D_t (toPoly2 p)` (`Polynomial.derivative`) for `dpdt` the formal
`dp/dt` list. -/
theorem toPoly2_dpdt (p : List (CPolyG ℚ)) :
    toPoly2 ((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1))
      = Polynomial.derivative (toPoly2 p) := by
  apply Polynomial.ext
  intro k
  rw [toPoly2_coeff, tanDeriv_dpdt_getD]
  simp only [denote]
  rw [Polynomial.coeff_derivative, toPoly2_coeff]
  simp only [CFieldSpec.toK, id_eq]
  rw [map_add, map_one, Polynomial.C_eq_natCast]
  ring

open CPolyG in
/-- `toPoly2_mulDt`: `toPoly2 mulDt = (X²+1)·toPoly2 dpdt` for `mulDt` the `(t²+1)·dpdt` list. -/
theorem toPoly2_mulDt (dpdt : List (CPolyG ℚ)) :
    toPoly2 ((List.range (dpdt.length + 2)).map (fun k =>
        caddG (if k ≥ 2 then dpdt.getD (k - 2) [] else []) (dpdt.getD k [])))
      = (Polynomial.X ^ 2 + 1) * toPoly2 dpdt := by
  apply Polynomial.ext
  intro k
  rw [toPoly2_coeff, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
  by_cases hk : k < dpdt.length + 2
  · rw [getD_range_map _ _ _ hk]
    simp only [denote]
    rw [toPoly2_coeff, apply_ite toPolyG, toPolyG_nil]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, toPoly2_coeff]
    · rw [if_neg h2, toPoly2_coeff]
  · have hcoeffk : (toPoly2 dpdt).coeff k = 0 := by
      rw [toPoly2_coeff, getD_out _ _ (by omega), toPolyG_nil]
    rw [getD_out _ _ (by rw [List.length_map, List.length_range]; omega), toPolyG_nil, hcoeffk]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, toPoly2_coeff, getD_out _ _ (by omega), toPolyG_nil, add_zero]
    · rw [if_neg h2, add_zero]

open CPolyG in
/-- `toPoly2_tanDeriv`: the tangent derivation is bivariate `D = ∂/∂x + (t²+1)·∂/∂t`,
`toPoly2 (tanDeriv p) = toPoly2 (p.map cderivQ) + (X²+1)·D_t(toPoly2 p)` over `ℚ[x][t]`. -/
theorem toPoly2_tanDeriv (p : List (CPolyG ℚ)) :
    toPoly2 (tanDeriv p)
      = toPoly2 (p.map cderivQ)
        + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 p) := by
  show toPoly2 (tadd (p.map cderivQ)
      ((List.range (((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1)).length + 2)).map
        (fun k => caddG
          (if k ≥ 2 then ((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1)).getD (k - 2) []
            else [])
          (((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1)).getD k [])))) = _
  rw [toPoly2_tadd, toPoly2_mulDt, toPoly2_dpdt]

/-! ## Tangent cleared checks -/

/-- `cancelTanC1 = −t²+2t−8x²+1` as a `t`-polynomial (`t⁰ ↦ 1−8x²`, `t¹ ↦ 2`, `t² ↦ −1`). -/
def cancelTanC1 : List (CPolyG ℚ) := [[1, 0, -8], [2], [-1]]
/-- `cancelTanC2 = 2−4x` as a `t`-polynomial (constant in `t`). -/
def cancelTanC2 : List (CPolyG ℚ) := [[2, -4]]

/-- `cancelTanClearedCheck b0 b2 c1 c2 q1 q2`: `true` iff `(q₁, q₂)` solves the tangent `t`-polynomial
system `(Dq₁; Dq₂) + [[b₀−2t, −b₂],[b₂, b₀−2t]](q₁; q₂) = (c₁; c₂)` (`a = −1`, `n = 2`, `D = tanDeriv`),
checked as both cleared residuals being `tisZero`. -/
def cancelTanClearedCheck (b0 b2 : CPolyG ℚ) (c1 c2 q1 q2 : List (CPolyG ℚ)) : Bool :=
  -- diagonal shift `±2t`: as a t-polynomial, `2t = [0, 2]` (ℚ[x]-coefficients [0] then [2]).
  let twoT : List (CPolyG ℚ) := [[], [2]]
  -- matrix·(q₁;q₂): row1 = (b₀−2t)q₁ + (−b₂)q₂; row2 = b₂q₁ + (b₀+2t)q₂  (as t-polynomials).
  let mulConst : CPolyG ℚ → List (CPolyG ℚ) → List (CPolyG ℚ) := fun s p => p.map (cmulG s)
  let mulT : List (CPolyG ℚ) → List (CPolyG ℚ) → List (CPolyG ℚ) := fun p q =>
    let n := p.length + q.length
    (List.range n).map (fun k =>
      (List.range (k + 1)).foldl (fun acc i =>
        caddG acc (cmulG (p.getD i []) (q.getD (k - i) []))) [])
  let row1 := tadd (tsub (mulConst b0 q1) (mulT twoT q1)) (mulConst (cscaleG (-1) b2) q2)
  let row2 := tadd (mulConst b2 q1) (tsub (mulConst b0 q2) (mulT twoT q2))
  let r1 := tsub (tadd (tanDeriv q1) row1) c1
  let r2 := tsub (tadd (tanDeriv q2) row2) c2
  tisZero r1 && tisZero r2

open CPolyG in
/-- `toPoly2_twoT`: `toPoly2 [[],[2]] = C(C 2)·X` (the diagonal `2t` as a `ℚ[x][t]` polynomial). -/
theorem toPoly2_twoT :
    toPoly2 ([[], [2]] : List (CPolyG ℚ)) = Polynomial.C (Polynomial.C 2) * Polynomial.X := by
  show toPoly2 ([[], [2]] : List (CPolyG ℚ)) = _
  rw [toPoly2_cons, toPoly2_cons, toPoly2_nil]
  simp only [toPolyG_nil, map_zero, mul_zero, add_zero, zero_add]
  rw [show toPolyG ([2] : CPolyG ℚ) = Polynomial.C 2 by
    simp only [denote]
    simp [CFieldSpec.toK]]
  ring

open CPolyG in
/-- `cancelTanClearedCheck_sound`: if `cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true` then `(q₁, q₂)`
solves the tangent `t`-polynomial system at the `ℚ[x][t]` level — both rows of
`(Dq; …) + [[b₀−2t, −b₂],[b₂, b₀−2t]]·q = c`, `D = ∂/∂x + (t²+1)·∂/∂t`. -/
theorem cancelTanClearedCheck_sound (b0 b2 : CPolyG ℚ) (c1 c2 q1 q2 : List (CPolyG ℚ))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
    (toPoly2 (q1.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q1))
        + (Polynomial.C (toPolyG b0) * toPoly2 q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q1)
        + Polynomial.C (toPolyG (cscaleG (-1) b2)) * toPoly2 q2
      = toPoly2 c1 ∧
      (toPoly2 (q2.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q2))
        + Polynomial.C (toPolyG b2) * toPoly2 q1
        + (Polynomial.C (toPolyG b0) * toPoly2 q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q2)
      = toPoly2 c2 := by
  rw [cancelTanClearedCheck, Bool.and_eq_true] at hcheck
  obtain ⟨h1, h2⟩ := hcheck
  have e1 := toPoly2_eq_zero_of_tisZero _ h1
  have e2 := toPoly2_eq_zero_of_tisZero _ h2
  simp only [toPoly2_tsub, toPoly2_tadd, toPoly2_tanDeriv, toPoly2_map_cmulG, toPoly2_mulT,
    toPoly2_twoT, sub_eq_zero] at e1 e2
  exact ⟨by linear_combination e1, by linear_combination e2⟩

/-- `cCoupledDECancelTan_sound_of_check`: if `cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2)`
and the returned pair passes `cancelTanClearedCheck`, then `(q₁, q₂)` solves the tangent coupled
`t`-polynomial system at the `ℚ[x][t]` level (composition with `cancelTanClearedCheck_sound`). -/
theorem cCoupledDECancelTan_sound_of_check (dbound : ℕ) (b0 b2 : CPolyG ℚ)
    (c1 c2 q1 q2 : List (CPolyG ℚ)) (n : ℕ)
    (_hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
    (toPoly2 (q1.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q1))
        + (Polynomial.C (toPolyG b0) * toPoly2 q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q1)
        + Polynomial.C (toPolyG (cscaleG (-1) b2)) * toPoly2 q2
      = toPoly2 c1 ∧
      (toPoly2 (q2.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q2))
        + Polynomial.C (toPolyG b2) * toPoly2 q1
        + (Polynomial.C (toPolyG b0) * toPoly2 q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q2)
      = toPoly2 c2 :=
  cancelTanClearedCheck_sound b0 b2 c1 c2 q1 q2 hcheck

/-! ## Examples -/

/-- `rischDE_cancelTan_example`: the tangent coupled system over `t = tan(x)` (`b₀ = 0`, `b₂ = 4x`,
`c₁ = −t²+2t−8x²+1`, `c₂ = 2−4x`, degree bound `n = 2`) solves via `cCoupledDECancelTan` to
`q₁ = t − 1`, `q₂ = 2x`, verified by `cancelTanClearedCheck`. -/
theorem rischDE_cancelTan_example :
    (match cCoupledDECancelTan 1 ([] : CPolyG ℚ) [0, 4] cancelTanC1 cancelTanC2 2 with
      | some (q1, q2) =>
          cancelTanClearedCheck [] [0, 4] cancelTanC1 cancelTanC2 q1 q2
      | none => false) = true := by native_decide

/-! ## Restatement of tangent soundness -/

-- ★ Tangent RDE cancellation soundness, `native_decide`-free: a self-certifying `cCoupledDECancelTan` solve
-- gives both rows of the tangent coupled `t`-system over `ℚ[x][t]` (`D = ∂/∂x + (t²+1)∂/∂t`).
example (dbound : ℕ) (b0 b2 : CPolyG ℚ) (c1 c2 q1 q2 : List (CPolyG ℚ)) (n : ℕ)
    (hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
    (toPoly2 (q1.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q1))
        + (Polynomial.C (toPolyG b0) * toPoly2 q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q1)
        + Polynomial.C (toPolyG (cscaleG (-1) b2)) * toPoly2 q2
      = toPoly2 c1 ∧
      (toPoly2 (q2.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q2))
        + Polynomial.C (toPolyG b2) * toPoly2 q1
        + (Polynomial.C (toPolyG b0) * toPoly2 q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q2)
      = toPoly2 c2 :=
  cCoupledDECancelTan_sound_of_check dbound b0 b2 c1 c2 q1 q2 n hsome hcheck

end DeepWiki.SymbolicIntegration
