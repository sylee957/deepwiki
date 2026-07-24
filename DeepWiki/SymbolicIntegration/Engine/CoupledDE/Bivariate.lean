import DeepWiki.SymbolicIntegration.Engine.CoupledDE.Tangent
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect

/-! # Bivariate semantics for tangent coupled systems

The generic `DensePoly.toPoly` denotation reads `t`-polynomial lists into `ℚ[x][t]`;
this file proves that tangent cleared checks imply genuine bivariate polynomial identities.
-/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-! ## The generic `t`-polynomial bivariate denotation -/

/-- `toPolyG_eq_sum_getD`: `DensePoly.toPoly p = Σ_{k<N} C(toPoly (p.getD k []))·Xᵏ` for any `N ≥ p.length`. -/
theorem toPolyG_eq_sum_getD (p : List (DensePoly ℚ)) (N : ℕ) (hN : p.length ≤ N) :
    DensePoly.toPoly p = ∑ k ∈ Finset.range N,
      Polynomial.C (toPoly (p.getD k [])) * Polynomial.X ^ k := by
  induction p generalizing N with
  | nil =>
    simp only [DensePoly.toPolyG_nil, List.getD_nil, toPolyG_nil, map_zero, zero_mul, Finset.sum_const_zero]
  | cons c cs ih =>
    cases N with
    | zero => simp at hN
    | succ M =>
      rw [DensePoly.toPolyG_cons_dense, Finset.sum_range_succ', ih M (by simpa using hN), Finset.mul_sum]
      simp only [List.getD_cons_succ, pow_succ, List.getD_cons_zero, pow_zero, mul_one]
      rw [add_comm]
      refine congrArg (fun q : Polynomial (Polynomial ℚ) =>
        q + Polynomial.C (toPoly c)) ?_
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
/-- `toPolyG_map_cmulG`: `DensePoly.toPoly (p.map (cmul s)) = C(toPoly s) · DensePoly.toPoly p`. -/
theorem toPolyG_map_cmulG (s : DensePoly ℚ) (p : List (DensePoly ℚ)) :
    DensePoly.toPoly (p.map (cmul s)) = Polynomial.C (toPoly s) * DensePoly.toPoly p := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_cons_dense, ih]
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
/-- `toPolyG_mulT`: `DensePoly.toPoly (mulT p q) = DensePoly.toPoly p · DensePoly.toPoly q`, where `mulT` is the Cauchy-product
`(mulT p q)_k = Σ_{i≤k} p_i·q_{k−i}`. -/
theorem toPolyG_mulT (p q : List (DensePoly ℚ)) :
    DensePoly.toPoly ((List.range (p.length + q.length)).map (fun k =>
        (List.range (k + 1)).foldl (fun acc i =>
          cadd acc (cmul (p.getD i []) (q.getD (k - i) []))) []))
      = DensePoly.toPoly p * DensePoly.toPoly q := by
  apply Polynomial.ext
  intro k
  rw [DensePoly.toPolyG_coeff_dense, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  by_cases hk : k < p.length + q.length
  · rw [getD_range_map _ _ _ hk, toPolyG_foldl_caddG, toPolyG_nil, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    simp only [denote, DensePoly.toPolyG_coeff_dense]
  · rw [getD_out _ _ (by rw [List.length_map, List.length_range]; omega), toPolyG_nil]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [DensePoly.toPolyG_coeff_dense, DensePoly.toPolyG_coeff_dense]
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
/-- `toPolyG_dpdt`: `DensePoly.toPoly dpdt = D_t (DensePoly.toPoly p)` (`Polynomial.derivative`) for `dpdt` the formal
`dp/dt` list. -/
theorem toPolyG_dpdt (p : List (DensePoly ℚ)) :
    DensePoly.toPoly ((p.drop 1).zipIdx.map (fun x => cscale ((x.2 : ℚ) + 1) x.1))
      = Polynomial.derivative (DensePoly.toPoly p) := by
  apply Polynomial.ext
  intro k
  rw [DensePoly.toPolyG_coeff_dense, tanDeriv_dpdt_getD]
  simp only [denote]
  rw [Polynomial.coeff_derivative, DensePoly.toPolyG_coeff_dense]
  simp only [CFieldSpec.toK, id_eq]
  rw [map_add, map_one, Polynomial.C_eq_natCast]
  ring

open DensePoly in
/-- `toPolyG_mulDt`: `DensePoly.toPoly mulDt = (X²+1)·DensePoly.toPoly dpdt` for `mulDt` the `(t²+1)·dpdt` list. -/
theorem toPolyG_mulDt (dpdt : List (DensePoly ℚ)) :
    DensePoly.toPoly ((List.range (dpdt.length + 2)).map (fun k =>
        cadd (if k ≥ 2 then dpdt.getD (k - 2) [] else []) (dpdt.getD k [])))
      = (Polynomial.X ^ 2 + 1) * DensePoly.toPoly dpdt := by
  apply Polynomial.ext
  intro k
  rw [DensePoly.toPolyG_coeff_dense, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
  by_cases hk : k < dpdt.length + 2
  · rw [getD_range_map _ _ _ hk]
    simp only [denote]
    rw [DensePoly.toPolyG_coeff_dense, apply_ite toPoly, toPolyG_nil]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, DensePoly.toPolyG_coeff_dense]
    · rw [if_neg h2, DensePoly.toPolyG_coeff_dense]
  · have hcoeffk : (DensePoly.toPoly dpdt).coeff k = 0 := by
      rw [DensePoly.toPolyG_coeff_dense, getD_out _ _ (by omega), toPolyG_nil]
    rw [getD_out _ _ (by rw [List.length_map, List.length_range]; omega), toPolyG_nil, hcoeffk]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, DensePoly.toPolyG_coeff_dense, getD_out _ _ (by omega), toPolyG_nil, add_zero]
    · rw [if_neg h2, add_zero]

open DensePoly in
/-- `toPolyG_tanDeriv`: the tangent derivation is bivariate `D = ∂/∂x + (t²+1)·∂/∂t`,
`DensePoly.toPoly (tanDeriv p) = DensePoly.toPoly (p.map cderiv) + (X²+1)·D_t(DensePoly.toPoly p)` over `ℚ[x][t]`. -/
theorem toPolyG_tanDeriv (p : List (DensePoly ℚ)) :
    DensePoly.toPoly (tanDeriv p)
      = DensePoly.toPoly (p.map cderiv)
        + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (DensePoly.toPoly p) := by
  show DensePoly.toPoly (DensePoly.cadd (p.map cderiv)
      ((List.range (((p.drop 1).zipIdx.map (fun x => cscale ((x.2 : ℚ) + 1) x.1)).length + 2)).map
        (fun k => cadd
          (if k ≥ 2 then ((p.drop 1).zipIdx.map (fun x => cscale ((x.2 : ℚ) + 1) x.1)).getD (k - 2) []
            else [])
          (((p.drop 1).zipIdx.map (fun x => cscale ((x.2 : ℚ) + 1) x.1)).getD k [])))) = _
  rw [DensePoly.toPolyG_caddG, toPolyG_mulDt, toPolyG_dpdt]

/-! ## Tangent cleared checks -/

/-- `cancelTanC1 = −t²+2t−8x²+1` as a `t`-polynomial (`t⁰ ↦ 1−8x²`, `t¹ ↦ 2`, `t² ↦ −1`). -/
def cancelTanC1 : List (DensePoly ℚ) := [[1, 0, -8], [2], [-1]]
/-- `cancelTanC2 = 2−4x` as a `t`-polynomial (constant in `t`). -/
def cancelTanC2 : List (DensePoly ℚ) := [[2, -4]]

/-- `cancelTanClearedCheck b0 b2 c1 c2 q1 q2`: `true` iff `(q₁, q₂)` solves the tangent `t`-polynomial
system `(Dq₁; Dq₂) + [[b₀−2t, −b₂],[b₂, b₀−2t]](q₁; q₂) = (c₁; c₂)` (`a = −1`, `n = 2`, `D = tanDeriv`),
checked by the generic nested `DensePoly.cisZero` test. -/
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
  DensePoly.cisZero r1 && DensePoly.cisZero r2

open DensePoly in
/-- `toPolyG_twoT`: `DensePoly.toPoly [[],[2]] = C(C 2)·X` (the diagonal `2t` as a `ℚ[x][t]` polynomial). -/
theorem toPolyG_twoT :
    DensePoly.toPoly ([[], [2]] : List (DensePoly ℚ)) = Polynomial.C (Polynomial.C 2) * Polynomial.X := by
  show DensePoly.toPoly ([[], [2]] : List (DensePoly ℚ)) = _
  rw [DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_nil]
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
    (DensePoly.toPoly (q1.map cderiv) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (DensePoly.toPoly q1))
        + (Polynomial.C (toPoly b0) * DensePoly.toPoly q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * DensePoly.toPoly q1)
        + Polynomial.C (toPoly (cscale (-1) b2)) * DensePoly.toPoly q2
      = DensePoly.toPoly c1 ∧
      (DensePoly.toPoly (q2.map cderiv) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (DensePoly.toPoly q2))
        + Polynomial.C (toPoly b2) * DensePoly.toPoly q1
        + (Polynomial.C (toPoly b0) * DensePoly.toPoly q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * DensePoly.toPoly q2)
      = DensePoly.toPoly c2 := by
  rw [cancelTanClearedCheck, Bool.and_eq_true] at hcheck
  obtain ⟨h1, h2⟩ := hcheck
  have e1 := (DensePoly.cisZeroG_iff _).mp h1
  have e2 := (DensePoly.cisZeroG_iff _).mp h2
  simp only [DensePoly.toPolyG_csubG, DensePoly.toPolyG_caddG, toPolyG_tanDeriv, toPolyG_map_cmulG, toPolyG_mulT,
    toPolyG_twoT, sub_eq_zero] at e1 e2
  exact ⟨by linear_combination e1, by linear_combination e2⟩

/-- `cCoupledDECancelTan_sound_of_check`: if `cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2)`
and the returned pair passes `cancelTanClearedCheck`, then `(q₁, q₂)` solves the tangent coupled
`t`-polynomial system at the `ℚ[x][t]` level (composition with `cancelTanClearedCheck_sound`). -/
theorem cCoupledDECancelTan_sound_of_check [CLinearSolve ℚ]
    (dbound : ℕ) (b0 b2 : DensePoly ℚ)
    (c1 c2 q1 q2 : List (DensePoly ℚ)) (n : ℕ)
    (_hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
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

end DeepWiki.SymbolicIntegration
