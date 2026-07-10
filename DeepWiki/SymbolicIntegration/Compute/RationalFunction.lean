import DeepWiki.Algebra.ListSums
import DeepWiki.SymbolicIntegration.Compute.RationalFunction.Operations

/-! # Computable rational functions ℚ(x)
Completes `QFun = DensePoly ℚ × DensePoly ℚ` into a computable field ℚ(x): the field operations, the
lowest-terms reduction `qnorm`, the `d/dx` derivation `QFun.qderiv`, and decidable equality `QFun.qeq`, each
proven through the field homomorphism `toQFun : QFun → RatFunc ℚ` to realize its `RatFunc ℚ`
counterpart. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `am`-abbreviation and the basic `toQFun` reading
`am = algebraMap ℚ[X] (RatFunc ℚ)` is the field embedding of polynomials, so
`toQFun (a, b) = am (toPoly a) / am (toPoly b)`. -/

/-- `am (toPoly p) ≠ 0` whenever `toPoly p ≠ 0`. -/
theorem am_toPoly_ne_zero {p : DensePoly ℚ} (hp : toPoly p ≠ 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hp

/-- Exact fuel-free computable division becomes division in `RatFunc ℚ`. -/
theorem am_cdivWf_of_cmodWf_zero (p q : DensePoly ℚ) (hq : cnorm q ≠ [])
    (hrem : toPoly (DensePoly.cmodWf p q) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly p) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly q)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly (DensePoly.cdivWf p q)) := by
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hqm : algebraMap ℚ[X] (RatFunc ℚ) (toPoly q) ≠ 0 := am_toPoly_ne_zero hq0
  have hrem' : DensePoly.toPoly (DensePoly.cmodWf p q) = 0 := by
    simpa only [toPoly_eq_dense] using hrem
  have hdiv' := DensePoly.toPolyG_cmodWf p q hq
  rw [hrem', add_zero] at hdiv'
  have hdiv : toPoly p = toPoly (DensePoly.cdivWf p q) * toPoly q := by
    simpa only [toPoly_eq_dense] using hdiv'
  rw [hdiv, map_mul, mul_div_assoc,
    div_self hqm, mul_one]

/-- Exact fuel-free computable division gives a multiplicative factorization in `RatFunc ℚ`. -/
theorem am_eq_cdivWf_mul_of_cmodWf_zero (p q : DensePoly ℚ) (hq : cnorm q ≠ [])
    (hrem : toPoly (DensePoly.cmodWf p q) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly p)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPoly (DensePoly.cdivWf p q))
        * algebraMap ℚ[X] (RatFunc ℚ) (toPoly q) := by
  have hrem' : DensePoly.toPoly (DensePoly.cmodWf p q) = 0 := by
    simpa only [toPoly_eq_dense] using hrem
  have hdiv' := DensePoly.toPolyG_cmodWf p q hq
  rw [hrem', add_zero] at hdiv'
  have hdiv : toPoly p = toPoly (DensePoly.cdivWf p q) * toPoly q := by
    simpa only [toPoly_eq_dense] using hdiv'
  rw [← map_mul, ← hdiv]

/-- `cisZero p = true ↔ toPoly p = 0`: the `DensePoly ℚ` zero test agrees with vanishing in `ℚ[X]`. -/
theorem cisZero_iff_toPoly_eq_zero (p : DensePoly ℚ) : cisZero p = true ↔ toPoly p = 0 := by
  simpa [cisZero] using cnorm_eq_nil_iff p

/-! ### Field-homomorphism lemmas
Each computable operation realizes the corresponding `RatFunc ℚ` field operation through `toQFun`. -/

/-- `toQFun QFun.qone = 1` in `RatFunc ℚ`. -/
theorem toQFun_qone : toQFun QFun.qone = 1 := by
  simp only [toQFun, QFun.qone, toPoly_eq_dense, DensePoly.toPolyG_one_singleton,
    map_one, div_one]

/-- `toQFun (QFun.qneg x) = -toQFun x` in `RatFunc ℚ`. -/
theorem toQFun_qneg (x : QFun ℚ) : toQFun (QFun.qneg x) = -toQFun x := by
  obtain ⟨a, b⟩ := x
  simp only [toQFun, QFun.qneg, toPoly_eq_dense, DensePoly.toPolyG_cnegG, map_neg, neg_div]

/-- `toQFun (QFun.qmul x y) = toQFun x * toQFun y` in `RatFunc ℚ`. -/
theorem toQFun_qmul (x y : QFun ℚ) : toQFun (QFun.qmul x y) = toQFun x * toQFun y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [toQFun, QFun.qmul, toPoly_eq_dense, DensePoly.toPolyG_cmulG, map_mul]
  rw [div_mul_div_comm]

/-- `toQFun (QFun.qsub x y) = toQFun x - toQFun y` in `RatFunc ℚ` (for nonzero denominators). -/
theorem toQFun_qsub (x y : QFun ℚ) (hb : toPoly x.2 ≠ 0) (hd : toPoly y.2 ≠ 0) :
    toQFun (QFun.qsub x y) = toQFun x - toQFun y := by
  have hd' : toPoly (QFun.qneg y).2 ≠ 0 := hd
  rw [QFun.qsub, toQFun_qadd x (QFun.qneg y) hb hd', toQFun_qneg, sub_eq_add_neg]

/-- `toQFun (QFun.qinv x) = (toQFun x)⁻¹` in `RatFunc ℚ` (including `0⁻¹ = 0`). -/
theorem toQFun_qinv (x : QFun ℚ) : toQFun (QFun.qinv x) = (toQFun x)⁻¹ := by
  obtain ⟨a, b⟩ := x
  rw [QFun.qinv]
  by_cases ha : cisZero (a, b).1 = true
  · -- numerator is zero: `toQFun (0/b) = 0`, and `0⁻¹ = 0`.
    have ha0 : toPoly a = 0 := (cisZero_iff_toPoly_eq_zero a).mp ha
    simp only [ha, if_true]
    rw [toQFun_qzero, toQFun, ha0, map_zero, zero_div, inv_zero]
  · -- numerator nonzero: `QFun.qinv (a,b) = (b,a)`, `am(b)/am(a) = (am(a)/am(b))⁻¹`.
    rw [if_neg ha, toQFun, toQFun, inv_div]

/-- `toQFun (QFun.qdiv x y) = toQFun x / toQFun y` in `RatFunc ℚ`. -/
theorem toQFun_qdiv (x y : QFun ℚ) : toQFun (QFun.qdiv x y) = toQFun x / toQFun y := by
  rw [QFun.qdiv, toQFun_qmul, toQFun_qinv, div_eq_mul_inv]

/-- `toQFun (QFun.qpow x n) = (toQFun x) ^ n` in `RatFunc ℚ`. -/
theorem toQFun_qpow (x : QFun ℚ) (n : ℕ) : toQFun (QFun.qpow x n) = (toQFun x) ^ n := by
  induction n with
  | zero => rw [QFun.qpow, toQFun_qone, pow_zero]
  | succ n ih => rw [QFun.qpow, toQFun_qmul, ih, pow_succ, mul_comm]

open scoped Differential in
/-- `toQFun (QFun.qderiv x) = (toQFun x)′` in `RatFunc ℚ` (the `ratFuncDeriv` derivation), for nonzero
denominator. -/
theorem toQFun_qderiv (x : QFun ℚ) (hb : toPoly x.2 ≠ 0) : toQFun (QFun.qderiv x) = (toQFun x)′ := by
  obtain ⟨a, b⟩ := x
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hbm : am (toPoly b) ≠ 0 := am_toPoly_ne_zero hb
  -- `am`-of-derivative rewrites.
  have hda : (am (toPoly a))′ = am (derivative (toPoly a)) := ratFuncDeriv_algebraMap (toPoly a)
  have hdb : (am (toPoly b))′ = am (derivative (toPoly b)) := ratFuncDeriv_algebraMap (toPoly b)
  -- the quotient rule for `(am a / am b)′`.
  have hderiv : (am (toPoly a) / am (toPoly b))′
      = (am (toPoly b) * am (derivative (toPoly a))
          - am (toPoly a) * am (derivative (toPoly b))) / (am (toPoly b) ^ 2) := by
    rw [deriv_div, hda, hdb]
  simp only [toPoly_eq_dense] at hderiv
  -- compute `toQFun (QFun.qderiv (a,b))`: numerator `cderiv a · b − a · cderiv b`, denom `b · b`.
  simp only [toQFun, QFun.qderiv, toPoly_eq_dense, DensePoly.toPolyG_csubG,
    DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cderivG, map_sub, map_mul]
  rw [hderiv, pow_two]
  ring

open scoped Differential in
/-- The `QFun.qadd`-fold derivative is the sum of the increment derivatives. -/
theorem deriv_toQFun_foldl_qadd (gs : List (QFun ℚ)) (hgs : ∀ g ∈ gs, toPoly g.2 ≠ 0) :
    (toQFun (gs.foldl QFun.qadd QFun.qzero))′ = (gs.map (fun g => (toQFun g)′)).sum := by
  rw [toQFun_foldl_qadd gs QFun.qzero
    (by simpa [QFun.qzero] using
      (DensePoly.toPolyG_one_singleton_ne_zero (α := ℚ))) hgs, toQFun_qzero, zero_add]
  rw [show ((gs.map toQFun).sum)′ = Differential.deriv (R := RatFunc ℚ) (gs.map toQFun).sum from rfl,
    map_list_sum (Differential.deriv (R := RatFunc ℚ)) (gs.map toQFun), List.map_map]
  rfl

open scoped Differential in
/-- If every increment satisfies `(toQFun gⱼ)′ = T - residⱼ`, the fold residual is `T - nT + ∑ residⱼ`. -/
theorem foldl_residual_eq (gs : List (QFun ℚ)) (hgs : ∀ g ∈ gs, toPoly g.2 ≠ 0)
    (T : RatFunc ℚ) (resid : QFun ℚ → RatFunc ℚ)
    (hstep : ∀ g ∈ gs, (toQFun g)′ = T - resid g) :
    T - (toQFun (gs.foldl QFun.qadd QFun.qzero))′
      = T - gs.length • T + (gs.map resid).sum := by
  rw [deriv_toQFun_foldl_qadd gs hgs, List.map_congr_left hstep, list_sum_map_const_sub]
  abel

/-- `QFun.qeq x y = true ↔ toQFun x = toQFun y` in `RatFunc ℚ` (for nonzero denominators). -/
theorem qeq_iff (x y : QFun ℚ) (hb : toPoly x.2 ≠ 0) (hd : toPoly y.2 ≠ 0) :
    QFun.qeq x y = true ↔ toQFun x = toQFun y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hbm : am (toPoly b) ≠ 0 := am_toPoly_ne_zero hb
  have hdm : am (toPoly d) ≠ 0 := am_toPoly_ne_zero hd
  -- LHS: the cross-multiplication zero test in `ℚ[X]`.
  rw [QFun.qeq, cisZero_iff_toPoly_eq_zero, toPoly_eq_dense, DensePoly.toPolyG_csubG,
    DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG, sub_eq_zero]
  -- RHS: the field equality, cleared to the cross-multiplication.
  rw [toQFun, toQFun, div_eq_div_iff hbm hdm]
  simp only [toPoly_eq_dense] at hbm hdm ⊢
  -- bridge through `am` injectivity (`map_mul` + injectivity).
  rw [← map_mul, ← map_mul]
  exact ⟨fun h => by rw [h], fun h => RatFunc.algebraMap_injective ℚ h⟩

/-- `am (C s) ≠ 0` for `s ≠ 0` (the constant `C s` embeds to a nonzero field element). -/
theorem am_C_ne_zero {s : ℚ} (hs : s ≠ 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C s) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr (Polynomial.C_ne_zero.mpr hs)

/-- Scaling numerator and denominator by a nonzero constant preserves the value:
`toQFun (cscale s a, cscale s b) = toQFun (a, b)` for `s ≠ 0`. -/
theorem toQFun_cscale_cscale (s : ℚ) (hs : s ≠ 0) (a b : DensePoly ℚ) :
    toQFun (cscale s a, cscale s b) = toQFun (a, b) := by
  simp only [toQFun, toPoly_eq_dense, DensePoly.toPolyG_cscaleG, toR_eq_toK,
    CFieldSpec.toK_rat, map_mul]
  rw [mul_div_mul_left _ _ (am_C_ne_zero hs)]

/-- Dividing numerator and denominator by an exact common divisor with `cdivWf` preserves the value. -/
theorem toQFun_cdivWf_cdivWf (a b q : DensePoly ℚ) (hq : cnorm q ≠ [])
    (hra : toPoly (DensePoly.cmodWf a q) = 0)
    (hrb : toPoly (DensePoly.cmodWf b q) = 0) :
    toQFun (DensePoly.cdivWf a q, DensePoly.cdivWf b q) = toQFun (a, b) := by
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hqm : am (toPoly q) ≠ 0 := am_toPoly_ne_zero hq0
  -- exact divisions: `toPoly a = toPoly (cdiv a q)·toPoly q`, same for `b`.
  have hra' : DensePoly.toPoly (DensePoly.cmodWf a q) = 0 := by
    simpa only [toPoly_eq_dense] using hra
  have hrb' : DensePoly.toPoly (DensePoly.cmodWf b q) = 0 := by
    simpa only [toPoly_eq_dense] using hrb
  have ha' := DensePoly.toPolyG_cmodWf a q hq
  have hbe' := DensePoly.toPolyG_cmodWf b q hq
  rw [hra', add_zero] at ha'
  rw [hrb', add_zero] at hbe'
  have ha : toPoly a = toPoly (DensePoly.cdivWf a q) * toPoly q := by
    simpa only [toPoly_eq_dense] using ha'
  have hbe : toPoly b = toPoly (DensePoly.cdivWf b q) * toPoly q := by
    simpa only [toPoly_eq_dense] using hbe'
  simp only [toQFun]
  rw [ha, hbe, map_mul, map_mul, mul_div_mul_right _ _ hqm]

/-- `qnorm` preserves the value: `toQFun (qnorm x) = toQFun x` in `RatFunc ℚ`. -/
theorem toQFun_qnorm (x : QFun ℚ) (hb : toPoly x.2 ≠ 0)
    (hq : cnorm (DensePoly.cgcdWf x.1 x.2).1 ≠ [])
    (hra : toPoly (DensePoly.cmodWf x.1 (DensePoly.cgcdWf x.1 x.2).1) = 0)
    (hrb : toPoly (DensePoly.cmodWf x.2 (DensePoly.cgcdWf x.1 x.2).1) = 0)
    (hbq : cnorm (DensePoly.cdivWf x.2 (DensePoly.cgcdWf x.1 x.2).1) ≠ []) :
    toQFun (qnorm x) = toQFun x := by
  obtain ⟨a, b⟩ := x
  simp only at hb hq hra hrb hbq
  rw [qnorm]
  by_cases ha : cisZero a = true
  · -- numerator zero: `qnorm = QFun.qzero`, and `toQFun (0/b) = 0 = toQFun QFun.qzero`.
    have ha0 : toPoly a = 0 := (cisZero_iff_toPoly_eq_zero a).mp ha
    simp only [ha, if_true]
    rw [toQFun_qzero, toQFun, ha0, map_zero, zero_div]
  · -- general case: divide by gcd, then scale by `(clead (b/q))⁻¹`.
    rw [if_neg ha]
    have hbq0 : toPoly (DensePoly.cdivWf b (DensePoly.cgcdWf a b).1) ≠ 0 :=
      fun h => hbq ((cnorm_eq_nil_iff _).mpr h)
    have hs : (clead (DensePoly.cdivWf b (DensePoly.cgcdWf a b).1))⁻¹ ≠ 0 :=
      inv_ne_zero (clead_ne_zero hbq)
    rw [toQFun_cscale_cscale _ hs, toQFun_cdivWf_cdivWf a b _ hq hra hrb]

end DeepWiki.SymbolicIntegration.Compute
