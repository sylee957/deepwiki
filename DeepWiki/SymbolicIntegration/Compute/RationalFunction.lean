import DeepWiki.SymbolicIntegration.Compute.Hermite
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative

/-! # Computable rational functions ℚ(x)
Completes `QFun = CPoly × CPoly` into a computable field ℚ(x): the field operations, the
lowest-terms reduction `qnorm`, the `d/dx` derivation `qderiv`, and decidable equality `qeq`, each
proven through the field homomorphism `toQFun : QFun → RatFunc ℚ` to realize its `RatFunc ℚ`
counterpart. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `am`-abbreviation and the basic `toQFun` reading
`am = algebraMap ℚ[X] (RatFunc ℚ)` is the field embedding of polynomials, so
`toQFun (a, b) = am (toPoly a) / am (toPoly b)`. -/

/-- `am (toPoly p) ≠ 0` whenever `toPoly p ≠ 0`. -/
theorem am_toPoly_ne_zero {p : CPoly} (hp : toPoly p ≠ 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hp

/-- `cisZero p = true ↔ toPoly p = 0`: the `CPoly` zero test agrees with vanishing in `ℚ[X]`. -/
theorem cisZero_iff_toPoly_eq_zero (p : CPoly) : cisZero p = true ↔ toPoly p = 0 := by
  rw [cisZero, beq_iff_eq, cnorm_eq_nil_iff]

/-! ### Computable field operations on `QFun` -/

/-- One rational function `1/1`. -/
def qone : QFun := ([1], [1])

/-- Negation of a rational function `−(a/b) = (−a)/b`. -/
def qneg (x : QFun) : QFun := (cneg x.1, x.2)

/-- Subtraction of rational functions `a/b − c/d = (a·d − c·b)/(b·d)`. -/
def qsub (x y : QFun) : QFun := qadd x (qneg y)

/-- Multiplication of rational functions `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def qmul (x y : QFun) : QFun := (cmul x.1 y.1, cmul x.2 y.2)

/-- Inverse of a rational function `(a/b)⁻¹ = b/a`; the zero fraction inverts to `qzero` (`0⁻¹ = 0`). -/
def qinv (x : QFun) : QFun := if cisZero x.1 then qzero else (x.2, x.1)

/-- Division of rational functions `(a/b)/(c/d) = (a·d)/(b·c)`. -/
def qdiv (x y : QFun) : QFun := qmul x (qinv y)

/-- Power of a rational function `(a/b)^n` by `ℕ`-recursion. -/
def qpow (x : QFun) : ℕ → QFun
  | 0 => qone
  | n + 1 => qmul x (qpow x n)

/-- Derivative `d/dx` of a rational function `D(a/b) = (a'·b − a·b')/b²` (quotient rule). -/
def qderiv (x : QFun) : QFun :=
  let (a, b) := x
  (csub (cmul (cderiv a) b) (cmul a (cderiv b)), cmul b b)

/-- Decidable equality of rational functions by cross-multiplication: `true` iff
`a₁·b₂ − a₂·b₁ = 0`. -/
def qeq (x y : QFun) : Bool :=
  cisZero (csub (cmul x.1 y.2) (cmul y.1 x.2))

/-- Lowest-terms reduction `qnorm fuel (a, b) = (a/q, b/q)` (`q = gcd(a, b)`) scaled so the
denominator is monic; the zero fraction stays `qzero`. -/
def qnorm (fuel : ℕ) (x : QFun) : QFun :=
  let (a, b) := x
  if cisZero a then qzero
  else
    let q := (cgcdExt fuel a b).1
    let a' := cdiv fuel a q
    let b' := cdiv fuel b q
    let s := (clead b')⁻¹
    (cscale s a', cscale s b')

/-! ### Field-homomorphism lemmas
Each computable operation realizes the corresponding `RatFunc ℚ` field operation through `toQFun`. -/

/-- `toQFun qone = 1` in `RatFunc ℚ`. -/
theorem toQFun_qone : toQFun qone = 1 := by
  simp [toQFun, qone, toPoly_cons, toPoly_nil]

/-- `toQFun (qneg x) = -toQFun x` in `RatFunc ℚ`. -/
theorem toQFun_qneg (x : QFun) : toQFun (qneg x) = -toQFun x := by
  obtain ⟨a, b⟩ := x
  simp only [toQFun, qneg, toPoly_cneg, map_neg, neg_div]

/-- `toQFun (qmul x y) = toQFun x * toQFun y` in `RatFunc ℚ`. -/
theorem toQFun_qmul (x y : QFun) : toQFun (qmul x y) = toQFun x * toQFun y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [toQFun, qmul, toPoly_cmul, map_mul]
  rw [div_mul_div_comm]

/-- `toQFun (qsub x y) = toQFun x - toQFun y` in `RatFunc ℚ` (for nonzero denominators). -/
theorem toQFun_qsub (x y : QFun) (hb : toPoly x.2 ≠ 0) (hd : toPoly y.2 ≠ 0) :
    toQFun (qsub x y) = toQFun x - toQFun y := by
  have hd' : toPoly (qneg y).2 ≠ 0 := hd
  rw [qsub, toQFun_qadd x (qneg y) hb hd', toQFun_qneg, sub_eq_add_neg]

/-- `toQFun (qinv x) = (toQFun x)⁻¹` in `RatFunc ℚ` (including `0⁻¹ = 0`). -/
theorem toQFun_qinv (x : QFun) : toQFun (qinv x) = (toQFun x)⁻¹ := by
  obtain ⟨a, b⟩ := x
  rw [qinv]
  by_cases ha : cisZero (a, b).1 = true
  · -- numerator is zero: `toQFun (0/b) = 0`, and `0⁻¹ = 0`.
    have ha0 : toPoly a = 0 := (cisZero_iff_toPoly_eq_zero a).mp ha
    simp only [ha, if_true]
    rw [toQFun_qzero, toQFun, ha0, map_zero, zero_div, inv_zero]
  · -- numerator nonzero: `qinv (a,b) = (b,a)`, `am(b)/am(a) = (am(a)/am(b))⁻¹`.
    rw [if_neg ha, toQFun, toQFun, inv_div]

/-- `toQFun (qdiv x y) = toQFun x / toQFun y` in `RatFunc ℚ`. -/
theorem toQFun_qdiv (x y : QFun) : toQFun (qdiv x y) = toQFun x / toQFun y := by
  rw [qdiv, toQFun_qmul, toQFun_qinv, div_eq_mul_inv]

/-- `toQFun (qpow x n) = (toQFun x) ^ n` in `RatFunc ℚ`. -/
theorem toQFun_qpow (x : QFun) (n : ℕ) : toQFun (qpow x n) = (toQFun x) ^ n := by
  induction n with
  | zero => rw [qpow, toQFun_qone, pow_zero]
  | succ n ih => rw [qpow, toQFun_qmul, ih, pow_succ, mul_comm]

open scoped Differential in
/-- `toQFun (qderiv x) = (toQFun x)′` in `RatFunc ℚ` (the `ratFuncDeriv` derivation), for nonzero
denominator. -/
theorem toQFun_qderiv (x : QFun) (hb : toPoly x.2 ≠ 0) : toQFun (qderiv x) = (toQFun x)′ := by
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
  -- compute `toQFun (qderiv (a,b))`: numerator `cderiv a · b − a · cderiv b`, denom `b · b`.
  simp only [toQFun, qderiv, toPoly_csub, toPoly_cmul, toPoly_cderiv, map_sub, map_mul]
  rw [hderiv, pow_two]
  ring

/-- `qeq x y = true ↔ toQFun x = toQFun y` in `RatFunc ℚ` (for nonzero denominators). -/
theorem qeq_iff (x y : QFun) (hb : toPoly x.2 ≠ 0) (hd : toPoly y.2 ≠ 0) :
    qeq x y = true ↔ toQFun x = toQFun y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hbm : am (toPoly b) ≠ 0 := am_toPoly_ne_zero hb
  have hdm : am (toPoly d) ≠ 0 := am_toPoly_ne_zero hd
  -- LHS: the cross-multiplication zero test in `ℚ[X]`.
  rw [qeq, cisZero_iff_toPoly_eq_zero, toPoly_csub, toPoly_cmul, toPoly_cmul, sub_eq_zero]
  -- RHS: the field equality, cleared to the cross-multiplication.
  rw [toQFun, toQFun, div_eq_div_iff hbm hdm]
  -- bridge through `am` injectivity (`map_mul` + injectivity).
  rw [← map_mul, ← map_mul]
  exact ⟨fun h => by rw [h], fun h => RatFunc.algebraMap_injective ℚ h⟩

/-- `am (C s) ≠ 0` for `s ≠ 0` (the constant `C s` embeds to a nonzero field element). -/
theorem am_C_ne_zero {s : ℚ} (hs : s ≠ 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C s) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr (Polynomial.C_ne_zero.mpr hs)

/-- Scaling numerator and denominator by a nonzero constant preserves the value:
`toQFun (cscale s a, cscale s b) = toQFun (a, b)` for `s ≠ 0`. -/
theorem toQFun_cscale_cscale (s : ℚ) (hs : s ≠ 0) (a b : CPoly) :
    toQFun (cscale s a, cscale s b) = toQFun (a, b) := by
  simp only [toQFun, toPoly_cscale, map_mul]
  rw [mul_div_mul_left _ _ (am_C_ne_zero hs)]

/-- Dividing numerator and denominator by an exact common divisor `q` preserves the value:
`toQFun (cdiv fuel a q, cdiv fuel b q) = toQFun (a, b)`. -/
theorem toQFun_cdiv_cdiv (fuel : ℕ) (a b q : CPoly) (hq : cnorm q ≠ [])
    (hra : toPoly (cmod fuel a q) = 0) (hrb : toPoly (cmod fuel b q) = 0) :
    toQFun (cdiv fuel a q, cdiv fuel b q) = toQFun (a, b) := by
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hqm : am (toPoly q) ≠ 0 := am_toPoly_ne_zero hq0
  -- exact divisions: `toPoly a = toPoly (cdiv a q)·toPoly q`, same for `b`.
  have ha := toPoly_cdiv_of_cmod_zero fuel a q hq hra
  have hbe := toPoly_cdiv_of_cmod_zero fuel b q hq hrb
  simp only [toQFun]
  rw [ha, hbe, map_mul, map_mul, mul_div_mul_right _ _ hqm]

/-- `qnorm` preserves the value: `toQFun (qnorm fuel x) = toQFun x` in `RatFunc ℚ`. -/
theorem toQFun_qnorm (fuel : ℕ) (x : QFun) (hb : toPoly x.2 ≠ 0)
    (hq : cnorm (cgcdExt fuel x.1 x.2).1 ≠ [])
    (hra : toPoly (cmod fuel x.1 (cgcdExt fuel x.1 x.2).1) = 0)
    (hrb : toPoly (cmod fuel x.2 (cgcdExt fuel x.1 x.2).1) = 0)
    (hbq : cnorm (cdiv fuel x.2 (cgcdExt fuel x.1 x.2).1) ≠ []) :
    toQFun (qnorm fuel x) = toQFun x := by
  obtain ⟨a, b⟩ := x
  simp only at hb hq hra hrb hbq
  rw [qnorm]
  by_cases ha : cisZero a = true
  · -- numerator zero: `qnorm = qzero`, and `toQFun (0/b) = 0 = toQFun qzero`.
    have ha0 : toPoly a = 0 := (cisZero_iff_toPoly_eq_zero a).mp ha
    simp only [ha, if_true]
    rw [toQFun_qzero, toQFun, ha0, map_zero, zero_div]
  · -- general case: divide by gcd, then scale by `(clead (b/q))⁻¹`.
    rw [if_neg ha]
    have hbq0 : toPoly (cdiv fuel b (cgcdExt fuel a b).1) ≠ 0 :=
      fun h => hbq ((cnorm_eq_nil_iff _).mpr h)
    have hs : (clead (cdiv fuel b (cgcdExt fuel a b).1))⁻¹ ≠ 0 :=
      inv_ne_zero (clead_ne_zero hbq)
    rw [toQFun_cscale_cscale _ hs, toQFun_cdiv_cdiv fuel a b _ hq hra hrb]

end DeepWiki.SymbolicIntegration.Compute
