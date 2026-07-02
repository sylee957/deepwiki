import DeepWiki.SymbolicIntegration.Compute.Hermite
import DeepWiki.SymbolicIntegration.HermiteCorrectness

/-! # Computable rational functions ℚ(x) (the field layer)
The Hermite engine of `HermiteCompute` carries a started rational-function type `QFun = CPoly × CPoly`
(numerator, denominator) with addition `qadd` and the bridge `toQFun : QFun → RatFunc ℚ`. This file
completes `QFun` into a genuinely **computable field** ℚ(x): one (`qone`), negation/subtraction
(`qneg`/`qsub`), multiplication/inverse/division (`qmul`/`qinv`/`qdiv`), power (`qpow`), the
lowest-terms reduction `qnorm` (via `cgcdExt`, with monic denominator), the `d/dx` derivation
`qderiv`, and decidable equality `qeq` (cross-multiply). Each operation is proven — through the
`toQFun` bridge — to realize the corresponding `RatFunc ℚ` field operation, so `toQFun` is a field
homomorphism that intertwines the computable engine with Mathlib's noncomputable ℚ(x): `toQFun_qone`,
`toQFun_qneg`, `toQFun_qsub`, `toQFun_qmul`, `toQFun_qinv`, `toQFun_qdiv`, `toQFun_qpow`,
`toQFun_qnorm` (value-preserving), `toQFun_qderiv` (the `ratFuncDeriv` derivation), and `qeq_iff`
(decidable-equality correctness). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `am`-abbreviation and the basic `toQFun` reading

`am = algebraMap ℚ[X] (RatFunc ℚ)` is the field embedding of polynomials; `toQFun (a, b) =
am (toPoly a) / am (toPoly b)`. The injectivity of `am` turns nonzero-`CPoly` hypotheses into
nonzero-`RatFunc` ones. -/

/-- `am (toPoly p) ≠ 0` whenever `toPoly p ≠ 0` (the field embedding `algebraMap ℚ[X] (RatFunc ℚ)` is
injective). -/
theorem am_toPoly_ne_zero {p : CPoly} (hp : toPoly p ≠ 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hp

/-- **`cisZero` reads as `toPoly = 0`**: `cisZero p = true ↔ toPoly p = 0` (the zero test on `CPoly`
agrees with vanishing in `ℚ[X]`). -/
theorem cisZero_iff_toPoly_eq_zero (p : CPoly) : cisZero p = true ↔ toPoly p = 0 := by
  rw [cisZero, beq_iff_eq, cnorm_eq_nil_iff]

/-! ### Computable field operations on `QFun` -/

/-- **One rational function** `1/1`. -/
def qone : QFun := ([1], [1])

/-- **Negation of a rational function** `−(a/b) = (−a)/b`. -/
def qneg (x : QFun) : QFun := (cneg x.1, x.2)

/-- **Subtraction of rational functions** `a/b − c/d = (a·d − c·b)/(b·d)`. -/
def qsub (x y : QFun) : QFun := qadd x (qneg y)

/-- **Multiplication of rational functions** `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def qmul (x y : QFun) : QFun := (cmul x.1 y.1, cmul x.2 y.2)

/-- **Inverse of a rational function** `(a/b)⁻¹ = b/a`; the zero fraction inverts to `qzero`
(matching the `RatFunc ℚ` field convention `0⁻¹ = 0`). -/
def qinv (x : QFun) : QFun := if cisZero x.1 then qzero else (x.2, x.1)

/-- **Division of rational functions** `(a/b)/(c/d) = (a·d)/(b·c) = (a/b)·(c/d)⁻¹`. -/
def qdiv (x y : QFun) : QFun := qmul x (qinv y)

/-- **Power of a rational function** `(a/b)^n` by `ℕ`-recursion (`qone` at `0`). -/
def qpow (x : QFun) : ℕ → QFun
  | 0 => qone
  | n + 1 => qmul x (qpow x n)

/-- **Derivative `d/dx` of a rational function** `D(a/b) = (a'·b − a·b')/b²` (the quotient rule;
`Dx = 1`), via `cderiv`. -/
def qderiv (x : QFun) : QFun :=
  let (a, b) := x
  (csub (cmul (cderiv a) b) (cmul a (cderiv b)), cmul b b)

/-- **Decidable equality of rational functions** `a₁/b₁ = a₂/b₂`, by cross-multiplication:
`true` iff `a₁·b₂ − a₂·b₁ = 0` (for nonzero denominators). -/
def qeq (x y : QFun) : Bool :=
  cisZero (csub (cmul x.1 y.2) (cmul y.1 x.2))

/-- **Lowest-terms reduction** `qnorm fuel (a, b) = (a/q, b/q)` scaled so the denominator is monic,
where `q = gcd(a, b)` (`cgcdExt`): divide numerator and denominator by their gcd, then scale both by
`(lead of b/q)⁻¹` so the reduced denominator is `cmonic`. The zero fraction stays `qzero`. -/
def qnorm (fuel : ℕ) (x : QFun) : QFun :=
  let (a, b) := x
  if cisZero a then qzero
  else
    let q := (cgcdExt fuel a b).1
    let a' := cdiv fuel a q
    let b' := cdiv fuel b q
    let s := (clead b')⁻¹
    (cscale s a', cscale s b')

/-! ### Field-homomorphism lemmas: `qone`, `qneg`, `qsub`, `qmul`

Each computable operation realizes the corresponding `RatFunc ℚ` field operation through `toQFun`.
These hold *unconditionally* for `qone`/`qneg`/`qmul` (no denominator-nonzero side condition: the
numeric `RatFunc ℚ` operations are total and the `am`-of-`toPoly` images line up directly);
`qsub`/`qadd`-derived ones inherit the `qadd` side condition. -/

/-- **`qone` realizes `1`**: `toQFun qone = 1` in `RatFunc ℚ`. -/
theorem toQFun_qone : toQFun qone = 1 := by
  simp [toQFun, qone, toPoly_cons, toPoly_nil]

/-- **`qneg` realizes negation**: `toQFun (qneg x) = -toQFun x` in `RatFunc ℚ`. -/
theorem toQFun_qneg (x : QFun) : toQFun (qneg x) = -toQFun x := by
  obtain ⟨a, b⟩ := x
  simp only [toQFun, qneg, toPoly_cneg, map_neg, neg_div]

/-- **`qmul` realizes multiplication**: `toQFun (qmul x y) = toQFun x * toQFun y` in `RatFunc ℚ`. -/
theorem toQFun_qmul (x y : QFun) : toQFun (qmul x y) = toQFun x * toQFun y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [toQFun, qmul, toPoly_cmul, map_mul]
  rw [div_mul_div_comm]

/-- **`qsub` realizes subtraction** (for nonzero denominators): `toQFun (qsub x y) = toQFun x -
toQFun y` in `RatFunc ℚ`. -/
theorem toQFun_qsub (x y : QFun) (hb : toPoly x.2 ≠ 0) (hd : toPoly y.2 ≠ 0) :
    toQFun (qsub x y) = toQFun x - toQFun y := by
  have hd' : toPoly (qneg y).2 ≠ 0 := hd
  rw [qsub, toQFun_qadd x (qneg y) hb hd', toQFun_qneg, sub_eq_add_neg]

/-- **`qinv` realizes inversion**: `toQFun (qinv x) = (toQFun x)⁻¹` in `RatFunc ℚ` (including the
field convention `0⁻¹ = 0`: when the numerator is zero, both sides are `0`). -/
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

/-- **`qdiv` realizes division**: `toQFun (qdiv x y) = toQFun x / toQFun y` in `RatFunc ℚ`. -/
theorem toQFun_qdiv (x y : QFun) : toQFun (qdiv x y) = toQFun x / toQFun y := by
  rw [qdiv, toQFun_qmul, toQFun_qinv, div_eq_mul_inv]

/-- **`qpow` realizes the `ℕ`-power**: `toQFun (qpow x n) = (toQFun x) ^ n` in `RatFunc ℚ`. -/
theorem toQFun_qpow (x : QFun) (n : ℕ) : toQFun (qpow x n) = (toQFun x) ^ n := by
  induction n with
  | zero => rw [qpow, toQFun_qone, pow_zero]
  | succ n ih => rw [qpow, toQFun_qmul, ih, pow_succ, mul_comm]

open scoped Differential in
/-- **`qderiv` realizes the `d/dx` derivation**: `toQFun (qderiv x) = (toQFun x)′` in `RatFunc ℚ`
(the `ratFuncDeriv` derivation), provided the denominator is nonzero. The computable quotient rule
`(a/b)′ = (a'·b − a·b')/b²` realizes the field derivation exactly. -/
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

/-- **`qeq` decides rational-function equality**: `qeq x y = true ↔ toQFun x = toQFun y` in
`RatFunc ℚ` (for nonzero denominators). The cross-multiplication test `a₁·b₂ − a₂·b₁ = 0` is
equivalent to the field equality `a₁/b₁ = a₂/b₂` once the denominators are units. -/
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

/-- `am (C s) = algebraMap ℚ (RatFunc ℚ) s` is nonzero for `s ≠ 0` (the constant `C s` embeds to a
nonzero field element). -/
theorem am_C_ne_zero {s : ℚ} (hs : s ≠ 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C s) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr (Polynomial.C_ne_zero.mpr hs)

/-- **Scaling numerator and denominator by a nonzero constant preserves the value**:
`toQFun (cscale s a, cscale s b) = toQFun (a, b)` for `s ≠ 0` (the `C s` factors cancel in the
field `RatFunc ℚ`). -/
theorem toQFun_cscale_cscale (s : ℚ) (hs : s ≠ 0) (a b : CPoly) :
    toQFun (cscale s a, cscale s b) = toQFun (a, b) := by
  simp only [toQFun, toPoly_cscale, map_mul]
  rw [mul_div_mul_left _ _ (am_C_ne_zero hs)]

/-- **Dividing numerator and denominator by an exact common divisor preserves the value**: if `q`
divides both `a` and `b` exactly (the remainders `cmod fuel a q` and `cmod fuel b q` read to `0`) and
`q ≠ 0`, then `toQFun (cdiv fuel a q, cdiv fuel b q) = toQFun (a, b)`. -/
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

/-- **`qnorm` preserves the value**: `toQFun (qnorm fuel x) = toQFun x` in `RatFunc ℚ`. The
lowest-terms reduction divides numerator and denominator by their gcd (exact division, certificates
`hra`/`hrb`) and scales both by the same nonzero constant `(clead (b/q))⁻¹` to make the denominator
monic — neither changes the fraction's value. Hypotheses: `b ≠ 0`, the gcd `q ≠ 0`, the two
exact-division certificates, and the reduced denominator `b/q ≠ 0` (so the monic-scaling constant is
nonzero). -/
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
