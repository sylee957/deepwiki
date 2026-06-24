import DeepWiki.SymbolicIntegration.HermiteCompute
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
