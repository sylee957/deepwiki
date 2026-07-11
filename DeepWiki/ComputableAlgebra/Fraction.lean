import DeepWiki.ComputableAlgebra.FracRepr
import DeepWiki.ComputableAlgebra.PolyEngineLawful
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Representation-independent computable fraction fields

`CFrac F P` receives generic field operations and a lawful denotation into
`RatFunc (CFieldSpec.K α)`. Dense and sparse fraction carriers share this implementation. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-! #### The pure-`CField` domain class `CFieldDomain` -/

/-- Polynomial-domain facts for representation `P`: `1` and products of nonzero polynomials are nonzero. -/
class CFieldDomain (α : Type u) [CField α]
    (P : Type u → Type u) [CPoly P] [CPolyEngine P] where
  /-- The represented constant `1` is nonzero. -/
  nz_one : CPolyEngine.cisZero (CPoly.one : P α) = false
  /-- A product of represented nonzero polynomials is nonzero. -/
  nz_mul : ∀ {b d : P α}, CPolyEngine.cisZero b = false → CPolyEngine.cisZero d = false →
    CPolyEngine.cisZero (CPolyEngine.mul b d) = false

/-- Every `[CFieldSpec α]` level is a `CFieldDomain`, since `(CFieldSpec.K α)[X]` is an integral domain;
provides only `Prop` fields (erased at runtime). -/
noncomputable instance instCFieldDomainOfCFieldSpec {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] {α : Type u} [CField α] [CFieldSpec.{u,v} α] :
    CFieldDomain α P where
  nz_one := by
    rw [Bool.eq_false_iff]
    intro h
    have hz := (LawfulCPolyEngine.cisZero_iff (P := P) (CPoly.one : P α)).mp h
    rw [CPoly.toPoly_one] at hz
    exact one_ne_zero hz
  nz_mul := by
    intro b d hb hd
    rw [Bool.eq_false_iff]
    intro h
    have hprod := (LawfulCPolyEngine.cisZero_iff (P := P) (CPolyEngine.mul b d)).mp h
    rw [LawfulCPolyEngine.toPoly_mul] at hprod
    have hb' : CPoly.toPoly b ≠ 0 := fun hzero =>
      (Bool.eq_false_iff.mp hb) ((LawfulCPolyEngine.cisZero_iff (P := P) b).mpr hzero)
    have hd' : CPoly.toPoly d ≠ 0 := fun hzero =>
      (Bool.eq_false_iff.mp hd) ((LawfulCPolyEngine.cisZero_iff (P := P) d).mpr hzero)
    exact (mul_ne_zero hb' hd') hprod

namespace CFrac

variable {F : (α : Type u) → [CField α] → Type u}
variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CFrac F P]

/-- A computable fraction's stored denominator passes the polynomial nonzero test. -/
theorem cisZeroG_den {α : Type u} [CField α] (x : F α) :
    CPolyEngine.cisZero (den x) = false :=
  CFrac.den_nonzero x

/-- The product of two represented nonzero polynomials is nonzero (from `CFieldDomain`). -/
theorem cmulG_ne_zero_of {α : Type u} [CField α] [CFieldDomain α P] {b d : P α}
    (hb : CPolyEngine.cisZero b = false)
    (hd : CPolyEngine.cisZero d = false) :
    CPolyEngine.cisZero (CPolyEngine.mul b d) = false :=
  CFieldDomain.nz_mul hb hd

/-- Embed a computable polynomial as the fraction `p/1`. -/
def ofPoly {α : Type u} [CField α] [CFieldDomain α P] (p : P α) : F α :=
  ofFraction p CPoly.one CFieldDomain.nz_one

/-- Embed a coefficient as the constant fraction `a/1`. -/
def ofScalar {α : Type u} [CField α] [CFieldDomain α P] (a : α) : F α :=
  ofPoly (CPolyEngine.ofCoeffList [a])

/-- The numerator of the polynomial embedding is the original polynomial. -/
@[simp] theorem num_ofPoly {α : Type u} [CField α] [CFieldDomain α P] (p : P α) :
    num (ofPoly (F := F) p) = p := by simp [ofPoly]

/-- The denominator of the polynomial embedding is `1`. -/
@[simp] theorem den_ofPoly {α : Type u} [CField α] [CFieldDomain α P] (p : P α) :
    den (ofPoly (F := F) p) = CPoly.one := by simp [ofPoly]

/-- `add`: addition on `CFrac` (the product denominator `b·d` is nonzero). -/
def add {α : Type u} [CField α] [CFieldDomain α P] (x y : F α) : F α :=
  ofFraction
    (CPolyEngine.add (CPolyEngine.mul (num x) (den y))
      (CPolyEngine.mul (num y) (den x)))
    (CPolyEngine.mul (den x) (den y))
    (cmulG_ne_zero_of (cisZeroG_den x) (cisZeroG_den y))

/-- `mul`: multiplication on `CFrac` (the product denominator `b·d` is nonzero). -/
def mul {α : Type u} [CField α] [CFieldDomain α P] (x y : F α) : F α :=
  ofFraction (CPolyEngine.mul (num x) (num y))
    (CPolyEngine.mul (den x) (den y))
    (cmulG_ne_zero_of (cisZeroG_den x) (cisZeroG_den y))

/-- `neg`: negation on `CFrac` (denominator unchanged). -/
def neg {α : Type u} [CField α] (x : F α) : F α :=
  ofFraction (CPolyEngine.neg (num x)) (den x) (cisZeroG_den x)

/-- `inv`: inverse on `CFrac`. If the numerator's zero test holds, the result is `ofPoly []` (the
`0⁻¹ = 0` convention); otherwise swap numerator and denominator (the new denominator is the old
numerator, nonzero exactly by `¬ cisZero`). -/
def inv {α : Type u} [CField α] [CFieldDomain α P] (x : F α) : F α :=
  if h : CPolyEngine.cisZero (num x) then ofPoly CPoly.czero
  else ofFraction (den x) (num x) (Bool.not_eq_true _ ▸ h)

/-- `sub`: subtraction on `CFrac`, `x − y := x + (−y)`. -/
def sub {α : Type u} [CField α] [CFieldDomain α P] (x y : F α) : F α :=
  add x (neg y)

/-- Formal polynomial-variable derivative of a represented fraction by the quotient rule. -/
def deriv {α : Type u} [CField α] [CFieldDomain α P] (x : F α) : F α :=
  ofFraction
    (CPolyEngine.sub
      (CPolyEngine.mul (CPolyEngine.deriv (num x)) (den x))
      (CPolyEngine.mul (num x) (CPolyEngine.deriv (den x))))
    (CPolyEngine.mul (den x) (den x))
    (cmulG_ne_zero_of (cisZeroG_den x) (cisZeroG_den x))

/-- `isZero`: the zero test on `CFrac`, reading `cisZero` off the **numerator** (the denominator
is nonzero by membership, so `x = 0` iff its numerator vanishes). -/
def isZero {α : Type u} [CField α] (x : F α) : Bool := CPolyEngine.cisZero (num x)

/-- Boolean equality of represented fractions, computed by zero-testing their difference. -/
def eq {α : Type u} [CField α] [CFieldDomain α P] (x y : F α) : Bool :=
  isZero (sub x y)

/-- `CFrac.eq` is the zero test of the represented fraction difference. -/
theorem eq_eq_isZero_sub {α : Type u} [CField α] [CFieldDomain α P] (x y : F α) :
    eq x y = isZero (sub x y) := rfl

/-- Evaluate a represented fraction at a coefficient-field point by evaluating its stored numerator
and denominator. -/
def eval {α : Type u} [CField α] (x : F α) (a : α) : α :=
  CField.div (CPolyEngine.eval (num x) a) (CPolyEngine.eval (den x) a)

/-- Fraction evaluation is the quotient of the selected polynomial evaluations of the stored pair. -/
theorem eval_eq_div {α : Type u} [CField α] (x : F α) (a : α) :
    eval x a = CField.div (CPolyEngine.eval (num x) a) (CPolyEngine.eval (den x) a) := rfl

end CFrac

/-! ### The generic computable field instance -/

/-- Every `CFrac F P` with polynomial-domain evidence is a computable field representation. -/
instance instCFieldCFrac {F : (α : Type u) → [CField α] → Type u}
    {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CFrac F P]
    {α : Type u} [CField α] [CFieldDomain α P] : CField (F α) where
  zero := CFrac.ofPoly (CPoly.czero : P α)
  one := CFrac.ofPoly (CPoly.one : P α)
  add := CFrac.add
  mul := CFrac.mul
  neg := CFrac.neg
  inv := CFrac.inv
  isZero := CFrac.isZero

/-! ### The bridge `toRatFunc` into `RatFunc (CFieldSpec.K α)` and its homomorphism laws -/

namespace CFrac

/-- `am = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))`, the polynomial-into-rational
embedding for the bridge. -/
noncomputable abbrev am (α : Type*) [CField α] [CFieldSpec α] :
    (CFieldSpec.K α)[X] →+* RatFunc (CFieldSpec.K α) :=
  algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))

variable {F : (α : Type u) → [CField α] → Type u}
variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CFrac F P]

/-- The rational-function denotation of a represented fraction, valid for every lawful polynomial
representation. -/
noncomputable def toRatFunc {α : Type u} [CField α] [CFieldSpec.{u,v} α] (x : F α) :
    RatFunc (CFieldSpec.K α) :=
  am α (CPoly.toPoly (num x)) / am α (CPoly.toPoly (den x))

/-- A represented fraction denotes the quotient of its polynomial numerator and denominator. -/
theorem toRatFunc_eq_div {α : Type u} [CField α] [CFieldSpec.{u,v} α] (x : F α) :
    toRatFunc x = am α (CPoly.toPoly (num x)) / am α (CPoly.toPoly (den x)) := rfl

/-- The polynomial embedding into `RatFunc` preserves nonzeroness. -/
theorem am_ne_zero {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    {p : (CFieldSpec.K α)[X]} (hp : p ≠ 0) : am α p ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mpr hp

/-- The stored denominator of a represented fraction has nonzero polynomial denotation. -/
theorem toPoly_den_ne_zero_generic [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (x : F α) :
    CPoly.toPoly (den x) ≠ 0 := by
  intro hzero
  have htrue : CPolyEngine.cisZero (den x) = true :=
    (LawfulCPolyEngine.cisZero_iff (P := P) (den x)).mpr hzero
  rw [CFrac.den_nonzero x] at htrue
  contradiction

/-- A constructed fraction denotes the supplied numerator divided by the supplied denominator. -/
@[denote] theorem toRatFunc_ofFraction {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (num den : P α) (h : CPolyEngine.cisZero den = false) :
    toRatFunc (ofFraction (F := F) num den h) =
      am α (CPoly.toPoly num) / am α (CPoly.toPoly den) := by
  rw [toRatFunc, num_ofFraction, den_ofFraction]

/-- The polynomial embedding denotes the natural rational-function embedding. -/
@[denote] theorem toRatFunc_ofPoly [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (p : P α) :
    toRatFunc (ofPoly (F := F) p) = am α (CPoly.toPoly p) := by
  rw [toRatFunc, num_ofPoly, den_ofPoly, CPoly.toPoly_one, map_one, div_one]

/-- Represented fraction addition realizes addition in `RatFunc`. -/
@[denote] theorem toRatFunc_add [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (x y : F α) :
    toRatFunc (add x y) = toRatFunc x + toRatFunc y := by
  rw [add, toRatFunc_ofFraction, toRatFunc_eq_div, toRatFunc_eq_div]
  simp only [LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_mul, map_add, map_mul]
  have hx : am α (CPoly.toPoly (den x)) ≠ 0 :=
    am_ne_zero (toPoly_den_ne_zero_generic x)
  have hy : am α (CPoly.toPoly (den y)) ≠ 0 :=
    am_ne_zero (toPoly_den_ne_zero_generic y)
  rw [div_add_div _ _ hx hy]
  ring

/-- Represented fraction multiplication realizes multiplication in `RatFunc`. -/
@[denote] theorem toRatFunc_mul [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (x y : F α) :
    toRatFunc (mul x y) = toRatFunc x * toRatFunc y := by
  rw [mul, toRatFunc_ofFraction, toRatFunc_eq_div, toRatFunc_eq_div]
  simp only [LawfulCPolyEngine.toPoly_mul, map_mul]
  rw [div_mul_div_comm]

/-- Represented fraction negation realizes negation in `RatFunc`. -/
@[denote] theorem toRatFunc_neg [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (x : F α) :
    toRatFunc (neg x) = -toRatFunc x := by
  rw [neg, toRatFunc_ofFraction, toRatFunc_eq_div]
  simp only [LawfulCPolyEngine.toPoly_neg, map_neg, neg_div]

/-- Represented fraction inversion realizes inversion in `RatFunc`. -/
@[denote] theorem toRatFunc_inv [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (x : F α) :
    toRatFunc (inv x) = (toRatFunc x)⁻¹ := by
  rw [inv]
  split
  next hzero =>
    have hnum : CPoly.toPoly (num x) = 0 :=
      (LawfulCPolyEngine.cisZero_iff (P := P) (num x)).mp hzero
    rw [toRatFunc_ofPoly, CPoly.toPoly_czero, map_zero, toRatFunc_eq_div, hnum, map_zero,
      zero_div, inv_zero]
  next _ =>
    rw [toRatFunc_ofFraction, toRatFunc_eq_div, inv_div]

/-- Represented fraction subtraction realizes subtraction in `RatFunc`. -/
@[denote] theorem toRatFunc_sub [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (x y : F α) :
    toRatFunc (sub x y) = toRatFunc x - toRatFunc y := by
  rw [sub, toRatFunc_add, toRatFunc_neg, sub_eq_add_neg]

/-- The represented numerator zero test agrees with vanishing in `RatFunc`. -/
@[denote] theorem isZero_iff_toRatFunc [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (x : F α) :
    isZero x = true ↔ toRatFunc x = 0 := by
  rw [isZero, LawfulCPolyEngine.cisZero_iff, toRatFunc_eq_div]
  have hden : am α (CPoly.toPoly (den x)) ≠ 0 :=
    am_ne_zero (toPoly_den_ne_zero_generic x)
  constructor
  · intro hzero
    rw [hzero, map_zero, zero_div]
  · intro hzero
    rw [div_eq_zero_iff] at hzero
    rcases hzero with hzero | hzero
    · exact (map_eq_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mp hzero
    · exact absurd hzero hden

/-- Represented-fraction Boolean equality agrees with equality of rational-function denotations. -/
@[denote] theorem eq_iff_toRatFunc [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (x y : F α) :
    eq x y = true ↔ toRatFunc x = toRatFunc y := by
  rw [eq, isZero_iff_toRatFunc, toRatFunc_sub, sub_eq_zero]

/-- The generic `CFieldSpec` induced by a lawful polynomial representation. -/
@[reducible] noncomputable def fieldSpec [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] : CFieldSpec (F α) where
  K := RatFunc (CFieldSpec.K α)
  toK := toRatFunc
  toK_zero := by
    change toRatFunc (ofPoly (F := F) (CPoly.czero : P α)) = 0
    rw [toRatFunc_ofPoly, CPoly.toPoly_czero, map_zero]
  toK_one := by
    change toRatFunc (ofPoly (F := F) (CPoly.one : P α)) = 1
    rw [toRatFunc_ofPoly, CPoly.toPoly_one, map_one]
  toK_add := toRatFunc_add
  toK_mul := toRatFunc_mul
  toK_neg := toRatFunc_neg
  toK_inv := toRatFunc_inv
  isZero_iff := isZero_iff_toRatFunc


end CFrac

/-- Every lawful represented fraction inherits the generic `RatFunc` field denotation. -/
@[reducible] noncomputable instance instCFieldSpecCFrac
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] [CFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] :
    CFieldSpec (F α) :=
  CFrac.fieldSpec (F := F) (P := P)

namespace CFrac

/-- The field bridge sends the polynomial embedding to the natural rational-function embedding. -/
@[denote] theorem toK_ofPoly
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] [CFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (p : P α) :
    CFieldSpec.toK (ofPoly (F := F) p) = am α (CPoly.toPoly p) := by
  change toRatFunc (ofPoly (F := F) p) = am α (CPoly.toPoly p)
  exact toRatFunc_ofPoly p

/-- The field bridge sends a packaged fraction to the quotient of its polynomial denotations. -/
@[denote] theorem toK_ofFraction
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] [CFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (num den : P α) (h : CPolyEngine.cisZero den = false) :
    CFieldSpec.toK (ofFraction (F := F) num den h) =
      am α (CPoly.toPoly num) / am α (CPoly.toPoly den) := by
  change toRatFunc (ofFraction (F := F) num den h) =
    am α (CPoly.toPoly num) / am α (CPoly.toPoly den)
  exact toRatFunc_ofFraction num den h

end CFrac

end DeepWiki.SymbolicIntegration
