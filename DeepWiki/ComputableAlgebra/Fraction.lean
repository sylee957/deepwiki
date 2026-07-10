import DeepWiki.ComputableAlgebra.FracReprDense
import DeepWiki.ComputableAlgebra.FracReprSparse
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The generic fraction field `DenseFrac α` (differential-tower carrier)
For a level `[CField α]`, `DenseFrac α` is the fraction field of `DensePoly α = α[t]` (denominator-nonzero
fraction pairs) with a computable `CField (DenseFrac α)` instance; `[CFieldSpec α]` adds a noncomputable
bridge into `RatFunc (CFieldSpec.K α)`. Iterating builds the tower `ℚ ⊂ ℚ(x) ⊂ ℚ(x)(t₁) ⊂ …`. The
carrier and its `CField` instance need only `[CField α]` (denominator-nonzero via `cisZero`, not the
`CFieldSpec`-valued `toPoly`), so the engine reduces in the native compiler at every tower level.

General computable-algebra layer: the fraction field of the computable polynomial ring, domain-neutral
(no symbolic-integration specifics). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-! #### The pure-`CField` domain class `CFieldDomain` -/

/-- Polynomial-domain facts for representation `P`: `1` is nonzero and products of nonzero
polynomials are nonzero. The dense representation is the default for existing tower signatures. -/
class CFieldDomain (α : Type u) [CField α]
    (P : Type u → Type u := DensePoly) [CPoly P] [CPolyEngine P] where
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

/-- The represented constant `1` is nonzero (from `CFieldDomain`). -/
theorem cisZeroG_one_singleton {α : Type u} [CField α] [CFieldDomain α P] :
    CPolyEngine.cisZero (CPoly.one : P α) = false :=
  CFieldDomain.nz_one

/-- The product of two represented nonzero polynomials is nonzero (from `CFieldDomain`). -/
theorem cmulG_ne_zero_of {α : Type u} [CField α] [CFieldDomain α P] {b d : P α}
    (hb : CPolyEngine.cisZero b = false)
    (hd : CPolyEngine.cisZero d = false) :
    CPolyEngine.cisZero (CPolyEngine.mul b d) = false :=
  CFieldDomain.nz_mul hb hd

/-- Embed a computable polynomial as the fraction `p/1`. -/
def ofPoly {α : Type u} [CField α] [CFieldDomain α P] (p : P α) : F α :=
  ofFraction p CPoly.one cisZeroG_one_singleton

/-- Embed a coefficient as the constant fraction `a/1`. -/
def ofScalar {α : Type u} [CField α] [CFieldDomain α P] (a : α) : F α :=
  ofPoly (CPolyEngine.ofCoeffList [a])

/-- The numerator of the polynomial embedding is the original polynomial. -/
@[simp] theorem num_ofPoly {α : Type u} [CField α] [CFieldDomain α P] (p : P α) :
    num (ofPoly (F := F) p) = p := by simp [ofPoly]

/-- The denominator of the polynomial embedding is `1`. -/
@[simp] theorem den_ofPoly {α : Type u} [CField α] [CFieldDomain α P] (p : P α) :
    den (ofPoly (F := F) p) = CPoly.one := by simp [ofPoly]

/-- `qaddNZ`: addition on `CFrac` (the product denominator `b·d` is nonzero). -/
def qaddNZ {α : Type u} [CField α] [CFieldDomain α P] (x y : F α) : F α :=
  ofFraction
    (CPolyEngine.add (CPolyEngine.mul (num x) (den y))
      (CPolyEngine.mul (num y) (den x)))
    (CPolyEngine.mul (den x) (den y))
    (cmulG_ne_zero_of (cisZeroG_den x) (cisZeroG_den y))

/-- `qmulNZ`: multiplication on `CFrac` (the product denominator `b·d` is nonzero). -/
def qmulNZ {α : Type u} [CField α] [CFieldDomain α P] (x y : F α) : F α :=
  ofFraction (CPolyEngine.mul (num x) (num y))
    (CPolyEngine.mul (den x) (den y))
    (cmulG_ne_zero_of (cisZeroG_den x) (cisZeroG_den y))

/-- `qnegNZ`: negation on `CFrac` (denominator unchanged). -/
def qnegNZ {α : Type u} [CField α] (x : F α) : F α :=
  ofFraction (CPolyEngine.neg (num x)) (den x) (cisZeroG_den x)

/-- `qinvNZ`: inverse on `CFrac`. If the numerator's zero test holds, the result is `ofPoly []` (the
`0⁻¹ = 0` convention); otherwise swap numerator and denominator (the new denominator is the old
numerator, nonzero exactly by `¬ cisZero`). -/
def qinvNZ {α : Type u} [CField α] [CFieldDomain α P] (x : F α) : F α :=
  if h : CPolyEngine.cisZero (num x) then ofPoly CPoly.czero
  else ofFraction (den x) (num x) (Bool.not_eq_true _ ▸ h)

/-- `qsubNZ`: subtraction on `CFrac`, `x − y := x + (−y)`. -/
def qsubNZ {α : Type u} [CField α] [CFieldDomain α P] (x y : F α) : F α :=
  qaddNZ x (qnegNZ y)

/-- Formal polynomial-variable derivative of a represented fraction by the quotient rule. -/
def qderiv {α : Type u} [CField α] [CFieldDomain α P] (x : F α) : F α :=
  ofFraction
    (CPolyEngine.sub
      (CPolyEngine.mul (CPolyEngine.deriv (num x)) (den x))
      (CPolyEngine.mul (num x) (CPolyEngine.deriv (den x))))
    (CPolyEngine.mul (den x) (den x))
    (cmulG_ne_zero_of (cisZeroG_den x) (cisZeroG_den x))

/-- `isZeroNZ`: the zero test on `CFrac`, reading `cisZero` off the **numerator** (the denominator
is nonzero by membership, so `x = 0` iff its numerator vanishes). -/
def isZeroNZ {α : Type u} [CField α] (x : F α) : Bool := CPolyEngine.cisZero (num x)

end CFrac

/-! ### The computable `CField (DenseFrac α)` instance -/

/-- Every `CFrac F P` with polynomial-domain evidence is a computable field representation. -/
instance instCFieldCFrac {F : (α : Type u) → [CField α] → Type u}
    {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CFrac F P]
    {α : Type u} [CField α] [CFieldDomain α P] : CField (F α) where
  zero := CFrac.ofPoly (CPoly.czero : P α)
  one := CFrac.ofPoly (CPoly.one : P α)
  add := CFrac.qaddNZ
  mul := CFrac.qmulNZ
  neg := CFrac.qnegNZ
  inv := CFrac.qinvNZ
  isZero := CFrac.isZeroNZ

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let one : SparseFrac ℚ := CFrac.ofFraction (ofList [1]) (ofList [1])
    let sum := CCommRing.add one one
    CPoly.coeff (CFrac.num sum) 0 = 2 ∧ CPoly.coeff (CFrac.den sum) 0 = 1 := by
  native_decide

/-! ### The bridge `toCFrac` into `RatFunc (CFieldSpec.K α)` and its homomorphism laws -/

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

omit [CPolyEngine P] in
/-- A nonzero represented polynomial remains nonzero in the rational-function field. -/
theorem am_toPoly_ne_zero {α : Type u} [CField α] [CFieldSpec.{u,v} α] {p : P α}
    (hp : CPoly.toPoly p ≠ 0) : am α (CPoly.toPoly p) ≠ 0 :=
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
@[denote] theorem toRatFunc_qaddNZ [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (x y : F α) :
    toRatFunc (qaddNZ x y) = toRatFunc x + toRatFunc y := by
  rw [qaddNZ, toRatFunc_ofFraction, toRatFunc_eq_div, toRatFunc_eq_div]
  simp only [LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_mul, map_add, map_mul]
  have hx : am α (CPoly.toPoly (den x)) ≠ 0 :=
    am_toPoly_ne_zero (toPoly_den_ne_zero_generic x)
  have hy : am α (CPoly.toPoly (den y)) ≠ 0 :=
    am_toPoly_ne_zero (toPoly_den_ne_zero_generic y)
  rw [div_add_div _ _ hx hy]
  ring

/-- Represented fraction multiplication realizes multiplication in `RatFunc`. -/
@[denote] theorem toRatFunc_qmulNZ [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (x y : F α) :
    toRatFunc (qmulNZ x y) = toRatFunc x * toRatFunc y := by
  rw [qmulNZ, toRatFunc_ofFraction, toRatFunc_eq_div, toRatFunc_eq_div]
  simp only [LawfulCPolyEngine.toPoly_mul, map_mul]
  rw [div_mul_div_comm]

/-- Represented fraction negation realizes negation in `RatFunc`. -/
@[denote] theorem toRatFunc_qnegNZ [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (x : F α) :
    toRatFunc (qnegNZ x) = -toRatFunc x := by
  rw [qnegNZ, toRatFunc_ofFraction, toRatFunc_eq_div]
  simp only [LawfulCPolyEngine.toPoly_neg, map_neg, neg_div]

/-- Represented fraction inversion realizes inversion in `RatFunc`. -/
@[denote] theorem toRatFunc_qinvNZ [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P] (x : F α) :
    toRatFunc (qinvNZ x) = (toRatFunc x)⁻¹ := by
  rw [qinvNZ]
  split
  next hzero =>
    have hnum : CPoly.toPoly (num x) = 0 :=
      (LawfulCPolyEngine.cisZero_iff (P := P) (num x)).mp hzero
    rw [toRatFunc_ofPoly, CPoly.toPoly_czero, map_zero, toRatFunc_eq_div, hnum, map_zero,
      zero_div, inv_zero]
  next _ =>
    rw [toRatFunc_ofFraction, toRatFunc_eq_div, inv_div]

/-- The represented numerator zero test agrees with vanishing in `RatFunc`. -/
@[denote] theorem isZeroNZ_iff_toRatFunc [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (x : F α) :
    isZeroNZ x = true ↔ toRatFunc x = 0 := by
  rw [isZeroNZ, LawfulCPolyEngine.cisZero_iff, toRatFunc_eq_div]
  have hden : am α (CPoly.toPoly (den x)) ≠ 0 :=
    am_toPoly_ne_zero (toPoly_den_ne_zero_generic x)
  constructor
  · intro hzero
    rw [hzero, map_zero, zero_div]
  · intro hzero
    rw [div_eq_zero_iff] at hzero
    rcases hzero with hzero | hzero
    · exact (map_eq_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mp hzero
    · exact absurd hzero hden

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
  toK_add := toRatFunc_qaddNZ
  toK_mul := toRatFunc_qmulNZ
  toK_neg := toRatFunc_qnegNZ
  toK_inv := toRatFunc_qinvNZ
  isZero_iff := isZeroNZ_iff_toRatFunc

/-- `am (toPoly p) ≠ 0` whenever `toPoly p ≠ 0` (the embedding `algebraMap K[X] (RatFunc K)` is
injective). -/
theorem amG_toPolyG_ne_zero {α : Type*} [CField α] [CFieldSpec α] {p : DensePoly α}
    (hp : DensePoly.toPoly p ≠ 0) :
    am α (DensePoly.toPoly p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mpr hp

/-- `cisZero b = false` reads as `toPoly b ≠ 0` (the denominator nonzero criterion through the
bridge). -/
theorem toPolyG_ne_zero_of_cisZeroG_false {α : Type*} [CField α] [CFieldSpec α] {b : DensePoly α}
    (hb : DensePoly.cisZero b = false) :
    DensePoly.toPoly b ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, DensePoly.cisZeroG_iff] at hb; exact hb

/-- A computable fraction's stored denominator denotes a nonzero polynomial. -/
theorem toPoly_den_ne_zero {α : Type*} [CField α] [CFieldSpec α] (x : DenseFrac α) :
    DensePoly.toPoly (den x) ≠ 0 := by
  obtain ⟨a, b, hb⟩ := x
  exact toPolyG_ne_zero_of_cisZeroG_false hb

/-- `toCFrac (num, den) = am (toPoly num) / am (toPoly den)` in `RatFunc (CFieldSpec.K α)`; the
bridge `toK` of the next tower level. -/
noncomputable def toCFrac {α : Type*} [CField α] [CFieldSpec α] (x : DenseFrac α) :
    RatFunc (CFieldSpec.K α) :=
  am α (DensePoly.toPoly (num x)) / am α (DensePoly.toPoly (den x))

/-- A computable fraction denotes its numerator divided by its denominator. -/
theorem toCFrac_eq_div {α : Type*} [CField α] [CFieldSpec α] (x : DenseFrac α) :
    toCFrac x = am α (DensePoly.toPoly (num x)) / am α (DensePoly.toPoly (den x)) := rfl

/-- A constructed computable fraction denotes its numerator divided by its denominator. -/
@[denote] theorem toCFrac_ofFraction {α : Type*} [CField α] [CFieldSpec α]
    (num den : DensePoly α) (h : DensePoly.cisZero den = false) :
    toCFrac (ofFraction num den h) =
      am α (DensePoly.toPoly num) / am α (DensePoly.toPoly den) := rfl

/-- The polynomial embedding denotes the natural map from polynomials to rational functions. -/
@[denote] theorem toCFrac_ofPoly {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α]
    (p : DensePoly α) :
    toCFrac (ofPoly p) = am α (DensePoly.toPoly p) := by
  rw [toCFrac_eq_div, num_ofPoly, den_ofPoly]
  have hone : DensePoly.toPoly (CPoly.one : DensePoly α) = 1 := by
    rw [← toPoly_list_eq, CPoly.toPoly_one]
  rw [hone, map_one, div_one]

/-- A polynomial embedding has nonzero denotation when its polynomial zero test is false. -/
theorem toCFrac_ofPoly_ne_zero {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α]
    {p : DensePoly α} (hp : DensePoly.cisZero p = false) : toCFrac (ofPoly p) ≠ 0 := by
  rw [toCFrac_ofPoly]
  exact amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hp)

/-- `toCFrac (qaddNZ x y) = toCFrac x + toCFrac y`: `qaddNZ` realizes `+`. -/
theorem toCFracG_qaddNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : DenseFrac α) :
    toCFrac (qaddNZ x y) = toCFrac x + toCFrac y := by
  obtain ⟨a, b, hb⟩ := x
  obtain ⟨c, d, hd⟩ := y
  have hb' : am α (DensePoly.toPoly b) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hb)
  have hd' : am α (DensePoly.toPoly d) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hd)
  show am α (DensePoly.toPoly (DensePoly.cadd (DensePoly.cmul a d) (DensePoly.cmul c b)))
      / am α (DensePoly.toPoly (DensePoly.cmul b d))
    = am α (DensePoly.toPoly a) / am α (DensePoly.toPoly b)
      + am α (DensePoly.toPoly c) / am α (DensePoly.toPoly d)
  simp only [denote, map_add, map_mul]
  rw [div_add_div _ _ hb' hd']
  ring

/-- `toCFrac (qmulNZ x y) = toCFrac x * toCFrac y`: `qmulNZ` realizes `*`. -/
theorem toCFracG_qmulNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : DenseFrac α) :
    toCFrac (qmulNZ x y) = toCFrac x * toCFrac y := by
  obtain ⟨a, b, hb⟩ := x
  obtain ⟨c, d, hd⟩ := y
  show am α (DensePoly.toPoly (DensePoly.cmul a c)) / am α (DensePoly.toPoly (DensePoly.cmul b d))
    = am α (DensePoly.toPoly a) / am α (DensePoly.toPoly b)
      * (am α (DensePoly.toPoly c) / am α (DensePoly.toPoly d))
  simp only [denote, map_mul]
  rw [div_mul_div_comm]

/-- `toCFrac (qnegNZ x) = - toCFrac x`: `qnegNZ` realizes negation. -/
theorem toCFracG_qnegNZG {α : Type*} [CField α] [CFieldSpec α] (x : DenseFrac α) :
    toCFrac (qnegNZ x) = - toCFrac x := by
  obtain ⟨a, b, hb⟩ := x
  show am α (DensePoly.toPoly (DensePoly.cneg a)) / am α (DensePoly.toPoly b)
    = - (am α (DensePoly.toPoly a) / am α (DensePoly.toPoly b))
  simp only [denote, map_neg]
  rw [neg_div]

/-- `toCFrac (qinvNZ x) = (toCFrac x)⁻¹`: `qinvNZ` realizes `⁻¹` (`0⁻¹ = 0`). -/
theorem toCFracG_qinvNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x : DenseFrac α) :
    toCFrac (qinvNZ x) = (toCFrac x)⁻¹ := by
  unfold qinvNZ
  split
  next h =>
    simp only [CPolyEngine.cisZero_dense_eq] at h
    rw [toCFrac_ofPoly]
    have hczero : DensePoly.toPoly (CPoly.czero : DensePoly α) = 0 := by
      rw [← toPoly_list_eq, CPoly.toPoly_czero]
    rw [hczero, map_zero]
    have hx0 : DensePoly.toPoly (num x) = 0 := (DensePoly.cisZeroG_iff (num x)).mp h
    have : toCFrac x = 0 := by
      rw [toCFrac, hx0, map_zero, zero_div]
    rw [this, inv_zero]
  next h =>
    show am α (DensePoly.toPoly (den x)) / am α (DensePoly.toPoly (num x))
      = (am α (DensePoly.toPoly (num x)) / am α (DensePoly.toPoly (den x)))⁻¹
    rw [inv_div]

/-- `toCFrac (qsubNZ x y) = toCFrac x - toCFrac y`: `qsubNZ` realizes subtraction. -/
theorem toCFracG_qsubNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : DenseFrac α) :
    toCFrac (qsubNZ x y) = toCFrac x - toCFrac y := by
  rw [qsubNZ, toCFracG_qaddNZG, toCFracG_qnegNZG, sub_eq_add_neg]

/-- `isZeroNZ x = true ↔ toCFrac x = 0`: the numerator zero test agrees with vanishing in
`RatFunc (CFieldSpec.K α)`. -/
theorem isZeroNZG_iff {α : Type*} [CField α] [CFieldSpec α] (x : DenseFrac α) :
    isZeroNZ x = true ↔ toCFrac x = 0 := by
  rw [isZeroNZ, CPolyEngine.cisZero_dense_eq, DensePoly.cisZeroG_iff]
  obtain ⟨a, b, hb⟩ := x
  have hbm : am α (DensePoly.toPoly b) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hb)
  show DensePoly.toPoly a = 0 ↔ am α (DensePoly.toPoly a) / am α (DensePoly.toPoly b) = 0
  constructor
  · intro h; rw [h, map_zero, zero_div]
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact (map_eq_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mp h
    · exact absurd h hbm

end CFrac

/-- `CFieldSpec (DenseFrac α)`: the field-homomorphism bridge over `K = RatFunc (CFieldSpec.K α)` with
`toK = toCFrac`. Noncomputable; only the correctness layer depends on it. -/
noncomputable instance instCFieldSpecCFrac {α : Type*} [CField α] [CFieldSpec α] :
    CFieldSpec (DenseFrac α) where
  K := RatFunc (CFieldSpec.K α)
  toK := CFrac.toCFrac
  toK_zero := by
    change CFrac.toCFrac (CFrac.ofPoly ([] : DensePoly α)) = 0
    rw [CFrac.toCFrac_ofPoly, DensePoly.toPolyG_nil, map_zero]
  toK_one := by
    change CFrac.toCFrac (CFrac.ofPoly ([CCommRing.one] : DensePoly α)) = 1
    rw [CFrac.toCFrac_ofPoly]
    simp only [denote, mul_zero, add_zero, map_one]
  toK_add := CFrac.toCFracG_qaddNZG
  toK_mul := CFrac.toCFracG_qmulNZG
  toK_neg := CFrac.toCFracG_qnegNZG
  toK_inv := CFrac.toCFracG_qinvNZG
  isZero_iff := CFrac.isZeroNZG_iff

/-- `SparseFrac α` inherits the generic `RatFunc` denotation from the `CFrac` interface and the
lawful sparse polynomial engine. -/
noncomputable instance instCFieldSpecSparseFrac {α : Type u} [CField α] [CFieldSpec.{u,v} α] :
    CFieldSpec (SparseFrac α) :=
  CFrac.fieldSpec (F := SparseFrac) (P := CPoly.SparsePoly)

namespace CFrac

/-- The field bridge sends the polynomial embedding to the natural rational-function embedding. -/
@[denote] theorem toK_ofPoly {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α]
    (p : DensePoly α) :
    CFieldSpec.toK (ofPoly p : DenseFrac α) = am α (DensePoly.toPoly p) :=
  toCFrac_ofPoly p

/-- The field bridge sends a packaged fraction to the quotient of its polynomial denotations. -/
@[denote] theorem toK_ofFraction {α : Type*} [CField α] [CFieldSpec α]
    (num den : DensePoly α) (h : DensePoly.cisZero den = false) :
    CFieldSpec.toK (ofFraction num den h : DenseFrac α) =
      am α (DensePoly.toPoly num) / am α (DensePoly.toPoly den) :=
  toCFrac_ofFraction num den h

end CFrac

example :
    CFieldSpec.toK (CFrac.ofPoly (F := SparseFrac)
      (CPoly.SparsePoly.ofList [(0, 1), (1, 2)] : CPoly.SparsePoly ℚ))
      = CFrac.am ℚ (CPoly.toPoly (CPoly.SparsePoly.ofList [(0, 1), (1, 2)] : CPoly.SparsePoly ℚ)) := by
  exact CFrac.toRatFunc_ofPoly _

end DeepWiki.SymbolicIntegration
