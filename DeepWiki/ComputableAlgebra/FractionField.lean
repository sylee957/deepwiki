import DeepWiki.ComputableAlgebra.GenericPolyEngine
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The generic fraction field `QFunNZ α` (differential-tower carrier)
For a level `[CField α]`, `QFunNZ α` is the fraction field of `CPoly α = α[t]` (denominator-nonzero
fraction pairs) with a computable `CField (QFunNZ α)` instance; `[CFieldSpec α]` adds a noncomputable
bridge into `RatFunc (CFieldSpec.K α)`. Iterating builds the tower `ℚ ⊂ ℚ(x) ⊂ ℚ(x)(t₁) ⊂ …`. The
carrier and its `CField` instance need only `[CField α]` (denominator-nonzero via `cisZero`, not the
`CFieldSpec`-valued `toPoly`), so the engine reduces in the native compiler at every tower level.

General computable-algebra layer: the fraction field of the computable polynomial ring, domain-neutral
(no symbolic-integration specifics). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The generic fraction pair `QFun α` and its computable arithmetic -/

/-- Generic fraction pair `(numerator, denominator)` over `α[t] = CPoly α`. -/
abbrev QFun (α : Type*) [CField α] := CPoly α × CPoly α

namespace QFun

/-- Generic zero fraction `0/1` (numerator `[]`, denominator `[1]`). -/
def qzero {α : Type*} [CField α] : QFun α := ([], [CField.one])

/-- Generic one fraction `1/1` (numerator `[1]`, denominator `[1]`). -/
def qone {α : Type*} [CField α] : QFun α := ([CField.one], [CField.one])

/-- Generic fraction addition `a/b + c/d = (a·d + c·b)/(b·d)` (cross-multiply, no gcd reduction). -/
def qadd {α : Type*} [CField α] (x y : QFun α) : QFun α :=
  let (a, b) := x
  let (c, d) := y
  (CPoly.cadd (CPoly.cmul a d) (CPoly.cmul c b), CPoly.cmul b d)

/-- Generic fraction multiplication `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def qmul {α : Type*} [CField α] (x y : QFun α) : QFun α :=
  (CPoly.cmul x.1 y.1, CPoly.cmul x.2 y.2)

/-- Generic fraction negation `−(a/b) = (−a)/b` (denominator unchanged). -/
def qneg {α : Type*} [CField α] (x : QFun α) : QFun α := (CPoly.cneg x.1, x.2)

/-- Generic fraction inverse `(a/b)⁻¹ = b/a`; `qzero` if the numerator is zero (`0⁻¹ = 0`). -/
def qinv {α : Type*} [CField α] (x : QFun α) : QFun α :=
  if CPoly.cisZero x.1 then qzero else (x.2, x.1)

/-- Generic fraction subtraction `a/b − c/d := a/b + (−(c/d))`. -/
def qsub {α : Type*} [CField α] (x y : QFun α) : QFun α := qadd x (qneg y)

end QFun

/-! ### The denominator-nonzero subtype `QFunNZ α` (the tower-level carrier) -/

/-- Denominator-nonzero generic fractions: the subtype of `QFun α` with `cisZero den = false`. The
carrier of the next tower level (`QFunNZ ℚ ≅ ℚ(x)`, `QFunNZ (QFunNZ ℚ) ≅ ℚ(x)(t₁)`, …); needs only
`[CField α]`. -/
def QFunNZ (α : Type*) [CField α] : Type _ :=
  { x : QFun α // CPoly.cisZero x.2 = false }

/-! #### The pure-`CField` domain class `CFieldDomain` -/

/-- Polynomial-domain facts in pure `CField`/`CPoly` terms: `[1]` is `cisZero`-nonzero, and the product
of two `cisZero`-nonzero `CPoly`s is `cisZero`-nonzero. Carries no `CFieldSpec` data, so it can gate
the computable `CField (QFunNZ α)` instance. -/
class CFieldDomain (α : Type*) [CField α] where
  /-- The constant `[1]` is `cisZero`-nonzero. -/
  nz_one : CPoly.cisZero ([CField.one] : CPoly α) = false
  /-- The product of two `cisZero`-nonzero `CPoly`s is `cisZero`-nonzero (no zero divisors). -/
  nz_mul : ∀ {b d : CPoly α}, CPoly.cisZero b = false → CPoly.cisZero d = false →
    CPoly.cisZero (CPoly.cmul b d) = false

/-- Every `[CFieldSpec α]` level is a `CFieldDomain`, since `(CFieldSpec.K α)[X]` is an integral domain;
provides only `Prop` fields (erased at runtime). -/
noncomputable instance instCFieldDomainOfCFieldSpec {α : Type*} [CField α] [CFieldSpec α] :
    CFieldDomain α where
  nz_one := by
    rw [Bool.eq_false_iff, Ne, CPoly.cisZeroG_iff]
    simp only [denote, mul_zero, add_zero, map_one]
    show (1 : (CFieldSpec.K α)[X]) ≠ 0
    exact one_ne_zero
  nz_mul := by
    intro b d hb hd
    rw [Bool.eq_false_iff] at hb hd ⊢
    rw [Ne, CPoly.cisZeroG_iff] at hb hd ⊢
    simp only [denote]
    exact mul_ne_zero hb hd

namespace QFunNZ

/-- The constant `[1]` is `cisZero`-nonzero (from `CFieldDomain`). -/
theorem cisZeroG_one_singleton {α : Type*} [CField α] [CFieldDomain α] :
    CPoly.cisZero ([CField.one] : CPoly α) = false :=
  CFieldDomain.nz_one

/-- The product of two `cisZero`-nonzero `CPoly`s is `cisZero`-nonzero (from `CFieldDomain`). -/
theorem cmulG_ne_zero_of {α : Type*} [CField α] [CFieldDomain α] {b d : CPoly α}
    (hb : CPoly.cisZero b = false)
    (hd : CPoly.cisZero d = false) : CPoly.cisZero (CPoly.cmul b d) = false :=
  CFieldDomain.nz_mul hb hd

/-- `qzeroNZ`: the zero fraction `0/1` as a `QFunNZ` (denominator `[1]` is nonzero). -/
def qzeroNZ {α : Type*} [CField α] [CFieldDomain α] : QFunNZ α :=
  ⟨QFun.qzero, cisZeroG_one_singleton⟩

/-- `qoneNZ`: the one fraction `1/1` as a `QFunNZ` (denominator `[1]` is nonzero). -/
def qoneNZ {α : Type*} [CField α] [CFieldDomain α] : QFunNZ α :=
  ⟨QFun.qone, cisZeroG_one_singleton⟩

/-- `qaddNZ`: addition on `QFunNZ` (the product denominator `b·d` is nonzero). -/
def qaddNZ {α : Type*} [CField α] [CFieldDomain α] (x y : QFunNZ α) : QFunNZ α :=
  ⟨QFun.qadd x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    exact cmulG_ne_zero_of hb hd⟩

/-- `qmulNZ`: multiplication on `QFunNZ` (the product denominator `b·d` is nonzero). -/
def qmulNZ {α : Type*} [CField α] [CFieldDomain α] (x y : QFunNZ α) : QFunNZ α :=
  ⟨QFun.qmul x.1 y.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    obtain ⟨⟨c, d⟩, hd⟩ := y
    exact cmulG_ne_zero_of hb hd⟩

/-- `qnegNZ`: negation on `QFunNZ` (denominator unchanged). -/
def qnegNZ {α : Type*} [CField α] (x : QFunNZ α) : QFunNZ α := ⟨QFun.qneg x.1, x.2⟩

/-- `qinvNZ`: inverse on `QFunNZ`. If the numerator's zero test holds, the result is `qzeroNZ` (the
`0⁻¹ = 0` convention); otherwise swap numerator and denominator (the new denominator is the old
numerator, nonzero exactly by `¬ cisZero`). -/
def qinvNZ {α : Type*} [CField α] [CFieldDomain α] (x : QFunNZ α) : QFunNZ α :=
  if h : CPoly.cisZero x.1.1 then qzeroNZ
  else ⟨(x.1.2, x.1.1), Bool.not_eq_true _ ▸ h⟩

/-- `qsubNZ`: subtraction on `QFunNZ`, `x − y := x + (−y)`. -/
def qsubNZ {α : Type*} [CField α] [CFieldDomain α] (x y : QFunNZ α) : QFunNZ α :=
  qaddNZ x (qnegNZ y)

/-- `isZeroNZ`: the zero test on `QFunNZ`, reading `cisZero` off the **numerator** (the denominator
is nonzero by membership, so `x = 0` iff its numerator vanishes). -/
def isZeroNZ {α : Type*} [CField α] (x : QFunNZ α) : Bool := CPoly.cisZero x.1.1

end QFunNZ

/-! ### The computable `CField (QFunNZ α)` instance -/

/-- `CField (QFunNZ α)`: the next tower level (fraction field of `α[t]`) as a computable field (over
`[CField α] [CFieldDomain α]`, no `CFieldSpec`), so the engine reduces over `CPoly (QFunNZ α)`. -/
instance instCFieldQFunNZ {α : Type*} [CField α] [CFieldDomain α] : CField (QFunNZ α) where
  zero := QFunNZ.qzeroNZ
  one := QFunNZ.qoneNZ
  add := QFunNZ.qaddNZ
  mul := QFunNZ.qmulNZ
  neg := QFunNZ.qnegNZ
  inv := QFunNZ.qinvNZ
  isZero := QFunNZ.isZeroNZ

/-! ### The bridge `toQFunNZ` into `RatFunc (CFieldSpec.K α)` and its homomorphism laws -/

namespace QFunNZ

/-- `am = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))`, the polynomial-into-rational
embedding for the bridge. -/
noncomputable abbrev am (α : Type*) [CField α] [CFieldSpec α] :
    (CFieldSpec.K α)[X] →+* RatFunc (CFieldSpec.K α) :=
  algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))

/-- `am (toPoly p) ≠ 0` whenever `toPoly p ≠ 0` (the embedding `algebraMap K[X] (RatFunc K)` is
injective). -/
theorem amG_toPolyG_ne_zero {α : Type*} [CField α] [CFieldSpec α] {p : CPoly α}
    (hp : CPoly.toPoly p ≠ 0) :
    am α (CPoly.toPoly p) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mpr hp

/-- `cisZero b = false` reads as `toPoly b ≠ 0` (the denominator nonzero criterion through the
bridge). -/
theorem toPolyG_ne_zero_of_cisZeroG_false {α : Type*} [CField α] [CFieldSpec α] {b : CPoly α}
    (hb : CPoly.cisZero b = false) :
    CPoly.toPoly b ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, CPoly.cisZeroG_iff] at hb; exact hb

/-- `toQFunNZ (num, den) = am (toPoly num) / am (toPoly den)` in `RatFunc (CFieldSpec.K α)`; the
bridge `toK` of the next tower level. -/
noncomputable def toQFunNZ {α : Type*} [CField α] [CFieldSpec α] (x : QFunNZ α) :
    RatFunc (CFieldSpec.K α) :=
  am α (CPoly.toPoly x.1.1) / am α (CPoly.toPoly x.1.2)

/-- `toQFunNZ qzeroNZ = 0`. -/
theorem toQFunNZG_qzeroNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] :
    toQFunNZ (qzeroNZ : QFunNZ α) = 0 := by
  rw [toQFunNZ]
  show am α (CPoly.toPoly ([] : CPoly α)) / _ = 0
  rw [CPoly.toPolyG_nil, map_zero, zero_div]

/-- `toQFunNZ qoneNZ = 1`. -/
theorem toQFunNZG_qoneNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] :
    toQFunNZ (qoneNZ : QFunNZ α) = 1 := by
  rw [toQFunNZ]
  show am α (CPoly.toPoly ([CField.one] : CPoly α))
      / am α (CPoly.toPoly ([CField.one] : CPoly α)) = 1
  have h1 : CPoly.toPoly ([CField.one] : CPoly α) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  rw [h1, map_one, div_self one_ne_zero]

/-- `toQFunNZ (qaddNZ x y) = toQFunNZ x + toQFunNZ y`: `qaddNZ` realizes `+`. -/
theorem toQFunNZG_qaddNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : QFunNZ α) :
    toQFunNZ (qaddNZ x y) = toQFunNZ x + toQFunNZ y := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  obtain ⟨⟨c, d⟩, hd⟩ := y
  have hb' : am α (CPoly.toPoly b) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hb)
  have hd' : am α (CPoly.toPoly d) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hd)
  show am α (CPoly.toPoly (CPoly.cadd (CPoly.cmul a d) (CPoly.cmul c b)))
      / am α (CPoly.toPoly (CPoly.cmul b d))
    = am α (CPoly.toPoly a) / am α (CPoly.toPoly b)
      + am α (CPoly.toPoly c) / am α (CPoly.toPoly d)
  simp only [denote, map_add, map_mul]
  rw [div_add_div _ _ hb' hd']
  ring

/-- `toQFunNZ (qmulNZ x y) = toQFunNZ x * toQFunNZ y`: `qmulNZ` realizes `*`. -/
theorem toQFunNZG_qmulNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : QFunNZ α) :
    toQFunNZ (qmulNZ x y) = toQFunNZ x * toQFunNZ y := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  obtain ⟨⟨c, d⟩, hd⟩ := y
  show am α (CPoly.toPoly (CPoly.cmul a c)) / am α (CPoly.toPoly (CPoly.cmul b d))
    = am α (CPoly.toPoly a) / am α (CPoly.toPoly b)
      * (am α (CPoly.toPoly c) / am α (CPoly.toPoly d))
  simp only [denote, map_mul]
  rw [div_mul_div_comm]

/-- `toQFunNZ (qnegNZ x) = - toQFunNZ x`: `qnegNZ` realizes negation. -/
theorem toQFunNZG_qnegNZG {α : Type*} [CField α] [CFieldSpec α] (x : QFunNZ α) :
    toQFunNZ (qnegNZ x) = - toQFunNZ x := by
  obtain ⟨⟨a, b⟩, hb⟩ := x
  show am α (CPoly.toPoly (CPoly.cneg a)) / am α (CPoly.toPoly b)
    = - (am α (CPoly.toPoly a) / am α (CPoly.toPoly b))
  simp only [denote, map_neg]
  rw [neg_div]

/-- `toQFunNZ (qinvNZ x) = (toQFunNZ x)⁻¹`: `qinvNZ` realizes `⁻¹` (`0⁻¹ = 0`). -/
theorem toQFunNZG_qinvNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x : QFunNZ α) :
    toQFunNZ (qinvNZ x) = (toQFunNZ x)⁻¹ := by
  rw [qinvNZ]
  by_cases h : CPoly.cisZero x.1.1
  · rw [dif_pos h, toQFunNZG_qzeroNZG]
    have hx0 : CPoly.toPoly x.1.1 = 0 := (CPoly.cisZeroG_iff x.1.1).mp h
    have : toQFunNZ x = 0 := by
      rw [toQFunNZ, hx0, map_zero, zero_div]
    rw [this, inv_zero]
  · rw [dif_neg h]
    show am α (CPoly.toPoly x.1.2) / am α (CPoly.toPoly x.1.1)
      = (am α (CPoly.toPoly x.1.1) / am α (CPoly.toPoly x.1.2))⁻¹
    rw [inv_div]

/-- `toQFunNZ (qsubNZ x y) = toQFunNZ x - toQFunNZ y`: `qsubNZ` realizes subtraction. -/
theorem toQFunNZG_qsubNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α] (x y : QFunNZ α) :
    toQFunNZ (qsubNZ x y) = toQFunNZ x - toQFunNZ y := by
  rw [qsubNZ, toQFunNZG_qaddNZG, toQFunNZG_qnegNZG, sub_eq_add_neg]

/-- `isZeroNZ x = true ↔ toQFunNZ x = 0`: the numerator zero test agrees with vanishing in
`RatFunc (CFieldSpec.K α)`. -/
theorem isZeroNZG_iff {α : Type*} [CField α] [CFieldSpec α] (x : QFunNZ α) :
    isZeroNZ x = true ↔ toQFunNZ x = 0 := by
  rw [isZeroNZ, CPoly.cisZeroG_iff]
  obtain ⟨⟨a, b⟩, hb⟩ := x
  have hbm : am α (CPoly.toPoly b) ≠ 0 :=
    amG_toPolyG_ne_zero (toPolyG_ne_zero_of_cisZeroG_false hb)
  show CPoly.toPoly a = 0 ↔ am α (CPoly.toPoly a) / am α (CPoly.toPoly b) = 0
  constructor
  · intro h; rw [h, map_zero, zero_div]
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact (map_eq_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K α))).mp h
    · exact absurd h hbm

end QFunNZ

/-- `CFieldSpec (QFunNZ α)`: the field-homomorphism bridge over `K = RatFunc (CFieldSpec.K α)` with
`toK = toQFunNZ`. Noncomputable; only the correctness layer depends on it. -/
noncomputable instance instCFieldSpecQFunNZ {α : Type*} [CField α] [CFieldSpec α] :
    CFieldSpec (QFunNZ α) where
  K := RatFunc (CFieldSpec.K α)
  toK := QFunNZ.toQFunNZ
  toK_zero := QFunNZ.toQFunNZG_qzeroNZG
  toK_one := QFunNZ.toQFunNZG_qoneNZG
  toK_add := QFunNZ.toQFunNZG_qaddNZG
  toK_mul := QFunNZ.toQFunNZG_qmulNZG
  toK_neg := QFunNZ.toQFunNZG_qnegNZG
  toK_inv := QFunNZ.toQFunNZG_qinvNZG
  isZero_iff := QFunNZ.isZeroNZG_iff

end DeepWiki.SymbolicIntegration
