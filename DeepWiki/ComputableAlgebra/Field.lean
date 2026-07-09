import DeepWiki.ComputableAlgebra.CommRing
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat

/-! # Computable fields (`CField`) and the field-homomorphism spec (`CFieldSpec`)

`CField α`: computable field operations (`zero`/`one`/`add`/`mul`/`neg`/`inv`, zero test), bridge-free
so instances stay computable; every `CField` is a `CCommRing` (bridge below). `CFieldSpec α`: the
companion homomorphism `toK : α → K` into a Mathlib `Field K` (a `CRingSpec` with `R = K`). `ℚ` is the
base instance. See `CommRing.lean` for the ring layer, `Polynomial.lean` for the `DensePoly` engine. -/

namespace DeepWiki.SymbolicIntegration

/-! ### The `CField` typeclass (computable operations only)

`CField α`: the computable field operations plus zero test, bridge-free so instances stay
computable; correctness proofs add `[CFieldSpec α]`. -/

/-- Computable field operations: `zero`/`one`/`add`/`mul`/`neg`/`inv` and a zero test `isZero`;
bridge-free, so instances stay computable. -/
class CField (α : Type*) where
  /-- Computable zero. -/
  zero : α
  /-- Computable one. -/
  one : α
  /-- Computable addition. -/
  add : α → α → α
  /-- Computable multiplication. -/
  mul : α → α → α
  /-- Computable negation. -/
  neg : α → α
  /-- Computable inverse (`0⁻¹ = 0`). -/
  inv : α → α
  /-- Computable zero test. -/
  isZero : α → Bool

namespace CField

/-- Computable subtraction `a - b := a + (-b)`, derived from `add`/`neg`. -/
def sub {α : Type*} [CField α] (a b : α) : α := add a (neg b)

/-- Computable division `a / b := a * b⁻¹`, derived from `mul`/`inv`. -/
def div {α : Type*} [CField α] (a b : α) : α := mul a (inv b)

end CField

/-- Every computable field is a computable commutative ring (forget `inv`). Bridge instance: makes
`[CCommRing α]` available at every `[CField α]` type, so ring-generic engine ops resolve on field
coefficients unchanged. -/
instance (priority := 100) instCCommRingOfCField {α : Type*} [CField α] : CCommRing α where
  zero := CField.zero
  one := CField.one
  add := CField.add
  mul := CField.mul
  neg := CField.neg
  isZero := CField.isZero

/-! ### The `CFieldSpec` typeclass (the field-homomorphism bridge)

`CFieldSpec α`: the noncomputable bridge `toK : α → K` into a Mathlib `Field K` intertwining the
`CField` operations, with `isZero_iff` certifying the zero test; `toK` need not be injective. -/

/-- Computable-field specification: the bridge `toK : α → K` into a Mathlib `Field K` intertwining
`zero`/`one`/`add`/`mul`/`neg`/`inv`, plus `isZero_iff` certifying `CField.isZero`. -/
class CFieldSpec (α : Type*) [CField α] where
  /-- The genuine Mathlib field the bridge lands in. -/
  K : Type*
  /-- `K` is a field. -/
  [instField : Field K]
  /-- The bridge to the genuine field. -/
  toK : α → K
  /-- `toK` sends `zero` to `0`. -/
  toK_zero : toK CField.zero = 0
  /-- `toK` sends `one` to `1`. -/
  toK_one : toK CField.one = 1
  /-- `toK` intertwines `add` with `+`. -/
  toK_add : ∀ a b, toK (CField.add a b) = toK a + toK b
  /-- `toK` intertwines `mul` with `*`. -/
  toK_mul : ∀ a b, toK (CField.mul a b) = toK a * toK b
  /-- `toK` intertwines `neg` with `-`. -/
  toK_neg : ∀ a, toK (CField.neg a) = - toK a
  /-- `toK` intertwines `inv` with `⁻¹`. -/
  toK_inv : ∀ a, toK (CField.inv a) = (toK a)⁻¹
  /-- `isZero a` is `true` iff `toK a = 0`. -/
  isZero_iff : ∀ a, CField.isZero a = true ↔ toK a = 0

/-- Expose `Field (CFieldSpec.K α)` as an instance so the genuine field structure resolves. -/
instance instFieldK (α : Type*) [CField α] [CFieldSpec α] : Field (CFieldSpec.K α) :=
  CFieldSpec.instField

/-- Every `[CFieldSpec α]` is a `CRingSpec α`: the field bridge is a ring bridge with `R := K`. The hom
laws transfer by defeq through the `CField ⇒ CCommRing` bridge, so `CRingSpec.R α = CFieldSpec.K α` and
ring-level denotation squares (over `CRingSpec.R`) agree with field-level ones (over `CFieldSpec.K`) on
field coefficients. -/
instance (priority := 100) instCRingSpecOfCFieldSpec {α : Type*} [CField α] [CFieldSpec α] :
    CRingSpec α where
  R := CFieldSpec.K α
  toR := CFieldSpec.toK
  toR_zero := CFieldSpec.toK_zero
  toR_one := CFieldSpec.toK_one
  toR_add := CFieldSpec.toK_add
  toR_mul := CFieldSpec.toK_mul
  toR_neg := CFieldSpec.toK_neg
  isZero_iff := CFieldSpec.isZero_iff

/-- On a field coefficient the ring bridge IS the field bridge (`R = K`, `toR = toK`), by defeq. -/
@[simp, denote] theorem toR_eq_toK {α : Type*} [CField α] [CFieldSpec α] (a : α) :
    CRingSpec.toR a = CFieldSpec.toK a := rfl

/-! ### Field-path element normalizers
The ring-generic engine ops emit `CCommRing.zero`/`one`/… (from the weakened `[CCommRing]` definitions);
on a field coefficient these are defeq to the `CField` operations, so these `@[simp]` lemmas normalize
them back to the `CField` head that field-path call sites and their satellite lemmas are phrased in. -/

/-- Field-path: `CCommRing.zero = CField.zero`. -/
@[simp] theorem ccrZero_eq_cfield {α : Type*} [CField α] : (CCommRing.zero : α) = CField.zero := rfl
/-- Field-path: `CCommRing.one = CField.one`. -/
@[simp] theorem ccrOne_eq_cfield {α : Type*} [CField α] : (CCommRing.one : α) = CField.one := rfl
/-- Field-path: `CCommRing.add = CField.add`. -/
@[simp] theorem ccrAdd_eq_cfield {α : Type*} [CField α] (a b : α) :
    CCommRing.add a b = CField.add a b := rfl
/-- Field-path: `CCommRing.mul = CField.mul`. -/
@[simp] theorem ccrMul_eq_cfield {α : Type*} [CField α] (a b : α) :
    CCommRing.mul a b = CField.mul a b := rfl
/-- Field-path: `CCommRing.neg = CField.neg`. -/
@[simp] theorem ccrNeg_eq_cfield {α : Type*} [CField α] (a : α) :
    CCommRing.neg a = CField.neg a := rfl

/-- `CRingSpec.R α = CFieldSpec.K α`, a `Field`, so field-level squares over the ring-generic
`toPoly : DensePoly α → (CRingSpec.R α)[X]` find `⁻¹`/`GroupWithZero` on the field path. -/
instance (priority := 100) instFieldROfCFieldSpec {α : Type*} [CField α] [CFieldSpec α] :
    Field (CRingSpec.R α) := instFieldK α

-- The base `toK` homomorphism laws are the leaf denotation squares.
attribute [denote] CFieldSpec.toK_zero CFieldSpec.toK_one CFieldSpec.toK_add
  CFieldSpec.toK_mul CFieldSpec.toK_neg CFieldSpec.toK_inv

/-! ### `toK` homomorphism laws through the `CField ⇒ CCommRing` bridge
Ring-generic engine ops (`cadd`/`cmul`/… weakened to `[CCommRing]`) put `CCommRing.add`/… in goals; on a
field coefficient that is defeq to `CField.add`/…, so these `@[denote]` lemmas let the denotation squares
fire on the ring-op head. -/
@[denote] theorem toK_ccrZero {α : Type*} [CField α] [CFieldSpec α] :
    CFieldSpec.toK (CCommRing.zero : α) = 0 := CFieldSpec.toK_zero
@[denote] theorem toK_ccrOne {α : Type*} [CField α] [CFieldSpec α] :
    CFieldSpec.toK (CCommRing.one : α) = 1 := CFieldSpec.toK_one
@[denote] theorem toK_ccrAdd {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    CFieldSpec.toK (CCommRing.add a b) = CFieldSpec.toK a + CFieldSpec.toK b := CFieldSpec.toK_add a b
@[denote] theorem toK_ccrMul {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    CFieldSpec.toK (CCommRing.mul a b) = CFieldSpec.toK a * CFieldSpec.toK b := CFieldSpec.toK_mul a b
@[denote] theorem toK_ccrNeg {α : Type*} [CField α] [CFieldSpec α] (a : α) :
    CFieldSpec.toK (CCommRing.neg a) = - CFieldSpec.toK a := CFieldSpec.toK_neg a

namespace CFieldSpec

/-- `toK` intertwines derived `sub` with `-`. -/
@[denote] theorem toK_sub {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    toK (CField.sub a b) = toK a - toK b := by
  rw [CField.sub, toK_add, toK_neg, sub_eq_add_neg]

/-- `toK` intertwines derived `div` with `/`. -/
@[denote] theorem toK_div {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    toK (CField.div a b) = toK a / toK b := by
  rw [CField.div, toK_mul, toK_inv, div_eq_mul_inv]

/-- `toK` intertwines a `CField.add` fold with the corresponding field addition fold. -/
@[denote] theorem toK_foldl_add {α : Type*} [CField α] [CFieldSpec α] (z : α) (L : List α) :
    toK (L.foldl CField.add z) = (L.map toK).foldl (· + ·) (toK z) := by
  induction L generalizing z with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons, List.map_cons, ih, CFieldSpec.toK_add]

/-- `toK` reads a `CField.zero`-defaulted list lookup through `List.map toK`. -/
theorem getD_map_toK {α : Type*} [CField α] [CFieldSpec α] (l : List α) (j : ℕ) :
    (l.map toK).getD j 0 = toK (l.getD j CField.zero) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[j]? with
  | none => simp [CFieldSpec.toK_zero]
  | some a => simp

end CFieldSpec

/-! ### Instances: `CField ℚ` and `CFieldSpec ℚ`

`ℚ` as a computable field over itself: `ℚ`'s own operations, `isZero` by decidable equality, bridge
`K = ℚ`, `toK = id`. -/

/-- `CField ℚ`: rationals as a computable field with `ℚ`'s own operations and
`isZero a := decide (a = 0)`. -/
instance : CField ℚ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  isZero a := decide (a = 0)

/-- `CFieldSpec ℚ`: the trivial bridge `K = ℚ`, `toK = id`; all homomorphism laws are `rfl` and
`isZero_iff` is decidable-equality. -/
instance : CFieldSpec ℚ where
  K := ℚ
  toK := id
  toK_zero := rfl
  toK_one := rfl
  toK_add _ _ := rfl
  toK_mul _ _ := rfl
  toK_neg _ := rfl
  toK_inv _ := rfl
  isZero_iff a := by show decide (a = 0) = true ↔ id a = 0; simp

end DeepWiki.SymbolicIntegration
