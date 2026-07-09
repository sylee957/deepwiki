import DeepWiki.ComputableAlgebra.CommRing
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat

/-! # Computable fields (`CField`) and the field-homomorphism spec (`CFieldSpec`)

`CField α`: computable field operations (`zero`/`one`/`add`/`mul`/`neg`/`inv`, zero test), bridge-free
so instances stay computable; every `CField` is a `CCommRing` (bridge below). `CFieldSpec α`: the
companion homomorphism `toK : α → K` into a Mathlib `Field K` (a `CRingSpec` with `R = K`). `ℚ` is the
base instance. See `CommRing.lean` for the ring layer and `PolyReprDense.lean` for the `DensePoly`
engine. -/

namespace DeepWiki.SymbolicIntegration

/-! ### The `CField` typeclass (computable operations only)

`CField α`: the computable field operations plus zero test, bridge-free so instances stay
computable; correctness proofs add `[CFieldSpec α]`. -/

/-- Computable field: a computable commutative ring plus a computable inverse (`0⁻¹ = 0`). Extends
`CCommRing`, so the ring operations (`zero`/`one`/`add`/`mul`/`neg`/`isZero`) are inherited and
`[CCommRing α]` resolves at every `[CField α]` automatically (no manual bridge). Bridge-free, so
instances stay computable. -/
class CField (α : Type*) extends CCommRing α where
  /-- Computable inverse (`0⁻¹ = 0`). -/
  inv : α → α

namespace CField

/-- Computable subtraction `a - b := a + (-b)`, derived from the ring `add`/`neg`. -/
def sub {α : Type*} [CField α] (a b : α) : α := CCommRing.add a (CCommRing.neg b)

/-- Computable division `a / b := a * b⁻¹`, derived from `mul`/`inv`. -/
def div {α : Type*} [CField α] (a b : α) : α := CCommRing.mul a (inv b)

end CField

/-! ### The `CFieldSpec` typeclass (the field-homomorphism bridge)

`CFieldSpec α`: the noncomputable bridge `toK : α → K` into a Mathlib `Field K` intertwining the
`CField` operations, with `isZero_iff` certifying the zero test; `toK` need not be injective. -/

/-- Computable-field specification: the bridge `toK : α → K` into a Mathlib `Field K` intertwining
`zero`/`one`/`add`/`mul`/`neg`/`inv`, plus `isZero_iff` certifying `CCommRing.isZero`. -/
class CFieldSpec (α : Type*) [CField α] where
  /-- The genuine Mathlib field the bridge lands in. -/
  K : Type*
  /-- `K` is a field. -/
  [instField : Field K]
  /-- The bridge to the genuine field. -/
  toK : α → K
  /-- `toK` sends `zero` to `0`. -/
  toK_zero : toK CCommRing.zero = 0
  /-- `toK` sends `one` to `1`. -/
  toK_one : toK CCommRing.one = 1
  /-- `toK` intertwines `add` with `+`. -/
  toK_add : ∀ a b, toK (CCommRing.add a b) = toK a + toK b
  /-- `toK` intertwines `mul` with `*`. -/
  toK_mul : ∀ a b, toK (CCommRing.mul a b) = toK a * toK b
  /-- `toK` intertwines `neg` with `-`. -/
  toK_neg : ∀ a, toK (CCommRing.neg a) = - toK a
  /-- `toK` intertwines `inv` with `⁻¹`. -/
  toK_inv : ∀ a, toK (CField.inv a) = (toK a)⁻¹
  /-- `isZero a` is `true` iff `toK a = 0`. -/
  isZero_iff : ∀ a, CCommRing.isZero a = true ↔ toK a = 0

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

/-- `CRingSpec.R α = CFieldSpec.K α`, a `Field`, so field-level squares over the ring-generic
`toPoly : DensePoly α → (CRingSpec.R α)[X]` find `⁻¹`/`GroupWithZero` on the field path. -/
instance (priority := 100) instFieldROfCFieldSpec {α : Type*} [CField α] [CFieldSpec α] :
    Field (CRingSpec.R α) := instFieldK α

-- The base `toK` homomorphism laws (over the inherited ring ops) are the leaf denotation squares.
attribute [denote] CFieldSpec.toK_zero CFieldSpec.toK_one CFieldSpec.toK_add
  CFieldSpec.toK_mul CFieldSpec.toK_neg CFieldSpec.toK_inv

namespace CFieldSpec

/-- `toK` intertwines derived `sub` with `-`. -/
@[denote] theorem toK_sub {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    toK (CField.sub a b) = toK a - toK b := by
  rw [CField.sub, toK_add, toK_neg, sub_eq_add_neg]

/-- `toK` intertwines derived `div` with `/`. -/
@[denote] theorem toK_div {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    toK (CField.div a b) = toK a / toK b := by
  rw [CField.div, toK_mul, toK_inv, div_eq_mul_inv]

/-- `toK` intertwines a `CCommRing.add` fold with the corresponding field addition fold. -/
@[denote] theorem toK_foldl_add {α : Type*} [CField α] [CFieldSpec α] (z : α) (L : List α) :
    toK (L.foldl CCommRing.add z) = (L.map toK).foldl (· + ·) (toK z) := by
  induction L generalizing z with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons, List.map_cons, ih, CFieldSpec.toK_add]

/-- `toK` reads a `CCommRing.zero`-defaulted list lookup through `List.map toK`. -/
theorem getD_map_toK {α : Type*} [CField α] [CFieldSpec α] (l : List α) (j : ℕ) :
    (l.map toK).getD j 0 = toK (l.getD j CCommRing.zero) := by
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
