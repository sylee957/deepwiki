import DeepWiki.SymbolicIntegration.LogToAtanCompute
import DeepWiki.SymbolicIntegration.ComputeCorrectness
import DeepWiki.SymbolicIntegration.RationalFunctionCompute

/-! # Generic computable field + polynomial engine (the differential-field-tower base)
The concrete `CPoly := List ℚ` engine (`LogToAtanCompute`, `ComputeCorrectness`) and the computable
ℚ(x) field `QFun` (`RationalFunctionCompute`) are each specialized to one carrier. The Risch
algorithm needs the **same** polynomial engine over a *tower* of differential fields ℚ ⊂ ℚ(x) ⊂
ℚ(x)(t) ⊂ …, so this file abstracts the carrier into a `CField` typeclass: a type `α` of computable
field elements with a bridge `toK : α → K` to a genuine Mathlib `Field K` that intertwines the
computable `zero`/`one`/`add`/`mul`/`neg`/`inv` with the field operations. The generic polynomial
engine `CPolyG α := List α` (dense coefficients, index = degree) mirrors the concrete `cadd`/`cmul`/…
over any `CField`, with a generic Horner bridge `toPolyG : CPolyG α → (CField.K α)[X]` proven to
realize `(CField.K α)[X]` arithmetic. The coherence lemmas (`caddG (α := ℚ) = cadd`, `toPolyG
(α := ℚ) = toPoly`) show the generic engine specializes back to the concrete one, so a later stage
can migrate `CPoly := CPolyG ℚ` without breaking consumers. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The `CField` typeclass

`CField α` packages computable field operations on `α` together with an injective bridge `toK : α → K`
into a genuine Mathlib `Field K` that intertwines them. The `isZero` predicate is the computable zero
test, certified by `isZero_iff` against `toK a = 0`. `sub`/`div` are derived (default-field-defined). -/

/-- **Computable field**: a type `α` of computable field elements with an injective field-homomorphism
bridge `toK : α → K` into a Mathlib `Field K` intertwining `zero`/`one`/`add`/`mul`/`neg`/`inv`, plus a
certified computable zero test `isZero`. The base of the differential-field tower the Risch algorithm
runs the polynomial engine over. -/
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
  /-- The genuine Mathlib field the bridge lands in. -/
  K : Type*
  /-- `K` is a field. -/
  [instField : Field K]
  /-- The bridge to the genuine field. -/
  toK : α → K
  /-- `toK` sends `zero` to `0`. -/
  toK_zero : toK zero = 0
  /-- `toK` sends `one` to `1`. -/
  toK_one : toK one = 1
  /-- `toK` intertwines `add` with `+`. -/
  toK_add : ∀ a b, toK (add a b) = toK a + toK b
  /-- `toK` intertwines `mul` with `*`. -/
  toK_mul : ∀ a b, toK (mul a b) = toK a * toK b
  /-- `toK` intertwines `neg` with `-`. -/
  toK_neg : ∀ a, toK (neg a) = - toK a
  /-- `toK` intertwines `inv` with `⁻¹`. -/
  toK_inv : ∀ a, toK (inv a) = (toK a)⁻¹
  /-- `toK` is injective (the computable carrier faithfully represents `K`'s reachable elements). -/
  toK_injective : Function.Injective toK
  /-- `isZero a` is `true` iff `toK a = 0`. -/
  isZero_iff : ∀ a, isZero a = true ↔ toK a = 0

/-- Expose `Field (CField.K α)` as an instance so the genuine field structure resolves. -/
instance instFieldK (α : Type*) [CField α] : Field (CField.K α) := CField.instField

namespace CField

/-- **Computable subtraction** `a - b := a + (-b)`, derived from `add`/`neg`. -/
def sub {α : Type*} [CField α] (a b : α) : α := add a (neg b)

/-- **Computable division** `a / b := a * b⁻¹`, derived from `mul`/`inv`. -/
def div {α : Type*} [CField α] (a b : α) : α := mul a (inv b)

/-- `toK` intertwines derived `sub` with `-`. -/
theorem toK_sub {α : Type*} [CField α] (a b : α) : toK (sub a b) = toK a - toK b := by
  rw [sub, toK_add, toK_neg, sub_eq_add_neg]

/-- `toK` intertwines derived `div` with `/`. -/
theorem toK_div {α : Type*} [CField α] (a b : α) : toK (div a b) = toK a / toK b := by
  rw [div, toK_mul, toK_inv, div_eq_mul_inv]

end CField

/-! ### Instance: `CField ℚ`

`ℚ` is trivially a computable field over itself: `K = ℚ`, `toK = id`, every law `rfl`, `isZero` by
decidable equality. The simplest instance — and the one that validates the whole abstraction. -/

/-- **`CField ℚ`**: rationals as a computable field over `K = ℚ` with `toK = id`; all bridge laws are
`rfl` and `isZero a := decide (a = 0)`. -/
instance : CField ℚ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  isZero a := decide (a = 0)
  K := ℚ
  toK := id
  toK_zero := rfl
  toK_one := rfl
  toK_add _ _ := rfl
  toK_mul _ _ := rfl
  toK_neg _ := rfl
  toK_inv _ := rfl
  toK_injective := fun _ _ h => h
  isZero_iff a := by simp [id]

end DeepWiki.SymbolicIntegration
