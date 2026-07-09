import Mathlib.Algebra.Ring.Basic
import DeepWiki.Transfer.Denote

/-! # Computable commutative rings (`CCommRing`) and their denotation spec (`CRingSpec`)

`CCommRing α`: computable commutative-ring operations (`zero`/`one`/`add`/`mul`/`neg`, zero test),
bridge-free so instances reduce under `native_decide`. `CRingSpec α`: the companion homomorphism
`toR : α → R` into a Mathlib `CommRing R` with intertwining laws — the target of the ring-generic
polynomial denotation. The field layer (`CField`/`CFieldSpec`) is built on top in `Field.lean`. -/

namespace DeepWiki.SymbolicIntegration

/-! ### The `CCommRing` typeclass (computable commutative-ring operations)

`CCommRing α` is the ring fragment of `CField` (no `inv`): the coefficient constraint the ring-generic
polynomial engine actually needs (20 of the 21 core `c*` ops use only these). Every `CField` is a
`CCommRing` (bridge instance below), and a `DensePoly` over a `CCommRing` is itself a `CCommRing`, so
bivariate polynomials are just `DensePoly (DensePoly _)`. See `docs/ring-generalization-plan.md`. -/

/-- Computable commutative-ring operations: `zero`/`one`/`add`/`mul`/`neg` and a zero test `isZero`;
bridge-free, so instances reduce in the native compiler (`native_decide`). -/
class CCommRing (α : Type*) where
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
  /-- Computable zero test. -/
  isZero : α → Bool

namespace CCommRing

/-- Computable subtraction `a - b := a + (-b)`, derived from `add`/`neg`. -/
def sub {α : Type*} [CCommRing α] (a b : α) : α := add a (neg b)

end CCommRing

/-- Computable-commutative-ring specification: the bridge `toR : α → R` into a Mathlib `CommRing R`
intertwining `zero`/`one`/`add`/`mul`/`neg`, plus `isZero_iff`. The ring analogue of `CFieldSpec`; the
ring-generic denotation `toPoly : DensePoly α → (CRingSpec.R α)[X]` lands in this `CommRing`. -/
class CRingSpec (α : Type*) [CCommRing α] where
  /-- The genuine Mathlib commutative ring the bridge lands in. -/
  R : Type*
  /-- `R` is a commutative ring. -/
  [instCommRing : CommRing R]
  /-- The bridge to the genuine ring. -/
  toR : α → R
  /-- `toR` sends `zero` to `0`. -/
  toR_zero : toR CCommRing.zero = 0
  /-- `toR` sends `one` to `1`. -/
  toR_one : toR CCommRing.one = 1
  /-- `toR` intertwines `add` with `+`. -/
  toR_add : ∀ a b, toR (CCommRing.add a b) = toR a + toR b
  /-- `toR` intertwines `mul` with `*`. -/
  toR_mul : ∀ a b, toR (CCommRing.mul a b) = toR a * toR b
  /-- `toR` intertwines `neg` with `-`. -/
  toR_neg : ∀ a, toR (CCommRing.neg a) = - toR a
  /-- `isZero a` is `true` iff `toR a = 0`. -/
  isZero_iff : ∀ a, CCommRing.isZero a = true ↔ toR a = 0

/-- Expose `CommRing (CRingSpec.R α)` so the polynomial ring `(CRingSpec.R α)[X]` resolves. -/
instance (priority := 50) instCommRingR (α : Type*) [CCommRing α] [CRingSpec α] :
    CommRing (CRingSpec.R α) :=
  CRingSpec.instCommRing

-- The ring bridge laws are the leaf denotation squares.
attribute [denote] CRingSpec.toR_zero CRingSpec.toR_one CRingSpec.toR_add
  CRingSpec.toR_mul CRingSpec.toR_neg

end DeepWiki.SymbolicIntegration
