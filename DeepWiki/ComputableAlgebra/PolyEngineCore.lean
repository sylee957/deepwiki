import DeepWiki.ComputableAlgebra.Field
import DeepWiki.ComputableAlgebra.PolyRepr

/-! # Core computable-polynomial engine interface

`CPolyEngine` is the Prop-free operation interface shared by every computable polynomial
representation. Concrete dense and sparse engines, together with their denotation laws, live in
`PolyEngine.lean`. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- The Prop-free polynomial-engine operations supplied by a concrete representation. -/
class CPolyEngine (P : Type u → Type u) where
  /-- Addition. -/
  add : {α : Type u} → [CCommRing α] → P α → P α → P α
  /-- Multiplication. -/
  mul : {α : Type u} → [CCommRing α] → P α → P α → P α
  /-- Negation. -/
  neg : {α : Type u} → [CCommRing α] → P α → P α
  /-- Monomial construction. -/
  monomial : {α : Type u} → [CCommRing α] → α → ℕ → P α
  /-- Enumerate the represented coefficients from degree zero through the representation bound. -/
  coeffList : {α : Type u} → [CCommRing α] → P α → List α
  /-- Build a polynomial representation from a low-to-high coefficient list. -/
  ofCoeffList : {α : Type u} → [CCommRing α] → List α → P α
  /-- Apply a coefficient function without changing the represented degree bound. -/
  mapCoeffs : {α : Type u} → [CCommRing α] → (α → α) → P α → P α
  /-- Formal derivative. -/
  deriv : {α : Type u} → [CField α] → P α → P α
  /-- Scalar multiplication. -/
  scale : {α : Type u} → [CCommRing α] → α → P α → P α
  /-- Trailing-zero-free canonical form. -/
  cnorm : {α : Type u} → [CCommRing α] → P α → P α
  /-- Zero test. -/
  cisZero : {α : Type u} → [CCommRing α] → P α → Bool
  /-- Honest degree. -/
  cdeg : {α : Type u} → [CCommRing α] → P α → ℕ
  /-- Leading coefficient. -/
  clead : {α : Type u} → [CCommRing α] → P α → α
  /-- Evaluation at a coefficient-ring value. -/
  eval : {α : Type u} → [CCommRing α] → P α → α → α

end DeepWiki.SymbolicIntegration
