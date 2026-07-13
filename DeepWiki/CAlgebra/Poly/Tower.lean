import DeepWiki.CAlgebra.Poly.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Tower iteration (concrete depth-2 validation)

The `CommRing (DensePoly R)` instance lets the normalized dense representation stack: `DensePoly`
over `DensePoly` over a base is again a `CommRing`, and the ring iso composes level by level with
`Polynomial.mapEquiv`. This validates that the tower construction `ℚ → ℚ[t₁] → ℚ[t₁][t₂] → …` iterates
with a bridge to the iterated Mathlib `Polynomial`. The generic depth-`n` carrier with recursive
instances (the known instance-recursion plumbing) is a later sub-phase. -/

open Polynomial

namespace DeepWiki.CAlgebra

/-- The depth-2 tower carrier is a commutative ring by iterating the `DensePoly` `CommRing`
instance (the instance is noncomputable — auxiliary ops route through the bridge — so it is exhibited
as a `Nonempty` witness rather than compiled as data). -/
example : Nonempty (CommRing (DensePoly (DensePoly ℚ))) := ⟨inferInstance⟩

/-- The depth-2 dense tower is ring-equivalent to the iterated Mathlib polynomial ring `ℚ[X][X]`,
composing the level-2 iso with `Polynomial.mapEquiv` of the level-1 iso. -/
noncomputable def equivTower2 : DensePoly (DensePoly ℚ) ≃+* Polynomial (Polynomial ℚ) :=
  (equiv (R := DensePoly ℚ)).trans (Polynomial.mapEquiv (equiv (R := ℚ)))

/-- Validation: the tower bridge is a genuine ring isomorphism onto the iterated polynomial ring. -/
example : Function.Bijective (equivTower2) := equivTower2.bijective

end DeepWiki.CAlgebra
