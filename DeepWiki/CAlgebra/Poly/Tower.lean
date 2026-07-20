import DeepWiki.CAlgebra.Poly.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Tower iteration (depth-2)

The `CommRing (DensePoly R)` instance lets the normalized dense representation stack: `DensePoly`
over `DensePoly` over any coefficient ring is again a `CommRing`, and the ring iso composes level by
level with `Polynomial.mapEquiv`, passing through the mixed midpoint `Polynomial (DensePoly R)`.
This gives the tower construction `R → R[t₁] → R[t₁][t₂] → …` a bridge to the iterated Mathlib
`Polynomial` at every coefficient ring. The generic depth-`n` carrier with recursive instances (the
known instance-recursion plumbing) is a later sub-phase. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- The depth-2 tower carrier is a commutative ring by iterating the computable `DensePoly`
`CommRing` instance. -/
example : CommRing (DensePoly (DensePoly R)) := inferInstance

/-- The depth-2 dense tower is ring-equivalent to the iterated Mathlib polynomial ring, composing
the level-2 iso (into the mixed carrier `Polynomial (DensePoly R)`) with `Polynomial.mapEquiv` of
the level-1 iso. -/
noncomputable def equivTower2 : DensePoly (DensePoly R) ≃+* Polynomial (Polynomial R) :=
  (equiv (R := DensePoly R)).trans (Polynomial.mapEquiv (equiv (R := R)))

/-- Validation: the tower bridge is a genuine ring isomorphism onto the iterated polynomial ring. -/
example : Function.Bijective (equivTower2 (R := R)) := equivTower2.bijective

/-- Validation: the bridge instantiates at a concrete carrier (`ℚ`). -/
example : Function.Bijective (equivTower2 (R := ℚ)) := equivTower2.bijective

end DeepWiki.CAlgebra
