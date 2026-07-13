import DeepWiki.Refine.Resolve
import DeepWiki.CAlgebra.Poly.Operations

/-! # Refinement witnesses for `DensePoly R ⇄ Polynomial R`

The per-operation abstraction lemmas (as `Refines` instances) for the functional refinement
`toPolynomial c = a`. Each is the relational form of a denotation homomorphism square. A term built
from these operations then transfers to its `Polynomial` denotation by chaining `Refines.app` — the
principled relational resolution (demonstrated manually here; automated by the resolver layer). -/

open Polynomial DeepWiki.CAlgebra
open scoped DeepWiki.Refine

namespace DeepWiki.Refine

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- The refinement relation: a dense polynomial refines its Mathlib denotation. -/
def RPoly : DensePoly R → Polynomial R → Prop := DenoteRel toPolynomial

/-- A dense polynomial refines its own denotation (leaf rule). -/
theorem refines_toPolynomial (p : DensePoly R) : Refines RPoly p (toPolynomial p) :=
  refines_denote _ p

/-- Multiplication respects refinement. -/
@[refines] instance refines_mul : Refines (RPoly (R := R) ⟹ RPoly ⟹ RPoly) (· * ·) (· * ·) where
  prf c a hca c' a' hc'a' := by
    have hca : toPolynomial c = a := hca
    have hc'a' : toPolynomial c' = a' := hc'a'
    show toPolynomial (c * c') = a * a'
    rw [toPolynomial_mul, hca, hc'a']

/-- Addition respects refinement. -/
@[refines] instance refines_add : Refines (RPoly (R := R) ⟹ RPoly ⟹ RPoly) (· + ·) (· + ·) where
  prf c a hca c' a' hc'a' := by
    have hca : toPolynomial c = a := hca
    have hc'a' : toPolynomial c' = a' := hc'a'
    show toPolynomial (c + c') = a + a'
    rw [toPolynomial_add, hca, hc'a']

/-- Subtraction respects refinement. -/
@[refines] instance refines_sub : Refines (RPoly (R := R) ⟹ RPoly ⟹ RPoly) (· - ·) (· - ·) where
  prf c a hca c' a' hc'a' := by
    have hca : toPolynomial c = a := hca
    have hc'a' : toPolynomial c' = a' := hc'a'
    show toPolynomial (c - c') = a - a'
    rw [toPolynomial_sub, hca, hc'a']

/-- Negation respects refinement. -/
@[refines] instance refines_neg : Refines (RPoly (R := R) ⟹ RPoly) (- ·) (- ·) where
  prf c a hca := by
    have hca : toPolynomial c = a := hca
    show toPolynomial (-c) = -a
    rw [toPolynomial_neg, hca]

/-- The resolver AUTOMATES the transfer: `refine_transfer` synthesizes the abstract `Polynomial`
denotation of the compound `(p + q) * r - s` and its proof — by `isDefEq`-driven relational
composition of the `@[refines]` witnesses, no `simp`. This one tactic replaces the hand-written
`Refines.app` tree. -/
example (p q r s : DensePoly R) :
    Refines RPoly ((p + q) * r - s)
      ((toPolynomial p + toPolynomial q) * toPolynomial r - toPolynomial s) := by
  refine_transfer

/-- A deeper term transfers just as automatically. -/
example (p q : DensePoly R) :
    Refines RPoly (-((p * q) + p) - (q - p))
      (-((toPolynomial p * toPolynomial q) + toPolynomial p) - (toPolynomial q - toPolynomial p)) := by
  refine_transfer

end DeepWiki.Refine
