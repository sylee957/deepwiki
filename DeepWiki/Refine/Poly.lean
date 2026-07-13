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

-- The functional-denotation leaf (any atom refines its denotation): the default leaf rule, registered
-- here so the resolver core stays free of a hardcoded base relation.
attribute [refines_leaf] refines_denote

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- The refinement relation: a dense polynomial refines its Mathlib denotation. -/
def RPoly : DensePoly R → Polynomial R → Prop := DenoteRel toPolynomial

/-- A dense polynomial refines its own denotation (leaf rule). -/
theorem refines_toPolynomial (p : DensePoly R) : Refines RPoly p (toPolynomial p) :=
  refines_denote _ p

/-- Multiplication respects refinement. -/
@[refines] instance refines_mul : Refines (RPoly (R := R) ⟹ RPoly ⟹ RPoly) (· * ·) (· * ·) := by
  derive_refines [RPoly] using toPolynomial_mul

/-- Addition respects refinement. -/
@[refines] instance refines_add : Refines (RPoly (R := R) ⟹ RPoly ⟹ RPoly) (· + ·) (· + ·) := by
  derive_refines [RPoly] using toPolynomial_add

/-- Subtraction respects refinement. -/
@[refines] instance refines_sub : Refines (RPoly (R := R) ⟹ RPoly ⟹ RPoly) (· - ·) (· - ·) := by
  derive_refines [RPoly] using toPolynomial_sub

/-- Negation respects refinement. -/
@[refines] instance refines_neg : Refines (RPoly (R := R) ⟹ RPoly) (- ·) (- ·) := by
  derive_refines [RPoly] using toPolynomial_neg

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

/-- The resolver transfers underneath a lambda by introducing a related pair of local variables. -/
example : Refines (RPoly (R := R) ⟹ RPoly) (fun p => p + p)
    (fun p => p + p) := by
  refine_transfer

/-- Nested lambdas use one explicit local refinement entry per binder. -/
example : Refines (RPoly (R := R) ⟹ RPoly ⟹ RPoly) (fun p q => p * q + p)
    (fun p q => p * q + p) := by
  refine_transfer

end DeepWiki.Refine
