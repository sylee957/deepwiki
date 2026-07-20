import DeepWiki.Refine.Poly
import DeepWiki.Refine.Goal
import DeepWiki.CAlgebra.Gcd

/-! # Transferring `gcd` up to units

Unlike `+` and `*`, the computable `DensePolyGcd.gcd` and `EuclideanDomain.gcd` agree only **up to a
unit** (`Associated`) because the raw Euclidean remainder is not normalized. Its transfer witness
therefore uses equality on the inputs and the coarser
`Associated` relation on the output; the resolver threads these mixed relations automatically. -/

open Polynomial DeepWiki.CAlgebra
open scoped DeepWiki.Refine

namespace DeepWiki.Refine

variable {R : Type*} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- The **up-to-a-unit** output relation: `toPolynomial c` is `Associated` to `a` (equal modulo a
unit), the coarser relation `gcd` respects. -/
def RPolyU : DensePoly R → Polynomial R → Prop := fun c a => Associated (toPolynomial c) a

/-- The gcd witness: **inputs** related by equality (`RPoly`), **output** related only up to a unit
(`RPolyU`). This is `toPolynomial_gcd_associated` packaged relationally — a witness whose output
relation differs from its inputs'. -/
@[refines] theorem refines_gcd :
    Refines (RPoly (R := R) ⟹ RPoly ⟹ RPolyU) DensePolyGcd.gcd EuclideanDomain.gcd := by
  derive_refines [RPoly, RPolyU] using toPolynomial_gcd_associated

/-- Manual transfer of a *compound* gcd expression, mixing relations: the arguments `p * q` and `r`
transfer at equality (`RPoly`, via the ring-op witnesses), and `gcd` combines them at the up-to-unit
relation (`RPolyU`). The kernel's `Refines.app` threads the two relations correctly — demonstrating
that `gcd` (and any such non-functional op) is expressible independently of the resolver. -/
example (p q r : DensePoly R) :
    Refines RPolyU (DensePolyGcd.gcd (p * q) r)
      (EuclideanDomain.gcd (toPolynomial p * toPolynomial q) (toPolynomial r)) :=
  Refines.app
    (Refines.app refines_gcd
      (Refines.app (Refines.app refines_mul (refines_toPolynomial p)) (refines_toPolynomial q)))
    (refines_toPolynomial r)

/-- The relation-threading resolver now does that **automatically**: `refine_transfer` transfers the
mixed-relation `gcd (p*q) r` (equality-inputs, up-to-unit-output) with one tactic call — dispatching
`gcd` at `RPolyU` and its arguments at `RPoly`, no `simp`. -/
example (p q r : DensePoly R) :
    Refines RPolyU (DensePolyGcd.gcd (p * q) r)
      (EuclideanDomain.gcd (toPolynomial p * toPolynomial q) (toPolynomial r)) := by
  refine_transfer

omit [DensePolyGcd R] in
/-- Divisibility of denotations respects refinement up to associated polynomials. -/
@[refines] theorem refines_dvd :
    Refines (RPolyU (R := R) ⟹ RPolyU ⟹ Iff)
      (fun p q : DensePoly R => toPolynomial p ∣ toPolynomial q)
      ((· ∣ ·) : Polynomial R → Polynomial R → Prop) where
  prf _ _ hp _ _ hq := by
    constructor
    · intro h
      exact hp.symm.dvd.trans (h.trans hq.dvd)
    · intro h
      exact hp.dvd.trans (h.trans hq.symm.dvd)

/-! ### Relation-hierarchy coercion: equality `⊑` up-to-a-unit -/

omit [DensePolyGcd R] in
/-- Equality implies `Associated`: `RPoly` is finer than `RPolyU`. Registering it lets the resolver
weaken any equality-level transfer to the up-to-unit level. -/
@[refines_sub] theorem subsume_RPoly_RPolyU : Subsumes (RPoly (R := R)) RPolyU := by
  intro c a h
  have h' : toPolynomial c = a := h
  subst h'
  exact Associated.refl _

/-- `refine_goal` turns the concrete divisibility goal into Mathlib's abstract gcd theorem. -/
example (p q : DensePoly R) : toPolynomial (DensePolyGcd.gcd p q) ∣ toPolynomial p := by
  refine_goal
  exact EuclideanDomain.gcd_dvd_left _ _

/-- The resolver now weakens across the hierarchy: a purely-functional term transfers **at the coarser
`RPolyU`** even though only equality-level (`RPoly`) witnesses exist — `refine_transfer` resolves it at
`RPoly` and coerces up along the subsumption. -/
example (p q : DensePoly R) :
    Refines RPolyU (p * q) (toPolynomial p * toPolynomial q) := by
  refine_transfer

end DeepWiki.Refine
