import DeepWiki.Refine.Poly
import DeepWiki.CAlgebra.Poly.Euclid

/-! # Transferring `gcd` — the non-functional (up-to-unit) case

`gcd` is the interesting frontier: unlike `+`/`*`, the computable `DensePoly.gcd` and Mathlib's
`EuclideanDomain.gcd` agree only **up to a unit** (`Associated`), because the raw Euclidean remainder
isn't normalized. So its transfer witness lives at a *weaker output relation* than equality — exactly
the general-relation case CoqEAL/Trocq exist for. The `Refine` **kernel** composes it fine (the
`⟹`/`Refines.app` machinery threads a different relation on the output than on the inputs); only the
current auto-resolver, specialized to a single functional relation, cannot yet dispatch it. -/

open Polynomial DeepWiki.CAlgebra
open scoped DeepWiki.Refine

namespace DeepWiki.Refine

variable {R : Type*} [Field R] [DecidableEq R]

/-- The **up-to-a-unit** output relation: `toPolynomial c` is `Associated` to `a` (equal modulo a
unit), the coarser relation `gcd` respects. -/
def RPolyU : DensePoly R → Polynomial R → Prop := fun c a => Associated (toPolynomial c) a

/-- The gcd witness: **inputs** related by equality (`RPoly`), **output** related only up to a unit
(`RPolyU`). This is `toPolynomial_gcd_associated` packaged relationally — a witness whose output
relation differs from its inputs', which the functional resolver can't produce but the kernel accepts. -/
@[refines] theorem refines_gcd :
    Refines (RPoly (R := R) ⟹ RPoly ⟹ RPolyU) DensePoly.gcd EuclideanDomain.gcd where
  prf c a hca c' a' hc'a' := by
    have hca : toPolynomial c = a := hca
    have hc'a' : toPolynomial c' = a' := hc'a'
    show Associated (toPolynomial (DensePoly.gcd c c')) (EuclideanDomain.gcd a a')
    rw [← hca, ← hc'a']
    exact toPolynomial_gcd_associated c c'

/-- Manual transfer of a *compound* gcd expression, mixing relations: the arguments `p * q` and `r`
transfer at equality (`RPoly`, via the ring-op witnesses), and `gcd` combines them at the up-to-unit
relation (`RPolyU`). The kernel's `Refines.app` threads the two relations correctly — demonstrating
that `gcd` (and any such non-functional op) is expressible; automating it is the resolver's next step. -/
example (p q r : DensePoly R) :
    Refines RPolyU (DensePoly.gcd (p * q) r)
      (EuclideanDomain.gcd (toPolynomial p * toPolynomial q) (toPolynomial r)) :=
  Refines.app
    (Refines.app refines_gcd
      (Refines.app (Refines.app refines_mul (refines_toPolynomial p)) (refines_toPolynomial q)))
    (refines_toPolynomial r)

/-- The relation-threading resolver now does that **automatically**: `refine_transfer` transfers the
mixed-relation `gcd (p*q) r` (equality-inputs, up-to-unit-output) with one tactic call — dispatching
`gcd` at `RPolyU` and its arguments at `RPoly`, no `simp`. -/
example (p q r : DensePoly R) :
    Refines RPolyU (DensePoly.gcd (p * q) r)
      (EuclideanDomain.gcd (toPolynomial p * toPolynomial q) (toPolynomial r)) := by
  refine_transfer

/-- And the payoff shape: a fact about the *abstract* gcd transfers to the *computable* one, up to a
unit — e.g. divisibility (which is `Associated`-invariant). -/
example (p q : DensePoly R) : toPolynomial (DensePoly.gcd p q) ∣ toPolynomial p :=
  (refines_gcd.prf p (toPolynomial p) rfl q (toPolynomial q) rfl).dvd.trans
    (EuclideanDomain.gcd_dvd_left _ _)

/-! ### Relation-hierarchy coercion: equality `⊑` up-to-a-unit -/

/-- Equality implies `Associated`: `RPoly` is finer than `RPolyU`. Registering it lets the resolver
weaken any equality-level transfer to the up-to-unit level. -/
@[refines_sub] theorem subsume_RPoly_RPolyU : Subsumes (RPoly (R := R)) RPolyU := by
  intro c a h
  have h' : toPolynomial c = a := h
  subst h'
  exact Associated.refl _

/-- The resolver now weakens across the hierarchy: a purely-functional term transfers **at the coarser
`RPolyU`** even though only equality-level (`RPoly`) witnesses exist — `refine_transfer` resolves it at
`RPoly` and coerces up along the subsumption. -/
example (p q : DensePoly R) :
    Refines RPolyU (p * q) (toPolynomial p * toPolynomial q) := by
  refine_transfer

end DeepWiki.Refine
