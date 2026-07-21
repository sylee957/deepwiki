import DeepWiki.CAlgebra.Resultant.Euclidean
import DeepWiki.CAlgebra.Resultant.Primitive
import DeepWiki.CAlgebra.Resultant.Subresultant
import DeepWiki.CAlgebra.Resultant.Reduced

/-! # Switchable resultant and PRS for `DensePoly`

`DensePolyResultant` packages a resultant algorithm with its contract — agreement with
Mathlib's Sylvester-determinant `Polynomial.resultant` on valid degree bounds — so consumers
depend only on the spec while instance priority selects the algorithm: the Euclidean-descent
pseudo-remainder sequence where the coefficients form a computable Euclidean domain
(polynomial-time), the Sylvester determinant as the total fallback.

`DensePolyPRS` packages a pseudo-remainder-sequence algorithm the same way: an instance is
a **clean policy with an invariant-carried strip-exactness contract**
(`C β * cleaned = pseudoMod f g` along the walk), so the dispatched sequence
`DensePolyPRS.prs` — the descent kernel's sequence projection — consists of constant
multiples of the raw pseudo-remainders; priority selects the strip (nothing, contents,
the subresultant `β` over a field, `z`-contents at polynomial coefficients). -/

namespace DeepWiki.CAlgebra

universe u

/-- A resultant algorithm together with its contract: it agrees with Mathlib's
`Polynomial.resultant` **at the canonical degree bounds** — the normalized representation
always knows the exact degrees, so no bound parameters and no side conditions. -/
class DensePolyResultant (S : Type u) [CommRing S] [DecidableEq S] where
  /-- The resultant of `p, q` (at their exact degrees). -/
  resultant : DensePoly S → DensePoly S → S
  /-- Agreement with the Sylvester-determinant resultant at the canonical bounds. -/
  resultant_eq : ∀ p q, resultant p q
    = (toPolynomial p).resultant (toPolynomial q)
        (toPolynomial p).natDegree (toPolynomial q).natDegree

/-- Default algorithm: the Sylvester determinant (total; factorial-time). -/
instance (priority := 100) {S : Type u} [CommRing S] [DecidableEq S] :
    DensePolyResultant S where
  resultant := DeepWiki.CAlgebra.resultant
  resultant_eq := toPolynomial_resultant

/-- Euclidean-descent algorithm: the pseudo-remainder sequence, where the coefficients form
a computable Euclidean domain — polynomial-time. -/
instance (priority := 200) euclideanDensePolyResultant {S : Type u} [EuclideanDomain S]
    [DecidableEq S] : DensePolyResultant S where
  resultant := DensePoly.resultantPRSEuclidean
  resultant_eq := DensePoly.resultantPRSEuclidean_eq

/-- Reduced pseudo-remainder sequence (Collins): fraction-free without content gcds — every
division exact by the discharged Brown–Traub invariant (`reducedExact_all`). -/
instance (priority := 250) reducedDensePolyResultant {S : Type u} [EuclideanDomain S]
    [DecidableEq S] : DensePolyResultant S where
  resultant := DensePoly.resultantPRSReduced
  resultant_eq := DensePoly.resultantPRSReduced_eq

/-- Primitive pseudo-remainder sequence: content-stripping keeps coefficients small — wins
the dispatch (320× over the plain descent on a degree-8 bivariate benchmark). -/
instance (priority := 300) primitiveDensePolyResultant {S : Type u} [EuclideanDomain S]
    [DecidableEq S] : DensePolyResultant S where
  resultant := DensePoly.resultantPRSPrimitive
  resultant_eq := DensePoly.resultantPRSPrimitive_eq

/-- A pseudo-remainder-sequence algorithm as a **clean policy with its contract**: the
state-threaded strip together with an invariant under which each strip is exact — the
invariant holds at entry and persists along the walk, so every element of the dispatched
sequence is a constant multiple of the raw pseudo-remainder. `DensePolyPRS.prs` is the
kernel's sequence projection under the selected policy; instance priority selects the
strip. -/
class DensePolyPRS (S : Type u) [CommRing S] [DecidableEq S] where
  /-- The policy state. -/
  State : Type u
  /-- The entry state. -/
  entry : State
  /-- The clean policy: extract a constant from each pseudo-remainder. -/
  clean : State → DensePoly S → DensePoly S → DensePoly S → S × DensePoly S × State
  /-- The cleaned remainder is no larger (feeds the kernel's termination). -/
  size_le : ∀ st f g r, (clean st f g r).2.1.size ≤ r.size
  /-- The strip invariant (`True` for stateless policies). -/
  Inv : State → Prop
  /-- The invariant holds at entry. -/
  entry_inv : Inv entry
  /-- The invariant persists across each walk step. -/
  inv_step : ∀ st f g, g.size ≠ 0 → Inv st →
    Inv (clean st f g (DensePoly.pseudoMod f g)).2.2
  /-- Under the invariant, the strip reconstructs the pseudo-remainder the walk cleans:
  `C β * cleaned = pseudoMod f g`. -/
  clean_exact : ∀ st f g, g.size ≠ 0 → Inv st →
    DensePoly.C (clean st f g (DensePoly.pseudoMod f g)).1
        * (clean st f g (DensePoly.pseudoMod f g)).2.1
      = DensePoly.pseudoMod f g

/-- The dispatched pseudo-remainder sequence: the descent kernel's sequence projection
under the selected clean policy. -/
def DensePolyPRS.prs {S : Type u} [CommRing S] [DecidableEq S] [DensePolyPRS S]
    (f g : DensePoly S) : List (DensePoly S) :=
  DensePoly.prsDescent DensePolyPRS.clean DensePolyPRS.size_le DensePolyPRS.entry f g

/-- Default policy: strip nothing (any computable commutative ring). -/
instance (priority := 100) {S : Type u} [CommRing S] [DecidableEq S] : DensePolyPRS S where
  State := PUnit
  entry := PUnit.unit
  clean := fun _ _ _ r => (1, r, PUnit.unit)
  size_le := fun _ _ _ _ => le_refl _
  Inv := fun _ => True
  entry_inv := trivial
  inv_step := fun _ _ _ _ _ => trivial
  clean_exact := fun _ _ _ _ _ => by rw [← DensePoly.one_def, one_mul]

/-- Content-stripping policy over a computable Euclidean domain: coefficients stay small
along the walk. -/
instance (priority := 200) primitiveDensePolyPRS {S : Type u} [EuclideanDomain S]
    [DecidableEq S] : DensePolyPRS S where
  State := PUnit
  entry := PUnit.unit
  clean := fun _ _ _ r => (DensePoly.polyContent r, DensePoly.polyPrimitive r, PUnit.unit)
  size_le := fun _ _ _ r => DensePoly.polyPrimitive_size_le r
  Inv := fun _ => True
  entry_inv := trivial
  inv_step := fun _ _ _ _ _ => trivial
  clean_exact := fun _ _ _ _ _ => DensePoly.C_polyContent_mul_polyPrimitive _

/-- The true subresultant policy over a field: `β = (−1)^(δ+1) · g · h^δ` with the running
`h`-value — the classical strip when the field elements are themselves big objects (tower
carriers). Exactness holds under the nonzero-state invariant. -/
instance (priority := 250) subresultantDensePolyPRS {R : Type u} [Field R] [DecidableEq R] :
    DensePolyPRS R where
  State := R × R
  entry := (1, 1)
  clean := DensePoly.cleanSubresultant
  size_le := DensePoly.cleanSubresultant_size
  Inv := fun st => st.1 ≠ 0 ∧ st.2 ≠ 0
  entry_inv := ⟨one_ne_zero, one_ne_zero⟩
  inv_step := fun st f g hg0 hI =>
    DensePoly.cleanSubresultant_step st f g (DensePoly.pseudoMod f g) hg0 hI
  clean_exact := fun st f g _ hI =>
    (DensePoly.cleanSubresultant_spec st f g (DensePoly.pseudoMod f g) hI).2

/-- `z`-content stripping at polynomial coefficients: contents through the dispatched
polynomial gcd — the sequence the Lazard–Rioboo–Trager log arguments are read off. -/
instance (priority := 300) zPrimitiveDensePolyPRS {R : Type u} [Field R] [DecidableEq R]
    [DensePolyGcd R] : DensePolyPRS (DensePoly R) where
  State := PUnit
  entry := PUnit.unit
  clean := fun _ _ _ r => (DensePoly.zContent r, DensePoly.zPrimitive r, PUnit.unit)
  size_le := fun _ _ _ r => DensePoly.zPrimitive_size_le r
  Inv := fun _ => True
  entry_inv := trivial
  inv_step := fun _ _ _ _ _ => trivial
  clean_exact := fun _ _ _ _ _ => DensePoly.C_zContent_mul_zPrimitive _

end DeepWiki.CAlgebra
