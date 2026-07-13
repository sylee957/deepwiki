import DeepWiki.CAlgebra.Matrix.Sylvester

/-! # Resultant via the Sylvester determinant

`resultant p q m n` is the determinant of the computable Sylvester matrix. Since Mathlib *defines*
`Polynomial.resultant` as exactly that determinant, the bridge `toPolynomial_resultant` is nearly
definitional — the work was the Sylvester matrix correspondence (Phase 3b). A fraction-free Bareiss
determinant is a later efficiency-only sub-phase; correctness needs only this. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- The resultant of `p, q` (block widths `m` for `p`, `n` for `q`): the Sylvester determinant. -/
def resultant (p q : DensePoly R) (m n : Nat) : R :=
  ((sylvester p q m n).toMatrix (m + n) (m + n)).det

/-- The computable resultant bridges to Mathlib's `Polynomial.resultant`. -/
theorem toPolynomial_resultant (p q : DensePoly R) (m n : Nat) :
    resultant p q m n = (toPolynomial p).resultant (toPolynomial q) m n := by
  rw [resultant, toMatrix_sylvester]
  rfl

/-- Validation: the computable resultant equals the Mathlib resultant of the bridged polynomials. -/
example (p q : DensePoly R) (m n : Nat) :
    resultant p q m n = Polynomial.resultant (toPolynomial p) (toPolynomial q) m n :=
  toPolynomial_resultant p q m n

end DeepWiki.CAlgebra
