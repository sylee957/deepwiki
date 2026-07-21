import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Derivation.DifferentialRing

/-! # The formal derivative as a scoped `Differential` structure on `Polynomial`

`Polynomial.derivative` packaged as a `Derivation ℤ` and a **scoped** `Differential`
instance: the formal derivative treats the coefficients as constants, which is one of
several derivations a polynomial ring supports (a differential coefficient ring induces an
extension derivation instead). Opting in via `open scoped FormalDiff` keeps the two from
ever meeting in one instance space. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R]

/-- `Polynomial.derivative` as a `ℤ`-derivation. -/
noncomputable def polynomialDerivation : Derivation ℤ (Polynomial R) (Polynomial R) where
  toLinearMap := (Polynomial.derivative (R := R)).toAddMonoidHom.toIntLinearMap
  map_one_eq_zero' := Polynomial.derivative_one
  leibniz' a b := by
    show Polynomial.derivative (a * b) = a • Polynomial.derivative b + b • Polynomial.derivative a
    rw [Polynomial.derivative_mul, smul_eq_mul, smul_eq_mul]; ring

end DeepWiki.CAlgebra

namespace FormalDiff

/-- The formal derivative as the differential structure of `Polynomial R` (scoped: coefficients
are treated as constants — open `FormalDiff` to use it). -/
noncomputable scoped instance {R : Type u} [CommRing R] :
    Differential (Polynomial R) := ⟨DeepWiki.CAlgebra.polynomialDerivation⟩

end FormalDiff

namespace DeepWiki.CAlgebra

variable {R : Type u} [CommRing R]

open scoped Differential FormalDiff

/-- The scoped `′` on `Polynomial R` is `Polynomial.derivative`. -/
@[simp] theorem polynomial_differential_apply (q : Polynomial R) :
    q′ = Polynomial.derivative q := rfl

end DeepWiki.CAlgebra
