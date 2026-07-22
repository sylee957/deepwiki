import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.Derivation.DifferentialRing

/-! # The formal polynomial derivative

The formal derivative as an opt-in differential structure on polynomial rings.
-/

universe u

namespace FormalDiff

/-- The formal derivative as an opt-in differential structure on `Polynomial R`. -/
noncomputable scoped instance {R : Type u} [CommRing R] : Differential (Polynomial R) :=
  ⟨(Polynomial.derivative' (R := R)).restrictScalars ℤ⟩

end FormalDiff

namespace DeepWiki.SymbolicIntegration

open scoped Differential FormalDiff

/-- Under `FormalDiff`, `q′` is `Polynomial.derivative q`. -/
@[simp] theorem polynomial_differential_apply {R : Type u} [CommRing R] (q : Polynomial R) :
    q′ = Polynomial.derivative q := rfl

end DeepWiki.SymbolicIntegration
