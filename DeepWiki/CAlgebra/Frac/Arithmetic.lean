import DeepWiki.CAlgebra.Frac.Dense

/-! # Rational-function arithmetic (multiplicative) — carrier ops

`mul`/`one` on `DenseFrac`. The `toRatFunc` homomorphism squares live in `FracBridge/Basic.lean`. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

namespace DenseFrac

/-- Rational-function multiplication: multiply numerators and denominators. -/
def mul (f g : DenseFrac R) : DenseFrac R := ⟨f.num * g.num, f.den * g.den⟩

instance : Mul (DenseFrac R) where mul := mul

/-- The multiplicative unit `1/1`. -/
instance : One (DenseFrac R) where one := ⟨1, 1⟩

theorem mul_def (f g : DenseFrac R) : f * g = ⟨f.num * g.num, f.den * g.den⟩ := rfl

end DenseFrac

end DeepWiki.CAlgebra
