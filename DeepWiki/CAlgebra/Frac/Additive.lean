import DeepWiki.CAlgebra.Frac.Arithmetic

/-! # Rational-function arithmetic (additive + inverse) — carrier ops

`neg`/`inv`/`add` on `DenseFrac`. The `toRatFunc` homomorphism squares live in
`FracBridge/Basic.lean`. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

namespace DenseFrac

/-- Rational-function negation: negate the numerator. -/
def neg (f : DenseFrac R) : DenseFrac R := ⟨-f.num, f.den⟩

instance : Neg (DenseFrac R) where neg := neg

theorem neg_def (f : DenseFrac R) : -f = ⟨-f.num, f.den⟩ := rfl

/-- Rational-function inverse: swap numerator and denominator. -/
def inv (f : DenseFrac R) : DenseFrac R := ⟨f.den, f.num⟩

instance : Inv (DenseFrac R) where inv := inv

theorem inv_def (f : DenseFrac R) : f⁻¹ = ⟨f.den, f.num⟩ := rfl

/-- Rational-function addition by cross-multiplication. -/
def add (f g : DenseFrac R) : DenseFrac R := ⟨f.num * g.den + g.num * f.den, f.den * g.den⟩

instance : Add (DenseFrac R) where add := add

theorem add_def (f g : DenseFrac R) :
    f + g = ⟨f.num * g.den + g.num * f.den, f.den * g.den⟩ := rfl

end DenseFrac

end DeepWiki.CAlgebra
