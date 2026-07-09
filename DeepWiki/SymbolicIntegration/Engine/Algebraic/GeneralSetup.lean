import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralDerivatives

/-! # Concrete setup for general algebraic-function computations

Ansatz monomials and the shared cuspidal-cubic fixture used by the general
algebraic-function computation modules. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

/-- The cuspidal cubic `f = y³ - x² ∈ ℚ(x)[y]`. -/
def gcuspCubicF : CPoly (QFunNZG ℚ) :=
  [qxOfNum [0, 0, -1], CField.zero, CField.zero, CField.one]

/-- The generator `y` of `ℚ(x)[y]/(y³ - x²)`. -/
def gcuspCubicY : CPoly (QFunNZG ℚ) := afBasisElem 1

/-- The element `y²` of `ℚ(x)[y]/(y³ - x²)`. -/
def gcuspCubicYsq : CPoly (QFunNZG ℚ) := afBasisElem 2

/-- A `ℚ(x)` value `xᵏ`, used as an ansatz scalar. -/
def qxMon (k : ℕ) : QFunNZG ℚ := qxOfNum (cshift k [(1 : ℚ)])

/-- The ansatz monomials `xʲ * wᵢ` over an integral basis. -/
def afRatMonomials (basis : List (CPoly (QFunNZG ℚ))) (degBound : ℕ) :
    List (CPoly (QFunNZG ℚ)) :=
  basis.flatMap (fun wi =>
    (List.range (degBound + 1)).map (fun j => cscale (qxMon j) wi))

/-- The integral basis of the cuspidal cubic `y³ = x²`. -/
def gcuspCubicBasis : List (CPoly (QFunNZG ℚ)) := integralBasis gcuspCubicF

end DeepWiki.SymbolicIntegration
