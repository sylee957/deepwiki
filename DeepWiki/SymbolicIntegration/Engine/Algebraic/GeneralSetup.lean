import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralDerivatives

/-! # Concrete setup for general algebraic-function computations

Ansatz monomials and the shared cuspidal-cubic fixture used by the general
algebraic-function computation modules. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- The cuspidal cubic `f = y³ - x² ∈ ℚ(x)[y]`. -/
def gcuspCubicF : DensePoly (CFrac ℚ) :=
  [CFrac.ofPoly [0, 0, -1], CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- The generator `y` of `ℚ(x)[y]/(y³ - x²)`. -/
def gcuspCubicY : DensePoly (CFrac ℚ) := afBasisElem 1

/-- The element `y²` of `ℚ(x)[y]/(y³ - x²)`. -/
def gcuspCubicYsq : DensePoly (CFrac ℚ) := afBasisElem 2

/-- A `ℚ(x)` value `xᵏ`, used as an ansatz scalar. -/
def qxMon (k : ℕ) : CFrac ℚ := CFrac.ofPoly (cshift k [(1 : ℚ)])

/-- The ansatz monomials `xʲ * wᵢ` over an integral basis. -/
def afRatMonomials (basis : List (DensePoly (CFrac ℚ))) (degBound : ℕ) :
    List (DensePoly (CFrac ℚ)) :=
  basis.flatMap (fun wi =>
    (List.range (degBound + 1)).map (fun j => cscale (qxMon j) wi))

/-- The integral basis of the cuspidal cubic `y³ = x²`. -/
def gcuspCubicBasis : List (DensePoly (CFrac ℚ)) := integralBasis gcuspCubicF

end DeepWiki.SymbolicIntegration
