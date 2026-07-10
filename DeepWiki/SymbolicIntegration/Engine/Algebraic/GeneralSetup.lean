import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralDerivatives

/-! # Concrete setup for general algebraic-function computations

Ansatz monomials and the shared cuspidal-cubic fixture used by the general
algebraic-function computation modules. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- The cuspidal cubic `f = y³ - x² ∈ ℚ(x)[y]`. -/
def gcuspCubicF : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [0, 0, -1], CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- The generator `y` of `ℚ(x)[y]/(y³ - x²)`. -/
def gcuspCubicY : DensePoly (DenseFrac ℚ) := afBasisElem 1

/-- The element `y²` of `ℚ(x)[y]/(y³ - x²)`. -/
def gcuspCubicYsq : DensePoly (DenseFrac ℚ) := afBasisElem 2

/-- A `ℚ(x)` value `xᵏ`, used as an ansatz scalar. -/
def qxMon (k : ℕ) : DenseFrac ℚ := CFrac.ofPoly (cshift k [(1 : ℚ)])

/-- The ansatz monomials `xʲ * wᵢ` over an integral basis. -/
def afRatMonomials {P : Type → Type} [CPoly P] [CPolyEngine P]
    (basis : List (P (DenseFrac ℚ))) (degBound : ℕ) : List (P (DenseFrac ℚ)) :=
  basis.flatMap (fun wi =>
    (List.range (degBound + 1)).map (fun j => CPolyEngine.scale (qxMon j) wi))

example :
    let ofList : List (DenseFrac ℚ) → CPoly.SparsePoly (DenseFrac ℚ) := CPolyEngine.ofCoeffList
    let basis := [ofList [CCommRing.one]]
    let ms := afRatMonomials basis 1
    CCommRing.isZero (CField.sub (CPoly.coeff (ms.getD 1 (ofList [])) 0) (qxMon 1)) = true := by
  native_decide

/-- The integral basis of the cuspidal cubic `y³ = x²`. -/
def gcuspCubicBasis : List (DensePoly (DenseFrac ℚ)) := integralBasis gcuspCubicF

end DeepWiki.SymbolicIntegration
