import DeepWiki.SymbolicIntegration.Computable.Algebraic.IntegralBasisFull

/-! # Shared setup for general algebraic-function computations

Partial derivatives, ansatz monomials, and common validation curves shared by
the general algebraic-function modules. -/

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-- The formal `y`-derivative `∂f/∂y` of a general curve polynomial. -/
def afFy (f : CPolyG α) : CPolyG α := cderivG f

section AfFyDenote

variable [CFieldSpec α]

/-- `afFy` reads as the formal derivative through `toPolyG`. -/
theorem derivative_toPolyG_eq_afFy (f : CPolyG α) :
    Polynomial.derivative (toPolyG f) = toPolyG (afFy f) := by
  simp only [afFy, denote]

end AfFyDenote

variable [CDiffField α]

/-- The coefficientwise base derivative `∂f/∂x` of a general curve polynomial. -/
def afFx (f : CPolyG α) : CPolyG α := (f : List α).map CDiffField.cderiv

end CPolyG

open CPolyG

/-- The cuspidal cubic `f = y³ - x² ∈ ℚ(x)[y]`. -/
def gcuspCubicF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [0, 0, -1], CField.zero, CField.zero, CField.one]

/-- The generator `y` of `ℚ(x)[y]/(y³ - x²)`. -/
def gcuspCubicY : CPolyG (QFunNZG ℚ) := afBasisElem 1

/-- The element `y²` of `ℚ(x)[y]/(y³ - x²)`. -/
def gcuspCubicYsq : CPolyG (QFunNZG ℚ) := afBasisElem 2

/-- A `ℚ(x)` value `xᵏ`, used as an ansatz scalar. -/
def qxMon (k : ℕ) : QFunNZG ℚ := qxOfNum (cshiftG k [(1 : ℚ)])

/-- The ansatz monomials `xʲ * wᵢ` over an integral basis. -/
def afRatMonomials (basis : List (CPolyG (QFunNZG ℚ))) (degBound : ℕ) :
    List (CPolyG (QFunNZG ℚ)) :=
  basis.flatMap (fun wi =>
    (List.range (degBound + 1)).map (fun j => cscaleG (qxMon j) wi))

/-- The integral basis of the cuspidal cubic `y³ = x²`. -/
def gcuspCubicBasis : List (CPolyG (QFunNZG ℚ)) := integralBasis gcuspCubicF

end DeepWiki.SymbolicIntegration
