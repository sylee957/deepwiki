import DeepWiki.SymbolicIntegration.Engine.FunctionAlgebraIntegrate.Soundness

/-! # Function-algebra integration examples

Worked checks for `∫y dx` on the reducible curve `(y²−x)(y³−x) = 0`, plus restatements of the
abstract recombination API. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace CPolyG

/-- The square-root component curve `T₁ = y² − x ∈ ℚ(x)[y]`. -/
def sqrtComponentCurve : CPolyG (QFunNZG ℚ) := [qxOfNum [0, -1], CField.zero, CField.one]

/-- The square-root component integral `F₁ = (2/3)·x·y`. -/
def sqrtComponentIntegral : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [0, 2/3]]

/-- The cube-root component curve `T₂ = y³ − x ∈ ℚ(x)[y]`. -/
def cubeRootComponentCurve : CPolyG (QFunNZG ℚ) := [qxOfNum [0, -1], CField.zero, CField.zero, CField.one]

/-- The cube-root component integral `F₂ = (3/4)·x·y`. -/
def cubeRootComponentIntegral : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [0, 3/4]]

/-- The integrand `y = [0, 1]` (`afBasisElem 1`) of `∫y dx`. -/
def componentIntegrandY : CPolyG (QFunNZG ℚ) := afBasisElem 1

/-- Component 1 (`native_decide`): `∫y dx = (2/3)·x·y` on `y² − x = 0`, checked by
`cisZeroG (afDerivWf (y²−x) F₁ − y)`. -/
theorem sqrtComponentIntegral_deriv :
    cisZeroG (csubG (afDerivWf sqrtComponentCurve sqrtComponentIntegral) componentIntegrandY) = true := by
  native_decide

/-- Component 2 (`native_decide`): `∫y dx = (3/4)·x·y` on `y³ − x = 0`, checked by
`cisZeroG (afDerivWf (y³−x) F₂ − y)`. -/
theorem cubeRootComponentIntegral_deriv :
    cisZeroG (csubG (afDerivWf cubeRootComponentCurve cubeRootComponentIntegral) componentIntegrandY)
      = true := by
  native_decide

end CPolyG

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ The keystone (abstract): a derivation kills any idempotent — "the indicators are constants".
example {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q] (D : Derivation R Q Q)
    (e : Q) (he : IsIdempotentElem e) : D e = 0 :=
  FunctionAlgebra.derivation_idempotent_eq_zero D e he

-- ★ The recombination soundness (abstract): `D(Σ eᵢ Fᵢ) = g` over a partition of unity by idempotents
-- with the per-component soundness `eᵢ·D Fᵢ = eᵢ·g` — the irreducible-curve caveat removed abstractly.
example {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q] (D : Derivation R Q Q)
    (pairs : List (Q × Q)) (g : Q)
    (hidem : ∀ p ∈ pairs, IsIdempotentElem p.1)
    (hcomp : ∀ p ∈ pairs, p.1 * D p.2 = p.1 * g)
    (hsum : (pairs.map (fun p => p.1)).sum = 1) :
    D ((pairs.map (fun p => p.1 * p.2)).sum) = g :=
  FunctionAlgebra.derivation_recombine_eq D pairs g hidem hcomp hsum

-- ★★ The concrete function-algebra soundness `D(F) = integrand` over a reducible curve is
-- `CPolyG.afIntegrateFunctionAlgebra_sound`. The recombined integral `F = Σ eᵢ Fᵢ` of the function
-- algebra `K(x)[y]/(T)` differentiates to the integrand in the carrier quotient.

end DeepWiki.SymbolicIntegration
