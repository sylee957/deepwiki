import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalRationalDriver
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgument
import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicResidues

/-! # Shared assembly layer for simple-radical algebraic integrals

This module contains the fuel-independent representation and differentiation layer for
`v + Σ cᵢ log uᵢ`, plus shared round-trip inputs used by both fueled and fuel-free drivers.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### Division in the radical extension `α[y]/(y² − ρ)` (`n = 2`) and the log-derivative -/

namespace RadElem

variable {α : Type*} [CField α]

/-- **The `α`-component (`y⁰`) of a `RadElem`** `radCoeff0 u = a` for `u = [a, b, …]`. -/
def radCoeff0 (u : RadElem α) : α := (u : List α).headD CField.zero

/-- **The `y`-component (`y¹`) of a `RadElem`** `radCoeff1 u = b` for `u = [a, b, …]`. -/
def radCoeff1 (u : RadElem α) : α := (u : List α).getD 1 CField.zero

/-- **The conjugate norm** `radNorm2 ρ u = a² − b²·ρ ∈ α` for `u = a + b·y`. -/
def radNorm2 (ρ : α) (u : RadElem α) : α :=
  let a := radCoeff0 u
  let b := radCoeff1 u
  CField.sub (CField.mul a a) (CField.mul (CField.mul b b) ρ)

/-- **The reciprocal in `α[y]/(y² − ρ)`** `radInv2 ρ u = [a/N, −b/N]` for `u = a + b·y`. -/
def radInv2 (ρ : α) (u : RadElem α) : RadElem α :=
  let a := radCoeff0 u
  let b := radCoeff1 u
  let N := radNorm2 ρ u
  [CField.div a N, CField.neg (CField.div b N)]

variable [CDiffField α]

/-- **The logarithmic derivative in `α[y]/(y² − ρ)`** `radLogDeriv ρ u = (radDeriv u)·u⁻¹`. -/
def radLogDeriv (ρ : α) (u : RadElem α) : RadElem α :=
  radMul 2 ρ (radDeriv 2 ρ u) (radInv2 ρ u)

end RadElem

open RadElem

/-! ### Shared example data for `radInv2` and `radLogDeriv` -/

/-- The radicand `ρ = x² + 1 ∈ ℚ(x)` (`y = √(x²+1)`). -/
def fullRhoArcsinh : CFrac ℚ := qxOfNum [1, 0, 1]

/-- The element `u = x + y = [x, 1]` over `ℚ(x)`, `y² = x²+1`. -/
def fullUxPlusY : RadElem (CFrac ℚ) := [qxOfNum [0, 1], CField.one]

/-- **`u · u⁻¹ = 1` in `(CFrac ℚ)[y]/(y² − (x²+1))`** (`native_decide`). -/
theorem radInv2_mul_self_eq_one :
    radIsZero (radSub (radMul 2 fullRhoArcsinh fullUxPlusY (radInv2 fullRhoArcsinh fullUxPlusY))
      [CField.one]) = true := by native_decide

/-- The integrand `1/y` of `∫ dx/√(x²+1)`, lifted to `[0, 1/ρ]` over `ℚ(x)`. -/
def fullIntegrandArcsinh : RadElem (CFrac ℚ) := radInvYLift fullRhoArcsinh CField.one

/-- **`radLogDeriv` agrees with the arcsinh log-derivative certificate** (`native_decide`). -/
theorem radLogDeriv_eq_integrand_arcsinh :
    radIsZero (radSub (radLogDeriv fullRhoArcsinh fullUxPlusY) fullIntegrandArcsinh) = true := by
  native_decide

/-! ### `AlgIntegralResult` and its derivative -/

/-- Tower-generic elementary integral `∫ = v + Σ cᵢ log uᵢ`: rational part `v : RadElem α` plus
log terms `[(cᵢ, uᵢ)]` (`cᵢ ∈ α`, `uᵢ ∈ α[y]/(y² − ρ)`). -/
structure AlgIntegralResult (α : Type*) [CField α] where
  /-- The rational part `v` of `∫ = v + Σ cᵢ log uᵢ` (a `RadElem α`). -/
  ratPart : RadElem α
  /-- The log terms `[(cᵢ, uᵢ)]` (`cᵢ ∈ α`, `uᵢ : RadElem α`). -/
  logTerms : List (α × RadElem α)

/-- Derivative `algDeriv ρ F = radDeriv v + Σ cᵢ · radLogDeriv uᵢ` in `α[y]/(y² − ρ)`, using the
tower's `CDiffField.cderiv` as base derivation. -/
def algDeriv {α : Type*} [CField α] [CDiffField α] (ρ : α) (F : AlgIntegralResult α) : RadElem α :=
  F.logTerms.foldl
    (fun acc (c, u) => radAdd acc (radScale c (radLogDeriv ρ u)))
    (radDeriv 2 ρ F.ratPart)


/-- **The derivative of a full algebraic integral** `algDerivQ ρ F = radDeriv v + Σ cᵢ·radLogDeriv uᵢ`,
the `CFrac ℚ` specialization of `algDeriv`. -/
def algDerivQ (ρ : CFrac ℚ) (F : AlgIntegralResult (CFrac ℚ)) : RadElem (CFrac ℚ) :=
  algDeriv ρ F

-- The concrete result/derivative are exactly the generic ones at the `ℚ(x)` base (`base + abbrev`).
example : AlgIntegralResult (CFrac ℚ) = AlgIntegralResult (CFrac ℚ) := rfl
example (ρ : CFrac ℚ) (F : AlgIntegralResult (CFrac ℚ)) : algDerivQ ρ F = algDeriv ρ F := rfl

/-- **Assemble the rational part `v` from a multi-case dispatch run**. -/
def radAssembleRatPart (ρ : CFrac ℚ)
    (runs : List (Bool × DensePoly ℚ × ℕ × DensePoly ℚ × DensePoly ℚ × DensePoly ℚ)) : RadElem (CFrac ℚ) :=
  runs.foldl
    (fun acc (isV, fi, e, _, vNum, _) =>
      let denomPow := if isV then cpow fi (e - 1) else cpow fi e
      radAdd acc
        [CField.zero, CField.div (qxOfNum vNum) (CField.mul (qxOfNum denomPow) ρ)])
    radZero

/-! ### Shared round-trip inputs for algebraic integrators -/

/-- Rational-only round-trip radicand `ρ = x² + 1 ∈ ℚ(x)`. -/
def rtRatRho : CFrac ℚ := qxOfNum [1, 0, 1]

/-- Rational-only round-trip numerator `R = 1`. -/
def rtRatR : DensePoly ℚ := [1]

/-- Rational-only round-trip denominator `B = (x−1)²`. -/
def rtRatB : DensePoly ℚ := cpow [-1, 1] 2

/-- A non-principal residual for the rational-only log solve. -/
def rtRatNonPrincipalResidual : RadElem (CFrac ℚ) := radInvYLift (qxOfNum [0, 0, 1, 0, 1]) CField.one

/-- Log-only round-trip radicand `ρ = x² + 1 ∈ ℚ(x)`. -/
def rtLogRho : CFrac ℚ := qxOfNum [1, 0, 1]

/-- The field element `x·ρ = x·(x²+1) = x + x³ ∈ ℚ(x)`. -/
def rtLogXRho : CFrac ℚ := qxOfNum [0, 1, 0, 1]

/-- The integrand `1/(x y)` of `∫ dx/(x√(x²+1))`. -/
def rtLogIntegrand : RadElem (CFrac ℚ) := radInvYLift rtLogXRho CField.one

/-- The fixed log-solve denominator `D = x`. -/
def rtLogD : DensePoly ℚ := [0, 1]

/-- Combined round-trip radicand `ρ = x² + 1 ∈ ℚ(x)`. -/
def rtCombRho : CFrac ℚ := qxOfNum [1, 0, 1]

/-- Combined round-trip rational numerator `R = 1`. -/
def rtCombR : DensePoly ℚ := [1]

/-- Combined round-trip rational denominator `B = (x−1)²`. -/
def rtCombB : DensePoly ℚ := cpow [-1, 1] 2

/-- The combined round-trip's log argument `u = x + y = [x, 1]`. -/
def rtCombU : RadElem (CFrac ℚ) := [qxOfNum [0, 1], CField.one]

/-- The log residual `[0, 1/(x²+1)]` absorbed by the combined log solve. -/
def rtCombLogResidual : RadElem (CFrac ℚ) := radInvYLift rtCombRho CField.one

end DeepWiki.SymbolicIntegration
