import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalRationalDriver
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogArgument
import DeepWiki.SymbolicIntegration.Computable.Algebraic.AlgebraicResidues

/-! # Shared assembly layer for simple-radical algebraic integrals

This module contains the fuel-independent representation and differentiation layer for
`v + Σ cᵢ log uᵢ`, plus shared round-trip inputs used by both fueled and fuel-free drivers.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

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
def fullRhoArcsinh : QFunNZG ℚ := qxOfNum [1, 0, 1]

/-- The element `u = x + y = [x, 1]` over `ℚ(x)`, `y² = x²+1`. -/
def fullUxPlusY : RadElem (QFunNZG ℚ) := [qxOfNum [0, 1], CField.one]

/-- **`u · u⁻¹ = 1` in `(QFunNZG ℚ)[y]/(y² − (x²+1))`** (`native_decide`). -/
theorem radInv2_mul_self_eq_one :
    radIsZero (radSub (radMul 2 fullRhoArcsinh fullUxPlusY (radInv2 fullRhoArcsinh fullUxPlusY))
      [CField.one]) = true := by native_decide

/-- The integrand `1/y` of `∫ dx/√(x²+1)`, lifted to `[0, 1/ρ]` over `ℚ(x)`. -/
def fullIntegrandArcsinh : RadElem (QFunNZG ℚ) := radInvYLift fullRhoArcsinh CField.one

/-- **`radLogDeriv` agrees with the arcsinh log-derivative certificate** (`native_decide`). -/
theorem radLogDeriv_eq_integrand_arcsinh :
    radIsZero (radSub (radLogDeriv fullRhoArcsinh fullUxPlusY) fullIntegrandArcsinh) = true := by
  native_decide

/-! ### `AlgIntegralResultG` and its derivative -/

/-- Tower-generic elementary integral `∫ = v + Σ cᵢ log uᵢ`: rational part `v : RadElem α` plus
log terms `[(cᵢ, uᵢ)]` (`cᵢ ∈ α`, `uᵢ ∈ α[y]/(y² − ρ)`). -/
structure AlgIntegralResultG (α : Type*) [CField α] where
  /-- The rational part `v` of `∫ = v + Σ cᵢ log uᵢ` (a `RadElem α`). -/
  ratPart : RadElem α
  /-- The log terms `[(cᵢ, uᵢ)]` (`cᵢ ∈ α`, `uᵢ : RadElem α`). -/
  logTerms : List (α × RadElem α)

/-- Derivative `algDerivG ρ F = radDeriv v + Σ cᵢ · radLogDeriv uᵢ` in `α[y]/(y² − ρ)`, using the
tower's `CDiffField.cderiv` as base derivation. -/
def algDerivG {α : Type*} [CField α] [CDiffField α] (ρ : α) (F : AlgIntegralResultG α) : RadElem α :=
  F.logTerms.foldl
    (fun acc (c, u) => radAdd acc (radScale c (radLogDeriv ρ u)))
    (radDeriv 2 ρ F.ratPart)

/-- **The full algebraic integral `∫ = v + Σ cᵢ log uᵢ`** (principal case) — the tower-generic
`AlgIntegralResultG` specialized to the `ℚ(x)` base `QFunNZG ℚ`. -/
abbrev AlgIntegralResult := AlgIntegralResultG (QFunNZG ℚ)

/-- **The derivative of a full algebraic integral** `algDeriv ρ F = radDeriv v + Σ cᵢ·radLogDeriv uᵢ`,
the `QFunNZG ℚ` specialization of `algDerivG`. -/
def algDeriv (ρ : QFunNZG ℚ) (F : AlgIntegralResult) : RadElem (QFunNZG ℚ) :=
  algDerivG ρ F

-- The concrete result/derivative are exactly the generic ones at the `ℚ(x)` base (`base + abbrev`).
example : AlgIntegralResult = AlgIntegralResultG (QFunNZG ℚ) := rfl
example (ρ : QFunNZG ℚ) (F : AlgIntegralResult) : algDeriv ρ F = algDerivG ρ F := rfl

/-- **Assemble the rational part `v` from a multi-case dispatch run**. -/
def radAssembleRatPart (ρ : QFunNZG ℚ)
    (runs : List (Bool × CPolyG ℚ × ℕ × CPolyG ℚ × CPolyG ℚ × CPolyG ℚ)) : RadElem (QFunNZG ℚ) :=
  runs.foldl
    (fun acc (isV, fi, e, _, vNum, _) =>
      let denomPow := if isV then cpowG fi (e - 1) else cpowG fi e
      radAdd acc
        [CField.zero, CField.div (qxOfNum vNum) (CField.mul (qxOfNum denomPow) ρ)])
    radZero

/-! ### Shared round-trip inputs for algebraic integrators -/

/-- Rational-only round-trip radicand `ρ = x² + 1 ∈ ℚ(x)`. -/
def rtRatRho : QFunNZG ℚ := qxOfNum [1, 0, 1]

/-- Rational-only round-trip numerator `R = 1`. -/
def rtRatR : CPolyG ℚ := [1]

/-- Rational-only round-trip denominator `B = (x−1)²`. -/
def rtRatB : CPolyG ℚ := cpowG [-1, 1] 2

/-- A non-principal residual for the rational-only log solve. -/
def rtRatNonPrincipalResidual : RadElem (QFunNZG ℚ) := radInvYLift (qxOfNum [0, 0, 1, 0, 1]) CField.one

/-- Log-only round-trip radicand `ρ = x² + 1 ∈ ℚ(x)`. -/
def rtLogRho : QFunNZG ℚ := qxOfNum [1, 0, 1]

/-- The field element `x·ρ = x·(x²+1) = x + x³ ∈ ℚ(x)`. -/
def rtLogXRho : QFunNZG ℚ := qxOfNum [0, 1, 0, 1]

/-- The integrand `1/(x y)` of `∫ dx/(x√(x²+1))`. -/
def rtLogIntegrand : RadElem (QFunNZG ℚ) := radInvYLift rtLogXRho CField.one

/-- The fixed log-solve denominator `D = x`. -/
def rtLogD : CPolyG ℚ := [0, 1]

/-- Combined round-trip radicand `ρ = x² + 1 ∈ ℚ(x)`. -/
def rtCombRho : QFunNZG ℚ := qxOfNum [1, 0, 1]

/-- Combined round-trip rational numerator `R = 1`. -/
def rtCombR : CPolyG ℚ := [1]

/-- Combined round-trip rational denominator `B = (x−1)²`. -/
def rtCombB : CPolyG ℚ := cpowG [-1, 1] 2

/-- The combined round-trip's log argument `u = x + y = [x, 1]`. -/
def rtCombU : RadElem (QFunNZG ℚ) := [qxOfNum [0, 1], CField.one]

/-- The log residual `[0, 1/(x²+1)]` absorbed by the combined log solve. -/
def rtCombLogResidual : RadElem (QFunNZG ℚ) := radInvYLift rtCombRho CField.one

end DeepWiki.SymbolicIntegration
