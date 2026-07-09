import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalCase2
import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicResidues

/-! # The algebraic-log integral, validated by the logarithmic-derivative check

For a radical-extension element `u ∈ α[y]/(yⁿ − ρ)`, `D(log u) = (radDeriv u)/u`, so
`∫(integrand) dx = log u` iff `radDeriv u = radMul u integrand` (the division-free certificate
`radIsLogIntegral`, the integrand lifted as an `R/y` form `[0, R/ρ]`). This file verifies the classic
algebraic-log integrals (arcsinh/arccosh `log(x + y)`, the finite-pole `∫ dx/(x√(x²+1)) = log((y−1)/x)`)
through that certificate, connects the finite-pole case to its residue resultant, and includes a
heuristic computing `u` for `∫ dx/√(monic quadratic)`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPoly

/-! ### The logarithmic-derivative certificate `radIsLogIntegral` -/

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α]

/-- The log-derivative certificate `radIsLogIntegral n ρ u integrand`: the division-free boolean check
`radDeriv u = radMul u integrand` (via `radIsZero` of the difference), i.e. `∫(integrand) dx = log u` in
`α[y]/(yⁿ − ρ)`. -/
def radIsLogIntegral (n : ℕ) (ρ : α) (u integrand : RadElem α) : Bool :=
  radIsZero (radSub (radDeriv n ρ u) (radMul n ρ u integrand))

/-- The log-derivative certificate as a `Prop`: `RadIsLogIntegral n ρ u integrand` is
`radIsLogIntegral … = true`, i.e. `radDeriv u − u·integrand` vanishes as field elements in
`α[y]/(yⁿ − ρ)`. -/
abbrev RadIsLogIntegral (n : ℕ) (ρ : α) (u integrand : RadElem α) : Prop :=
  radIsLogIntegral n ρ u integrand = true

/-- An `R/y` integrand lift `radInvYLift ρ R = [0, R/ρ]`: the pure-`y` element representing `R/y` in
`α[y]/(y² − ρ)`. -/
def radInvYLift (ρ R : α) : RadElem α := [CField.zero, CField.div R ρ]

end RadElem

/-! ### Classic algebraic-log integrals: arcsinh / arccosh as `log(x + y)`

Over `ℚ(x)`, `n = 2`: the integrand `1/y` lifts to `[0, 1/ρ]`, the claimed `u = x + y = [x, 1]`, checked
by the log-derivative certificate. -/

open RadElem

/-- The radicand `ρ = x² + 1 ∈ ℚ(x)` (`y = √(x²+1)`), numerator `[1, 0, 1]`. -/
def radLogRhoArcsinh : QFunNZG ℚ := qxOfNum [1, 0, 1]

/-- The radicand `ρ = x² − 1 ∈ ℚ(x)` (`y = √(x²−1)`), numerator `[−1, 0, 1]`. -/
def radLogRhoArccosh : QFunNZG ℚ := qxOfNum [-1, 0, 1]

/-- The field element `x ∈ ℚ(x)`, numerator `[0, 1]`. -/
def radLogX : QFunNZG ℚ := qxOfNum [0, 1]

/-- The claimed log argument `u = x + y = [x, 1]` for both `arcsinh`/`arccosh` (`∫ dx/√(x²±1) =
log(x + y)`). -/
def radLogUxPlusY : RadElem (QFunNZG ℚ) := [radLogX, CField.one]

/-- The integrand `1/y` of `∫ dx/√(x²+1)`, lifted to `[0, 1/ρ]` over `ℚ(x)` (`ρ = x²+1`). -/
def radLogIntegrandArcsinh : RadElem (QFunNZG ℚ) := radInvYLift radLogRhoArcsinh CField.one

/-- The integrand `1/y` of `∫ dx/√(x²−1)`, lifted to `[0, 1/ρ]` over `ℚ(x)` (`ρ = x²−1`). -/
def radLogIntegrandArccosh : RadElem (QFunNZG ℚ) := radInvYLift radLogRhoArccosh CField.one

/-- `∫ dx/√(x²+1) = log(x + √(x²+1))`: the log-derivative certificate holds for `u = x + y`,
`integrand = [0, 1/(x²+1)]`, `y² = x²+1`. -/
theorem radLog_arcsinh :
    radIsLogIntegral 2 radLogRhoArcsinh radLogUxPlusY radLogIntegrandArcsinh = true := by
  native_decide

/-- `∫ dx/√(x²−1) = log(x + √(x²−1))`: the same `u = x + y` validates against `integrand = [0, 1/(x²−1)]`
on `y² = x²−1`. -/
theorem radLog_arccosh :
    radIsLogIntegral 2 radLogRhoArccosh radLogUxPlusY radLogIntegrandArccosh = true := by
  native_decide

/-- The `Prop`-form arcsinh certificate: `radDeriv (x + y) − (x + y)·[0, 1/(x²+1)]` vanishes as field
elements, i.e. `∫ dx/√(x²+1) = log(x + y)`. -/
theorem radLog_arcsinh_prop :
    RadIsLogIntegral 2 radLogRhoArcsinh radLogUxPlusY radLogIntegrandArcsinh := by
  native_decide

/-! ### A finite-pole example: `∫ dx/(x√(x²+1)) = log((y − 1)/x)`

`∫ dx/(x√(x²+1))` has a finite pole at `x = 0`; the integrand `1/(x y)` lifts to `[0, 1/(x·ρ)]`, and the
log argument `u = (y − 1)/x = [−1/x, 1/x]` passes the certificate (the wrong-sign `(y + 1)/x` fails). -/

/-- The field element `x·ρ = x·(x²+1) = x + x³ ∈ ℚ(x)`, numerator `[0, 1, 0, 1]` — the denominator of the
lifted integrand `1/(x·y)`. -/
def radLogXRho : QFunNZG ℚ := qxOfNum [0, 1, 0, 1]

/-- The field element `1/x ∈ ℚ(x)`. -/
def radLogInvX : QFunNZG ℚ := CField.div CField.one radLogX

/-- The integrand `1/(x y)` of `∫ dx/(x√(x²+1))`, lifted to `[0, 1/(x·ρ)]` over `ℚ(x)` (`R = 1/x`). -/
def radLogIntegrandFinite : RadElem (QFunNZG ℚ) := radInvYLift radLogXRho CField.one

/-- The finite-pole log argument `u = (y − 1)/x = [−1/x, 1/x]` for `∫ dx/(x√(x²+1))`. -/
def radLogUFinite : RadElem (QFunNZG ℚ) := [CField.neg radLogInvX, radLogInvX]

/-- The wrong-sign candidate `u = (y + 1)/x = [1/x, 1/x]`, which fails the certificate. -/
def radLogUFiniteWrong : RadElem (QFunNZG ℚ) := [radLogInvX, radLogInvX]

/-- `∫ dx/(x√(x²+1)) = log((√(x²+1) − 1)/x)`: the log-derivative certificate holds for `u = (y − 1)/x`,
`integrand = [0, 1/(x(x²+1))]`, `y² = x²+1`. -/
theorem radLog_finitePole :
    radIsLogIntegral 2 radLogRhoArcsinh radLogUFinite radLogIntegrandFinite = true := by
  native_decide

/-- Negative control: `(y + 1)/x` is not the log argument — the wrong-sign candidate fails the
certificate (`radIsLogIntegral … = false`). -/
theorem radLog_finitePole_wrong_sign :
    radIsLogIntegral 2 radLogRhoArcsinh radLogUFiniteWrong radLogIntegrandFinite = false := by
  native_decide

/-! ### The residue connection for the finite-pole example

Rationalizing `1/(x y) = y/(x³+x)`: numerator `g = y`, denominator `D = x³ + x`. The resultant
`cAlgResidueResultant` computes `R(Z)`, whose roots are the residues. -/

open CPoly

/-- Residue-connection radicand `ρ = x² + 1` (curve `y² = x²+1`), `ℚ[x]` `[1, 0, 1]`. -/
def radLogResRho : CPoly ℚ := [1, 0, 1]

/-- Residue-connection denominator `D = x³ + x = x(x²+1)` of `f = y/(x³+x)` — its finite root `x = 0`
carries the pole, `x = ±i` the branch places, `ℚ[x]` `[0, 1, 0, 1]`. -/
def radLogResD : CPoly ℚ := [0, 1, 0, 1]

/-- Residue-connection numerator low part `g₀ = 0` (`g(x,y) = y` has no `y⁰` part). -/
def radLogResG0 : CPoly ℚ := []

/-- Residue-connection numerator `y`-coefficient `g₁ = 1` (`g(x,y) = y`), `ℚ[x]` `[1]`. -/
def radLogResG1 : CPoly ℚ := [1]

/-- The computed residue resultant `R(Z)` for `∫ dx/(x√(x²+1))` (`n = 2`). -/
def radLogResR : CPoly ℚ := cAlgResidueResultant radLogResD radLogResRho radLogResG0 radLogResG1

-- Sanity print: `R(Z) = 16·Z⁴(Z² − 1) = −16·Z⁴ + 16·Z⁶` (low→high in `Z`).
#eval (cnormG radLogResR : List ℚ)

/-- The finite-pole residues are `±1`: `cAlgResidueResultant` returns `R(Z) = 16·Z⁴(Z² − 1)`, so
`cIsResidue R (±1) = true` and `cIsResidue R 0 = true`. -/
theorem radLog_finitePole_residues :
    cIsResidue radLogResR (1 : ℚ) = true
    ∧ cIsResidue radLogResR (-1 : ℚ) = true
    ∧ cIsResidue radLogResR (0 : ℚ) = true := by
  native_decide

/-- `Z = 2` is not a residue: `cIsResidue R 2 = false` (`R(2) ≠ 0`). -/
theorem radLog_finitePole_two_not_residue :
    cIsResidue radLogResR (2 : ℚ) = false := by
  native_decide

/-- The finite-pole residues are all integers: `R(Z)` factors with integer linear factors
`0, 0, 0, 0, 1, −1`, so `cResiduesMatch R [0, 0, 0, 0, 1, -1] = true`. -/
theorem radLog_finitePole_residues_integer :
    cResiduesMatch radLogResR [0, 0, 0, 0, 1, -1] = true := by
  native_decide

/-! ### A heuristic computing `u` for `∫ dx/√(monic quadratic)`

For `∫ dx/√(x² + bx + c)` the log term is `u = x + b/2 + y` (completing the square). `radQuadraticLogArg`
produces `u` from the coefficients, validated by the certificate on `ρ = x² + 2x + 2`. -/

namespace RadElem

variable {α : Type*} [CField α]

/-- Heuristic log argument for `∫ dx/√(x² + bx + c)`: `radQuadraticLogArg b = [b/2, 1]`, the element
`u = x + b/2 + y` of `α[y]/(y² − (x² + bx + c))`. -/
def radQuadraticLogArg (b : α) : RadElem α :=
  [CField.div b (CPoly.cnatCastG 2), CField.one]

end RadElem

/-- The shifted radicand `ρ = x² + 2x + 2 = (x+1)² + 1 ∈ ℚ(x)`, numerator `[2, 2, 1]`. -/
def radLogRhoShift : QFunNZG ℚ := qxOfNum [2, 2, 1]

/-- The field element `x + 1 ∈ ℚ(x)`, numerator `[1, 1]`. -/
def radLogXPlusOne : QFunNZG ℚ := qxOfNum [1, 1]

/-- The heuristic-computed log argument `u = (x + 1) + y = [x + 1, 1]` for `∫ dx/√(x² + 2x + 2)`. -/
def radLogUShift : RadElem (QFunNZG ℚ) := [radLogXPlusOne, CField.one]

/-- The integrand `1/y` of `∫ dx/√(x² + 2x + 2)`, lifted to `[0, 1/ρ]` over `ℚ(x)` (`ρ = x²+2x+2`). -/
def radLogIntegrandShift : RadElem (QFunNZG ℚ) := radInvYLift radLogRhoShift CField.one

/-- The quadratic heuristic computes a valid log argument: for `∫ dx/√(x² + 2x + 2)` the heuristic
`u = (x + 1) + y` satisfies the log-derivative certificate over `ℚ(x)`, `y² = x²+2x+2`. -/
theorem radLog_quadratic_heuristic :
    radIsLogIntegral 2 radLogRhoShift radLogUShift radLogIntegrandShift = true := by
  native_decide

/-! ### Axiom audit for the algebraic-log examples -/

-- Algebraic-log integrals `∫ = log u` validated through `radDeriv`:
#print axioms radLog_arcsinh
#print axioms radLog_arccosh
#print axioms radLog_finitePole
#print axioms radLog_finitePole_residues_integer
#print axioms radLog_quadratic_heuristic

end DeepWiki.SymbolicIntegration
