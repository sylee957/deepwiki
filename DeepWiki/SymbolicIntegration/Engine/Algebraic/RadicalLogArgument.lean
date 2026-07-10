import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogIntegral
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGeneric

/-! # Solving for the log argument `u` in `∫ = log u` (principal case)

The log-derivative condition `∫(integrand) dx = log(N/D)` is `ℚ`-linear in the numerator `N = a₀ + a₁·y`:
clearing `D`, it is `radDeriv(N)·D − N·D' − radMul(N, integrand)·D = 0`. `radLogArgSolve` sets up this
finite homogeneous `ℚ`-linear system on a bounded monomial ansatz, finds a nonzero kernel vector by
Gaussian elimination, and returns `N` (so `u = N/D`), or `none` when the principal ansatz has trivial
kernel. Each solve is validated by the log-derivative certificate `radIsLogIntegral`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### Solve-then-verify: arcsinh / arccosh / finite-pole

For each target `radLogArgSolve` computes `N`; the computed `u = N/D` is fed to the log-derivative
certificate `radIsLogIntegral` and compared against the closed form. -/

/-- The radicand `ρ = x²+1 ∈ ℚ(x)` (`y = √(x²+1)`), `[1,0,1]`. -/
def radArgRhoArcsinh : DenseFrac ℚ := CFrac.ofPoly [1, 0, 1]

/-- The radicand `ρ = x²−1 ∈ ℚ(x)` (`y = √(x²−1)`), `[−1,0,1]`. -/
def radArgRhoArccosh : DenseFrac ℚ := CFrac.ofPoly [-1, 0, 1]

/-- The integrand `1/y` of `∫ dx/√(x²+1)`, lifted to `[0, 1/ρ]` over ℚ(x) (`ρ = x²+1`). -/
def radArgIntegrandArcsinh : RadElem (DenseFrac ℚ) := radInvYLift radArgRhoArcsinh CCommRing.one

/-- The integrand `1/y` of `∫ dx/√(x²−1)`, lifted to `[0, 1/ρ]` over ℚ(x) (`ρ = x²−1`). -/
def radArgIntegrandArccosh : RadElem (DenseFrac ℚ) := radInvYLift radArgRhoArccosh CCommRing.one

/-- The computed log argument for `∫ dx/√(x²+1)`: `radLogArgSolve` with `ρ = x²+1`, `D = 1`, ansatz
degree `1` (expected `N = x + y` up to a constant). -/
def radArgSolvedArcsinh : Option (RadElem (DenseFrac ℚ)) :=
  radLogArgSolve radArgRhoArcsinh radArgIntegrandArcsinh [1] 1

-- Computed numerator `N` for arcsinh, expected up to scalar as `x + y`.
#eval (radArgSolvedArcsinh.map (fun N => N.map (fun z => ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ)))))

/-- `radLogArgSolve` computes `u = x + y` for `∫ dx/√(x²+1)`: the solved `N` passes the log-derivative
certificate `radIsLogIntegral 2 ρ N integrand = true`. -/
theorem radArg_arcsinh_compute_verify :
    (radArgSolvedArcsinh.map (fun N =>
      radIsLogIntegral 2 radArgRhoArcsinh N radArgIntegrandArcsinh)) = some true := by
  native_decide

/-- The computed log argument for `∫ dx/√(x²−1)`: `radLogArgSolve` with `ρ = x²−1`, `D = 1`, ansatz
degree `1` (expected `N = x + y`). -/
def radArgSolvedArccosh : Option (RadElem (DenseFrac ℚ)) :=
  radLogArgSolve radArgRhoArccosh radArgIntegrandArccosh [1] 1

/-- `radLogArgSolve` computes `u = x + y` for `∫ dx/√(x²−1)`: the solved `N` passes the log-derivative
certificate. -/
theorem radArg_arccosh_compute_verify :
    (radArgSolvedArccosh.map (fun N =>
      radIsLogIntegral 2 radArgRhoArccosh N radArgIntegrandArccosh)) = some true := by
  native_decide

/-! #### The finite-pole target `∫ dx/(x√(x²+1)) = log((y − 1)/x)` -/

/-- The field element `x·ρ = x·(x²+1) = x + x³ ∈ ℚ(x)`, `[0,1,0,1]` — denominator of the lifted integrand
`1/(x·y)`. -/
def radArgXRho : DenseFrac ℚ := CFrac.ofPoly [0, 1, 0, 1]

/-- The integrand `1/(x y)` of `∫ dx/(x√(x²+1))`, lifted to `[0, 1/(x·ρ)]` over ℚ(x). -/
def radArgIntegrandFinite : RadElem (DenseFrac ℚ) := radInvYLift radArgXRho CCommRing.one

/-- The field element `x ∈ ℚ(x)`, `[0,1]` — the fixed denominator `D = x` of the finite-pole case. -/
def radArgXBaseX : DenseFrac ℚ := CFrac.ofPoly [0, 1]

/-- The computed log argument for `∫ dx/(x√(x²+1))`: `radLogArgSolve` with `ρ = x²+1`, `D = x`, ansatz
degree `0` (expected `N = y − 1`, so `u = (y − 1)/x`). -/
def radArgSolvedFinite : Option (RadElem (DenseFrac ℚ)) :=
  radLogArgSolve radArgRhoArcsinh radArgIntegrandFinite [0, 1] 0

-- Computed numerator `N` for the finite-pole case, expected up to scalar as `y − 1`.
#eval (radArgSolvedFinite.map (fun N => N.map (fun z => ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ)))))

/-- `radLogArgSolve` computes `u = (y − 1)/x` for `∫ dx/(x√(x²+1))` with fixed `D = x`: the solved `N`
(a multiple of `y − 1`) gives `u = N/x` passing the log-derivative certificate; the solve picks the
correct sign `(y − 1)`. -/
theorem radArg_finitePole_compute_verify :
    (radArgSolvedFinite.map (fun N =>
      radIsLogIntegral 2 radArgRhoArcsinh
        [CField.div (N.getD 0 CCommRing.zero) radArgXBaseX,
         CField.div (N.getD 1 CCommRing.zero) radArgXBaseX]
        radArgIntegrandFinite)) = some true := by
  native_decide

/-! #### Matching the computed `N` to the known closed forms -/

/-- The computed arcsinh `N = [a₀, a₁]` is a nonzero constant multiple of `x + y`: `a₁ ≠ 0` and
`a₀ = a₁·x`, matching `u = x + y` up to scalar. -/
theorem radArg_arcsinh_matches_closed_form :
    (radArgSolvedArcsinh.map (fun N =>
      let a0 := N.getD 0 CCommRing.zero
      let a1 := N.getD 1 CCommRing.zero
      (CCommRing.isZero a1 == false) &&
      CCommRing.isZero (CField.sub a0 (CCommRing.mul a1 radArgXBaseX)))) = some true := by
  native_decide

/-! ### Negative control: a non-principal target returns `none`

`∫ dx/(x²·√(x²+1))` has a double pole at `x = 0`; with the bounded ansatz `D = x²`, degree `≤ 1`, there
is no bounded `N/D`, so `radLogArgSolve` returns `none`. -/

/-- The field element `x²·ρ = x²·(x²+1) = x² + x⁴ ∈ ℚ(x)`, `[0,0,1,0,1]` — denominator of the lifted
integrand `1/(x²·y)`. -/
def radArgX2Rho : DenseFrac ℚ := CFrac.ofPoly [0, 0, 1, 0, 1]

/-- The integrand `1/(x² y)` of `∫ dx/(x²√(x²+1))`, lifted to `[0, 1/(x²·ρ)]` over `ℚ(x)` (a double
pole at `x = 0`). -/
def radArgIntegrandDouble : RadElem (DenseFrac ℚ) := radInvYLift radArgX2Rho CCommRing.one

/-- The solve for the double-pole target: `radLogArgSolve` with `ρ = x²+1`, `D = x²`, degree `1`
(expected `none`). -/
def radArgSolvedDouble : Option (RadElem (DenseFrac ℚ)) :=
  radLogArgSolve radArgRhoArcsinh radArgIntegrandDouble [0, 0, 1] 1

/-- Negative control: the double-pole target has no bounded log argument —
`radLogArgSolve (x²+1) (1/(x²y)) x² 1 = none` (only the trivial kernel). -/
theorem radArg_double_pole_none :
    radArgSolvedDouble = none := by
  native_decide

/-! ### `#print axioms` — the solved log arguments, validated by the log-derivative certificate, and
the non-principal negative control. -/

-- Log arguments `u` computed by the linear solve, validated by the log-derivative check:
#print axioms radArg_arcsinh_compute_verify
#print axioms radArg_arccosh_compute_verify
#print axioms radArg_finitePole_compute_verify
#print axioms radArg_arcsinh_matches_closed_form
#print axioms radArg_double_pole_none

end DeepWiki.SymbolicIntegration
