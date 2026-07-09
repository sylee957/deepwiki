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

open RadElem CPoly

/-! ### Gaussian elimination over ℚ: a nonzero kernel vector of a ℚ-matrix

`ratKernelVector` row-reduces the matrix and reads a kernel vector off a free column, or returns `none`
for a trivial kernel. -/

/-- Reduce a `ℚ`-matrix to reduced row-echelon form, returning `(rrefRows, pivotCols)` — the `ℚ`-base
specialization of the `[CField β]`-generic `gaussElimG`. -/
def ratRref (nCols : ℕ) (rows : List (List ℚ)) : List (List ℚ) × List ℕ :=
  gaussElimG nCols rows

/-- A nonzero kernel vector of a `ℚ`-matrix: `ratKernelVector nCols rows = some c` with `M·c = 0`,
`c ≠ 0`, read off the first free column after `ratRref` — the `ℚ`-base specialization of `kernelVectorG`. -/
def ratKernelVector (nCols : ℕ) (rows : List (List ℚ)) : Option (List ℚ) :=
  kernelVectorG nCols rows

/-! ### Extracting the ℚ-linear system from the cleared log-derivative relation

The residual `radLogResidual ρ integrand D N = radDeriv(N)·D − N·D' − radMul(N, integrand)·D` is
`ℚ`-linear in `N`; evaluating it on the monomial basis and clearing each `ℚ(x)` entry to a polynomial
numerator gives the `ℚ`-matrix of the system. -/

/-- The ℚ(x) value `xᵏ`: numerator the `k`-th monomial `[0,…,0,1]`, denominator `1` — the `ℚ`-base
specialization of `qMonomialG`. -/
def qxMonomial (k : ℕ) : QFunNZG ℚ := qMonomialG k

/-- The cleared log-derivative residual `radLogResidual ρ integrand D N = radDeriv(N)·D − N·D' −
radMul(N, integrand)·D` in `(QFunNZG ℚ)[y]/(y² − ρ)`, whose vanishing says `∫(integrand) dx = log(N/D)`;
`ℚ`-linear in `N`. The `ℚ`-base specialization of `radLogResidualG` (which uses the actual base-field
derivation `CDiffField.cderiv`, agreeing with the formal `cderiv` on the untowered base `ℚ(x)`). -/
def radLogResidual (ρ : QFunNZG ℚ) (integrand : RadElem (QFunNZG ℚ)) (D : CPoly ℚ)
    (N : RadElem (QFunNZG ℚ)) : RadElem (QFunNZG ℚ) :=
  radLogResidualG ρ integrand D N

/-- The numerator coefficient list `qxNum z = z.1.1 ∈ ℚ[x]` of a ℚ(x) element — specialization of `qNumG`. -/
def qxNum (z : QFunNZG ℚ) : CPoly ℚ := qNumG z

/-- The denominator coefficient list `qxDen z = z.1.2 ∈ ℚ[x]` of a ℚ(x) element — specialization of `qDenG`. -/
def qxDen (z : QFunNZG ℚ) : CPoly ℚ := qDenG z

/-- The monomial basis `radLogBasis degBound` for the ansatz `N = a₀ + a₁·y`: the `2·(degBound+1)`
elements `[xᵏ, 0]` then `[0, xᵏ]`, giving the matrix columns — specialization of `radLogBasisG`. -/
def radLogBasis (degBound : ℕ) : List (RadElem (QFunNZG ℚ)) :=
  radLogBasisG degBound

/-- The `ℚ`-matrix of the cleared log-derivative system: for each basis column `Nⱼ`, the residual's
cleared numerators `Pᵢⱼ` (common denominator across columns), one row per `x`-power per component, one
column per basis index; a kernel vector gives the coefficients of a solving `N`. -/
def radLogMatrix (ρ : QFunNZG ℚ) (integrand : RadElem (QFunNZG ℚ)) (D : CPoly ℚ)
    (degBound : ℕ) : List (List ℚ) × ℕ :=
  radLogMatrixG ρ integrand D degBound

/-! ### `radLogArgSolve`: compute the log argument `N` (so `u = N/D`) -/

/-- Solve for the log argument: `radLogArgSolve ρ integrand D degBound = some N` with `N = a₀ + a₁·y`
(degree `≤ degBound`) and `∫(integrand) dx = log(N/D)`, by finding a nonzero kernel vector of the
`ℚ`-matrix `radLogMatrix` and reassembling `N = Σⱼ cⱼ Nⱼ`; `none` on trivial kernel. -/
def radLogArgSolve (ρ : QFunNZG ℚ) (integrand : RadElem (QFunNZG ℚ)) (D : CPoly ℚ)
    (degBound : ℕ) : Option (RadElem (QFunNZG ℚ)) :=
  radLogArgSolveG ρ integrand D degBound

/-! ### Solve-then-verify: arcsinh / arccosh / finite-pole

For each target `radLogArgSolve` computes `N`; the computed `u = N/D` is fed to the log-derivative
certificate `radIsLogIntegral` and compared against the closed form. -/

/-- The radicand `ρ = x²+1 ∈ ℚ(x)` (`y = √(x²+1)`), `[1,0,1]`. -/
def radArgRhoArcsinh : QFunNZG ℚ := qxOfNum [1, 0, 1]

/-- The radicand `ρ = x²−1 ∈ ℚ(x)` (`y = √(x²−1)`), `[−1,0,1]`. -/
def radArgRhoArccosh : QFunNZG ℚ := qxOfNum [-1, 0, 1]

/-- The integrand `1/y` of `∫ dx/√(x²+1)`, lifted to `[0, 1/ρ]` over ℚ(x) (`ρ = x²+1`). -/
def radArgIntegrandArcsinh : RadElem (QFunNZG ℚ) := radInvYLift radArgRhoArcsinh CField.one

/-- The integrand `1/y` of `∫ dx/√(x²−1)`, lifted to `[0, 1/ρ]` over ℚ(x) (`ρ = x²−1`). -/
def radArgIntegrandArccosh : RadElem (QFunNZG ℚ) := radInvYLift radArgRhoArccosh CField.one

/-- The computed log argument for `∫ dx/√(x²+1)`: `radLogArgSolve` with `ρ = x²+1`, `D = 1`, ansatz
degree `1` (expected `N = x + y` up to a constant). -/
def radArgSolvedArcsinh : Option (RadElem (QFunNZG ℚ)) :=
  radLogArgSolve radArgRhoArcsinh radArgIntegrandArcsinh [1] 1

-- Computed numerator `N` for arcsinh, expected up to scalar as `x + y`.
#eval (radArgSolvedArcsinh.map (fun N => N.map (fun z => ((qxNum z : List ℚ), (qxDen z : List ℚ)))))

/-- `radLogArgSolve` computes `u = x + y` for `∫ dx/√(x²+1)`: the solved `N` passes the log-derivative
certificate `radIsLogIntegral 2 ρ N integrand = true`. -/
theorem radArg_arcsinh_compute_verify :
    (radArgSolvedArcsinh.map (fun N =>
      radIsLogIntegral 2 radArgRhoArcsinh N radArgIntegrandArcsinh)) = some true := by
  native_decide

/-- The computed log argument for `∫ dx/√(x²−1)`: `radLogArgSolve` with `ρ = x²−1`, `D = 1`, ansatz
degree `1` (expected `N = x + y`). -/
def radArgSolvedArccosh : Option (RadElem (QFunNZG ℚ)) :=
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
def radArgXRho : QFunNZG ℚ := qxOfNum [0, 1, 0, 1]

/-- The integrand `1/(x y)` of `∫ dx/(x√(x²+1))`, lifted to `[0, 1/(x·ρ)]` over ℚ(x). -/
def radArgIntegrandFinite : RadElem (QFunNZG ℚ) := radInvYLift radArgXRho CField.one

/-- The field element `x ∈ ℚ(x)`, `[0,1]` — the fixed denominator `D = x` of the finite-pole case. -/
def radArgXBaseX : QFunNZG ℚ := qxOfNum [0, 1]

/-- The computed log argument for `∫ dx/(x√(x²+1))`: `radLogArgSolve` with `ρ = x²+1`, `D = x`, ansatz
degree `0` (expected `N = y − 1`, so `u = (y − 1)/x`). -/
def radArgSolvedFinite : Option (RadElem (QFunNZG ℚ)) :=
  radLogArgSolve radArgRhoArcsinh radArgIntegrandFinite [0, 1] 0

-- Computed numerator `N` for the finite-pole case, expected up to scalar as `y − 1`.
#eval (radArgSolvedFinite.map (fun N => N.map (fun z => ((qxNum z : List ℚ), (qxDen z : List ℚ)))))

/-- `radLogArgSolve` computes `u = (y − 1)/x` for `∫ dx/(x√(x²+1))` with fixed `D = x`: the solved `N`
(a multiple of `y − 1`) gives `u = N/x` passing the log-derivative certificate; the solve picks the
correct sign `(y − 1)`. -/
theorem radArg_finitePole_compute_verify :
    (radArgSolvedFinite.map (fun N =>
      radIsLogIntegral 2 radArgRhoArcsinh
        [CField.div (N.getD 0 CField.zero) radArgXBaseX,
         CField.div (N.getD 1 CField.zero) radArgXBaseX]
        radArgIntegrandFinite)) = some true := by
  native_decide

/-! #### Matching the computed `N` to the known closed forms -/

/-- The computed arcsinh `N = [a₀, a₁]` is a nonzero constant multiple of `x + y`: `a₁ ≠ 0` and
`a₀ = a₁·x`, matching `u = x + y` up to scalar. -/
theorem radArg_arcsinh_matches_closed_form :
    (radArgSolvedArcsinh.map (fun N =>
      let a0 := N.getD 0 CField.zero
      let a1 := N.getD 1 CField.zero
      (CField.isZero a1 == false) &&
      CField.isZero (CField.sub a0 (CField.mul a1 radArgXBaseX)))) = some true := by
  native_decide

/-! ### Negative control: a non-principal target returns `none`

`∫ dx/(x²·√(x²+1))` has a double pole at `x = 0`; with the bounded ansatz `D = x²`, degree `≤ 1`, there
is no bounded `N/D`, so `radLogArgSolve` returns `none`. -/

/-- The field element `x²·ρ = x²·(x²+1) = x² + x⁴ ∈ ℚ(x)`, `[0,0,1,0,1]` — denominator of the lifted
integrand `1/(x²·y)`. -/
def radArgX2Rho : QFunNZG ℚ := qxOfNum [0, 0, 1, 0, 1]

/-- The integrand `1/(x² y)` of `∫ dx/(x²√(x²+1))`, lifted to `[0, 1/(x²·ρ)]` over `ℚ(x)` (a double
pole at `x = 0`). -/
def radArgIntegrandDouble : RadElem (QFunNZG ℚ) := radInvYLift radArgX2Rho CField.one

/-- The solve for the double-pole target: `radLogArgSolve` with `ρ = x²+1`, `D = x²`, degree `1`
(expected `none`). -/
def radArgSolvedDouble : Option (RadElem (QFunNZG ℚ)) :=
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
