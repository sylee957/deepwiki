import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGeneric
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogIntegral
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalOverTower
import DeepWiki.SymbolicIntegration.Engine.ElementaryIntegrate
import DeepWiki.ComputableAlgebra.LinearAlgebraRat
import DeepWiki.ComputableAlgebra.FracReprSparse

/-! # Generic radical log-argument examples

Worked `radLogArgSolve` examples over the rational base and an exponential tower base.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### Generic solver over the rational base

At `β = ℚ`, `radLogArgSolve` reproduces the arcsinh solve `∫ dx/√(x²+1) = log(x + y)`, confirming the
generalization is conservative. -/

/-- The radicand `ρ = x²+1 ∈ ℚ(x)` (`y = √(x²+1)`), `[1,0,1]` — the arcsinh case at `β = ℚ`. -/
def genArgRhoArcsinh : DenseFrac ℚ := CFrac.ofPoly [1, 0, 1]

/-- The integrand `1/y` of `∫ dx/√(x²+1)`, lifted to `[0, 1/ρ]` over ℚ(x). -/
def genArgIntegrandArcsinh : RadElem (DenseFrac ℚ) := radInvYLift genArgRhoArcsinh CCommRing.one

/-- The field element `x ∈ ℚ(x)`, `[0,1]` — for matching `N = c·(x + y)`. -/
def genArgX : DenseFrac ℚ := CFrac.ofPoly [0, 1]

/-- The computed arcsinh log argument under the generic solver: `radLogArgSolve` at `β = ℚ`, `ρ = x²+1`,
`D = 1`, ansatz degree `1` (expected `N = x + y`). -/
def genArgSolvedArcsinh : Option (RadElem (DenseFrac ℚ)) :=
  radLogArgSolve genArgRhoArcsinh genArgIntegrandArcsinh [1] 1

-- Computed numerator `N` for arcsinh under the generic solver, a multiple of `x + y`.
#eval (genArgSolvedArcsinh.map (fun N => N.map (fun z => ((CFrac.num z : List ℚ), (CFrac.den z : List ℚ)))))

/-- `radLogArgSolve` computes `u = x + y` for `∫ dx/√(x²+1)` at `β = ℚ`: the solved `N` passes the
log-derivative certificate, reproducing the `ℚ`-base solve. -/
theorem genArg_arcsinh_isLogIntegral :
    (genArgSolvedArcsinh.map (fun N =>
      radIsLogIntegral 2 genArgRhoArcsinh N genArgIntegrandArcsinh)) = some true := by
  native_decide

/-- The generic-solved arcsinh `N = [a₀, a₁]` is a nonzero constant multiple of `x + y`: `a₁ ≠ 0` and
`a₀ = a₁·x`. -/
theorem genArg_arcsinh_matches_closed_form :
    (genArgSolvedArcsinh.map (fun N =>
      let a0 := N.getD 0 CCommRing.zero
      let a1 := N.getD 1 CCommRing.zero
      (CCommRing.isZero a1 == false) &&
      CCommRing.isZero (CField.sub a0 (CCommRing.mul a1 genArgX)))) = some true := by
  native_decide

/-! ### Sparse representation validation -/

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let ρ : SparseFrac ℚ := CFrac.ofPoly (ofList [1, 0, 1])
    let integrand : RadElem (SparseFrac ℚ) := radInvYLift ρ CCommRing.one
    ((radLogArgSolve ρ integrand (ofList [1]) 1).isSome,
      (cIntegrateElementary ρ ([] : RadElem (SparseFrac ℚ)) integrand CCommRing.one
        (ofList [1]) 1).logTerms.length) = (true, 1) := by
  ccompute

/-! ### Compute `∫ dx/√(eˣ+1) = log((y−1)/(y+1))` over `α = ℚ(x)(eˣ)`

`β = ℚ(x)`, `α = ℚ(x)(eˣ)`, `θ = eˣ`, `ρ = θ+1`, `y² = ρ`, with the exponential derivation
`expTowerDiff`. The integrand `1/y` lifts to `[0, 1/ρ]`; the log argument is `u = (y−1)/(y+1) =
((θ+2) − 2y)/θ`, so `N = (θ+2) − 2y`, `D = θ`. The whole solve runs over `β = ℚ(x)`, and the computed
`u = N/θ` passes the log-derivative certificate. -/

/-- The fixed denominator `D = θ = eˣ ∈ ℚ(x)(eˣ)` as a `DensePoly β` (`β = ℚ(x)`): the polynomial `θ = t₁`,
i.e. `[0, 1]`. -/
def expDenTheta : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CCommRing.one]

/-- The integrand `1/√(eˣ+1) = 1/y` lifted to `[0, 1/ρ]` over `α = ℚ(x)(eˣ)` (`ρ = eˣ+1`), the `R/y` form
for the log-derivative system. -/
def expArgIntegrand : RadElem Lvl2 := radInvYLift expRadicand CCommRing.one

/-- The computed log argument for `∫ dx/√(eˣ+1)` over the tower: `radLogArgSolve` at `β = ℚ(x)`,
`α = ℚ(x)(eˣ)`, with `expTowerDiff`, `ρ = eˣ+1`, `D = θ`, ansatz degree `1` (expected `N = (θ+2) − 2y`,
so `u = N/θ = (y−1)/(y+1)`). -/
def expArgSolved : Option (RadElem Lvl2) :=
  letI : CDiffField Lvl2 := expTowerDiff
  radLogArgSolve expRadicand expArgIntegrand expDenTheta 1

-- Computed numerator `N` for `∫ dx/√(eˣ+1)` over the tower, a multiple of `(θ+2) − 2y`.
#eval (expArgSolved.map (fun N => N.map (fun z =>
  ((CFrac.num z).map (fun w => (CFrac.num w : List ℚ)),
   (CFrac.den z).map (fun w => (CFrac.num w : List ℚ))))))

/-- `radLogArgSolve` computes the log argument for `∫ dx/√(eˣ+1)` over `ℚ(x)(eˣ)`: the generic solver,
its Gaussian elimination running over `β = ℚ(x)`, returns `some N`. -/
theorem expArg_solves :
    (expArgSolved.map (fun _ => true)) = some true := by native_decide

/-- The computed `u = N/θ` integrates `∫ dx/√(eˣ+1)` over `ℚ(x)(eˣ)`: the log argument `N` computed by
`radLogArgSolve` yields `u = N/θ` passing the log-derivative certificate at the exponential instance
`expTowerDiff`, i.e. `∫ dx/√(eˣ+1) = log((y−1)/(y+1))`. -/
theorem expArg_isLogIntegral :
    (expArgSolved.map (fun N =>
      @radIsLogIntegral _ _ expTowerDiff 2 expRadicand
        [CField.div (N.getD 0 CCommRing.zero) expTheta,
         CField.div (N.getD 1 CCommRing.zero) expTheta]
        expArgIntegrand)) = some true := by native_decide

/-- The computed tower `N = [a₀, a₁]` is a nonzero constant multiple of `(θ+2) − 2y`: `a₁ ≠ 0` and
`a₀·(−2) = a₁·(θ+2)`, matching `u = (y−1)/(y+1)` up to scalar. -/
theorem expArg_matches_closed_form :
    (expArgSolved.map (fun N =>
      let a0 := N.getD 0 CCommRing.zero
      let a1 := N.getD 1 CCommRing.zero
      (CCommRing.isZero a1 == false) &&
      CCommRing.isZero (CField.sub (CCommRing.mul a0 (CCommRing.neg (CCommRing.add CCommRing.one CCommRing.one)))
        (CCommRing.mul a1 (CCommRing.add expTheta (CCommRing.add CCommRing.one CCommRing.one)))))) = some true := by
  native_decide

/-! ### Axiom audit for the generic log-argument solver -/

-- The generic solver reproduces `radLogArgSolve` at `β = ℚ`.
#print axioms genArg_arcsinh_isLogIntegral
#print axioms genArg_arcsinh_matches_closed_form

-- The log argument computed over the tower `α = ℚ(x)(eˣ)`.
#print axioms expArg_solves
#print axioms expArg_isLogIntegral
#print axioms expArg_matches_closed_form

end DeepWiki.SymbolicIntegration
