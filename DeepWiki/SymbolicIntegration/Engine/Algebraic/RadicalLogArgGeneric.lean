import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension
import DeepWiki.ComputableAlgebra.LinearAlgebra

/-! # Solving for the log argument `u` over a transcendental tower base

The log-argument solve, generalized off `ℚ` to an arbitrary computable base `[CField β]`. When
`α = DenseFrac β = β(x)`, the cleared log-derivative system is `β`-linear, so `radLogArgSolve`
selects its nullspace computation through `CLinearSolve β`. Over `α = ℚ(x)(eˣ)`, it computes
`N = (θ+2) − 2y` for `∫ dx/√(eˣ+1)`,
whose `u = N/θ` passes the log-derivative certificate; the `ℚ`-base instance specializes
to the classical arcsinh log argument. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### The generic cleared log-derivative residual + matrix over `α = DenseFrac β`

Over `α = DenseFrac β = β(x)`, the residual `radDeriv(N)·D − N·D' − radMul(N, integrand)·D` is a pair of
`β(x)` elements; clearing each to a numerator over `β` gives a `β`-matrix solved by
the selected `CLinearSolve.nullspaceBasis` operation. -/

section
variable {β : Type*} [CField β] [CLinearSolve β]
variable [CFieldDomain β DensePoly] [CDiffField (DenseFrac β)]

/-- A `β(x)` value `xᵏ`: numerator the `k`-th monomial, denominator `1`. -/
def qMonomial (k : ℕ) : DenseFrac β := CFrac.ofPoly (cshift k [(CCommRing.one : β)])

/-- The cleared log-derivative residual over `α = DenseFrac β`:
`radLogResidual ρ integrand D N = radDeriv(N)·D − N·D' − radMul(N, integrand)·D`, where
`D' = CDiffField.cderiv (CFrac.ofPoly D)` is the actual base-field derivation (essential over a tower where
`θ' ≠ 1`, unlike the formal `cderiv`). `β`-linear in `N`. -/
def radLogResidual (ρ : DenseFrac β) (integrand : RadElem (DenseFrac β)) (D : DensePoly β)
    (N : RadElem (DenseFrac β)) : RadElem (DenseFrac β) :=
  let Dq : DenseFrac β := CFrac.ofPoly D
  let Dpq : DenseFrac β := CDiffField.cderiv Dq
  DensePoly.csub (DensePoly.csub (DensePoly.cscale Dq (radDeriv 2 ρ N)) (DensePoly.cscale Dpq N))
    (DensePoly.cscale Dq (radMul 2 ρ N integrand))

/-- The monomial basis of numerators over `α = DenseFrac β`: `radLogBasis degBound` gives the
`2·(degBound+1)` elements `[xᵏ, 0]` then `[0, xᵏ]`. -/
def radLogBasis (degBound : ℕ) : List (RadElem (DenseFrac β)) :=
  ((List.range (degBound + 1)).map
    (fun k => ([qMonomial k, CCommRing.zero] : RadElem (DenseFrac β)))) ++
  ((List.range (degBound + 1)).map
    (fun k => ([CCommRing.zero, qMonomial k] : RadElem (DenseFrac β))))

/-- The `β`-matrix of the cleared log-derivative system over `α = DenseFrac β`: for each basis column, the
residual's cleared numerators (common denominator across columns), one row per `x`-power per component, one
column per basis index; a kernel vector gives a solving `N`. -/
def radLogMatrix (ρ : DenseFrac β) (integrand : RadElem (DenseFrac β)) (D : DensePoly β)
    (degBound : ℕ) : List (List β) × ℕ :=
  let basis := radLogBasis (β := β) degBound
  let nCols := basis.length
  let resids : List (RadElem (DenseFrac β)) := basis.map (radLogResidual ρ integrand D)
  let rowsForComp : ℕ → List (List β) := fun i =>
    let entryOf : ℕ → DenseFrac β := fun j => (resids[j]!).getD i CCommRing.zero
    let nums : List (DensePoly β) := (List.range nCols).map (fun j => cnorm (CFrac.num (entryOf j)))
    let dens : List (DensePoly β) := (List.range nCols).map (fun j => cnorm (CFrac.den (entryOf j)))
    let cleared : List (DensePoly β) := (List.range nCols).map (fun j =>
      let prod := (List.range nCols).foldl (fun acc k =>
        if k = j then acc else cmul acc (dens[k]!)) [(CCommRing.one : β)]
      cnorm (cmul (nums[j]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun j => (cleared[j]!).getD r CCommRing.zero))
  let allRows := rowsForComp 0 ++ rowsForComp 1
  let nonzero := allRows.filter (fun row => row.any (fun a => !CCommRing.isZero a))
  (nonzero, nCols)

/-- Solve for the log argument over `α = DenseFrac β`: `radLogArgSolve ρ integrand D degBound = some N`
with `N = a₀ + a₁·y` (degree `≤ degBound`) and `∫(integrand) dx = log(N/D)`, by finding a nonzero kernel
vector selected from the `β`-matrix `radLogMatrix` and reassembling `N = Σⱼ cⱼ Nⱼ`; `none` on a trivial
kernel. The whole solve depends only on the abstract linear-solver capability. -/
def radLogArgSolve (ρ : DenseFrac β) (integrand : RadElem (DenseFrac β)) (D : DensePoly β)
    (degBound : ℕ) : Option (RadElem (DenseFrac β)) :=
  let (rows, nCols) := radLogMatrix ρ integrand D degBound
  match kernelVector nCols rows with
  | none => none
  | some c =>
    let a0 : DenseFrac β := (List.range (degBound + 1)).foldl (fun acc k =>
      CCommRing.add acc (CCommRing.mul (CFrac.ofPoly [c.getD k CCommRing.zero]) (qMonomial k))) CCommRing.zero
    let a1 : DenseFrac β := (List.range (degBound + 1)).foldl (fun acc k =>
      CCommRing.add acc (CCommRing.mul (CFrac.ofPoly [c.getD (degBound + 1 + k) CCommRing.zero]) (qMonomial k)))
      CCommRing.zero
    some [a0, a1]

end

end DeepWiki.SymbolicIntegration
