import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension
import DeepWiki.ComputableAlgebra.LinearAlgebra

/-! # Solving for the log argument `u` over a transcendental tower base

The log-argument solve, generalized off `ℚ` to an arbitrary computable base `[CField β]` and
represented fraction field `F β`. The cleared log-derivative system is `β`-linear, so `radLogArgSolve`
selects its nullspace computation through `CLinearSolve β`. Over `α = ℚ(x)(eˣ)`, it computes
`N = (θ+2) − 2y` for `∫ dx/√(eˣ+1)`,
whose `u = N/θ` passes the log-derivative certificate; the `ℚ`-base instance specializes
to the classical arcsinh log argument. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

universe u

/-! ### The generic cleared log-derivative residual and matrix over `α = F β`

The residual `radDeriv(N)·D − N·D' − radMul(N, integrand)·D` is a pair of represented fractions over
`β`; clearing each to a numerator in representation `P` gives a `β`-matrix solved by
the selected `CLinearSolve.nullspaceBasis` operation. -/

section
variable {β : Type u} [CField β] [CLinearSolve β]
variable {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
variable [CPoly P] [CPolyEngine P] [CFrac F P] [LawfulCFrac F P]
variable [CFieldDomain β P] [CDiffField (F β)]

/-- The represented fraction `xᵏ`: numerator the `k`-th monomial, denominator `1`. -/
private def qMonomial (k : ℕ) : F β :=
  CFrac.ofPoly (CPolyEngine.monomial (P := P) (CCommRing.one : β) k)

/-- The cleared log-derivative residual over `α = F β`:
`radLogResidual ρ integrand D N = radDeriv(N)·D − N·D' − radMul(N, integrand)·D`, where
`D' = CDiffField.cderiv (CFrac.ofPoly D)` is the actual base-field derivation (essential over a tower where
`θ' ≠ 1`, unlike the formal `cderiv`). `β`-linear in `N`. -/
def radLogResidual (ρ : F β) (integrand : RadElem (F β)) (D : P β)
    (N : RadElem (F β)) : RadElem (F β) :=
  let Dq : F β := CFrac.ofPoly D
  let Dpq : F β := CDiffField.cderiv Dq
  DensePoly.csub (DensePoly.csub (DensePoly.cscale Dq (radDeriv 2 ρ N)) (DensePoly.cscale Dpq N))
    (DensePoly.cscale Dq (radMul 2 ρ N integrand))

/-- The monomial basis of numerators over `α = F β`: `radLogBasis degBound` gives the
`2·(degBound+1)` elements `[xᵏ, 0]` then `[0, xᵏ]`. -/
private def radLogBasis (degBound : ℕ) : List (RadElem (F β)) :=
  ((List.range (degBound + 1)).map
    (fun k => ([qMonomial (F := F) (P := P) k, CCommRing.zero] : RadElem (F β)))) ++
  ((List.range (degBound + 1)).map
    (fun k => ([CCommRing.zero, qMonomial (F := F) (P := P) k] : RadElem (F β))))

/-- The `β`-matrix of the cleared log-derivative system over `α = F β`: for each basis column, the
residual's cleared numerators (common denominator across columns), one row per `x`-power per component, one
column per basis index; a kernel vector gives a solving `N`. -/
def radLogMatrix (ρ : F β) (integrand : RadElem (F β)) (D : P β)
    (degBound : ℕ) : List (List β) × ℕ :=
  let basis := radLogBasis (F := F) (P := P) (β := β) degBound
  let nCols := basis.length
  let resids : List (RadElem (F β)) := basis.map (radLogResidual ρ integrand D)
  let rowsForComp : ℕ → List (List β) := fun i =>
    let entryOf : ℕ → F β := fun j => (resids[j]!).getD i CCommRing.zero
    let nums : List (P β) := (List.range nCols).map (fun j => CPolyEngine.cnorm (CFrac.num (entryOf j)))
    let dens : List (P β) := (List.range nCols).map (fun j => CPolyEngine.cnorm (CFrac.den (entryOf j)))
    let cleared : List (P β) := (List.range nCols).map (fun j =>
      let prod := (List.range nCols).foldl (fun acc k =>
        if k = j then acc else CPolyEngine.mul acc (dens.getD k CPoly.czero)) (CPoly.one : P β)
      CPolyEngine.cnorm (CPolyEngine.mul (nums.getD j CPoly.czero) prod))
    let width := cleared.foldl (fun acc p => max acc (CPoly.degBound p)) 0
    (List.range width).map (fun r =>
      (List.range nCols).map (fun j => CPoly.coeff (cleared.getD j CPoly.czero) r))
  let allRows := rowsForComp 0 ++ rowsForComp 1
  let nonzero := allRows.filter (fun row => row.any (fun a => !CCommRing.isZero a))
  (nonzero, nCols)

/-- Solve for the log argument over `α = F β`: `radLogArgSolve ρ integrand D degBound = some N`
with `N = a₀ + a₁·y` (degree `≤ degBound`) and `∫(integrand) dx = log(N/D)`, by finding a nonzero kernel
vector selected from the `β`-matrix `radLogMatrix` and reassembling `N = Σⱼ cⱼ Nⱼ`; `none` on a trivial
kernel. The whole solve depends only on the abstract linear-solver capability. -/
def radLogArgSolve (ρ : F β) (integrand : RadElem (F β)) (D : P β)
    (degBound : ℕ) : Option (RadElem (F β)) :=
  let (rows, nCols) := radLogMatrix ρ integrand D degBound
  match kernelVector nCols rows with
  | none => none
  | some c =>
    let a0 : F β := (List.range (degBound + 1)).foldl (fun acc k =>
      CCommRing.add acc (CCommRing.mul
        (CFrac.ofPoly (CPolyEngine.ofCoeffList (P := P) [c.getD k CCommRing.zero]))
        (qMonomial (F := F) (P := P) k))) CCommRing.zero
    let a1 : F β := (List.range (degBound + 1)).foldl (fun acc k =>
      CCommRing.add acc (CCommRing.mul
        (CFrac.ofPoly (CPolyEngine.ofCoeffList (P := P) [c.getD (degBound + 1 + k) CCommRing.zero]))
        (qMonomial (F := F) (P := P) k)))
      CCommRing.zero
    some [a0, a1]

end

end DeepWiki.SymbolicIntegration
