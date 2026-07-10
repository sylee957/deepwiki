import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension

/-! # Solving for the log argument `u` over a transcendental tower base

The log-argument solve, generalized off `ℚ` to an arbitrary computable base `[CField β]`. When
`α = DenseFrac β = β(x)`, the cleared log-derivative system is `β`-linear, so `gaussElim`/`kernelVector`
and `radLogArgSolve` solve it over any `β`. Over `α = ℚ(x)(eˣ)`, `radLogArgSolve` computes
`N = (θ+2) − 2y` for `∫ dx/√(eˣ+1)`,
whose `u = N/θ` passes the log-derivative certificate; the `ℚ`-base instance specializes
to the classical arcsinh log argument. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### Generic Gaussian elimination over `[CField β]`: a nonzero kernel vector of a `β`-matrix

`gaussElim`/`kernelVector` row-reduce a `β`-matrix over any `[CField β]` using the engine ops
(`CCommRing.isZero`/`div`/`mul`/`sub`), no `DecidableEq β` needed. The matrix is a `List (List β)` of rows
of length `nCols`. -/

/-- Reduce a `β`-matrix to reduced row-echelon form over `[CField β]`, returning `(rrefRows, pivotCols)`
by Gauss–Jordan with the engine ops over `nCols` columns. -/
def gaussElim {β : Type*} [CField β] (nCols : ℕ) (rows : List (List β)) :
    List (List β) × List ℕ :=
  let step : (List (List β) × ℕ × List ℕ) → ℕ → (List (List β) × ℕ × List ℕ) :=
    fun (rs, pr, piv) col =>
      if pr ≥ rs.length then (rs, pr, piv)
      else
        -- find a row index ≥ pr whose `col`-entry is `CCommRing.isZero`-nonzero
        match (List.range rs.length).find?
            (fun i => i ≥ pr && (!CCommRing.isZero (rs[i]!.getD col CCommRing.zero))) with
        | none => (rs, pr, piv)
        | some i =>
          -- swap rows `pr` and `i`
          let rowPr := rs[pr]!
          let rowI := rs[i]!
          let rs := rs.set pr rowI |>.set i rowPr
          -- scale pivot row to a leading `1`
          let pivRow := rs[pr]!
          let lead := pivRow.getD col CCommRing.zero
          let pivRow := pivRow.map (fun a => CField.div a lead)
          let rs := rs.set pr pivRow
          -- eliminate `col` from all other rows
          let rs := (List.range rs.length).foldl (fun acc r =>
            if r = pr then acc
            else
              let row := acc[r]!
              let factor := row.getD col CCommRing.zero
              if CCommRing.isZero factor then acc
              else
                let newRow := (List.range nCols).map (fun c =>
                  CField.sub (row.getD c CCommRing.zero) (CCommRing.mul factor (pivRow.getD c CCommRing.zero)))
                acc.set r newRow) rs
          (rs, pr + 1, col :: piv)
  let (rs, _, pivRev) := (List.range nCols).foldl step (rows, 0, [])
  (rs, pivRev.reverse)

/-- A nonzero kernel vector of a `β`-matrix over `[CField β]`: `kernelVector nCols rows = some c` with
`M·c = 0`, `c ≠ 0`, read off the first free column after `gaussElim`, or `none` for a trivial kernel. -/
def kernelVector {β : Type*} [CField β] (nCols : ℕ) (rows : List (List β)) :
    Option (List β) :=
  let (rs, pivots) := gaussElim nCols rows
  let freeCols := (List.range nCols).filter (fun c => ¬ pivots.contains c)
  match freeCols with
  | [] => none
  | fc :: _ =>
    let base : List β := (List.range nCols).map (fun c =>
      if c = fc then (CCommRing.one : β) else CCommRing.zero)
    let withPivots := (List.range pivots.length).foldl (fun (acc : List β) r =>
      let pc := pivots[r]!
      let v := CCommRing.neg ((rs[r]!).getD fc CCommRing.zero)
      acc.set pc v) base
    some withPivots

/-! ### The generic cleared log-derivative residual + matrix over `α = DenseFrac β`

Over `α = DenseFrac β = β(x)`, the residual `radDeriv(N)·D − N·D' − radMul(N, integrand)·D` is a pair of
`β(x)` elements; clearing each to a numerator over `β` gives a `β`-matrix solved by
`gaussElim`/`kernelVector`. -/

section
variable {β : Type*} [CField β] [CFieldDomain β] [CDiffField (DenseFrac β)]

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
vector of the `β`-matrix `radLogMatrix` and reassembling `N = Σⱼ cⱼ Nⱼ`; `none` on trivial kernel. The
whole solve runs over any tower base `β`. -/
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
