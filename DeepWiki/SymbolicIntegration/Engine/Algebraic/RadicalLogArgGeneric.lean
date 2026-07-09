import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension

/-! # Solving for the log argument `u` over a transcendental tower base

The log-argument solve, generalized off `ℚ` to an arbitrary computable base `[CField β]`. When
`α = CFrac β = β(x)`, the cleared log-derivative system is `β`-linear, so `gaussElim`/`kernelVector`
(the `CField`-generic analogues of `ratRref`/`ratKernelVector`) and `radLogArgSolve` solve it over any
`β`. Over `α = ℚ(x)(eˣ)`, `radLogArgSolve` computes `N = (θ+2) − 2y` for `∫ dx/√(eˣ+1)`,
whose `u = N/θ` passes the log-derivative certificate; the `ℚ`-base instance specializes
to the classical arcsinh log argument. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPoly

/-! ### Generic Gaussian elimination over `[CField β]`: a nonzero kernel vector of a `β`-matrix

`gaussElim`/`kernelVector` row-reduce a `β`-matrix over any `[CField β]` using the engine ops
(`CField.isZero`/`div`/`mul`/`sub`), no `DecidableEq β` needed. The matrix is a `List (List β)` of rows
of length `nCols`. -/

/-- Reduce a `β`-matrix to reduced row-echelon form over `[CField β]`, returning `(rrefRows, pivotCols)`
by Gauss–Jordan with the engine ops over `nCols` columns. The generic analogue of `ratRref`. -/
def gaussElim {β : Type*} [CField β] (nCols : ℕ) (rows : List (List β)) :
    List (List β) × List ℕ :=
  let step : (List (List β) × ℕ × List ℕ) → ℕ → (List (List β) × ℕ × List ℕ) :=
    fun (rs, pr, piv) col =>
      if pr ≥ rs.length then (rs, pr, piv)
      else
        -- find a row index ≥ pr whose `col`-entry is `CField.isZero`-nonzero
        match (List.range rs.length).find?
            (fun i => i ≥ pr && (!CField.isZero (rs[i]!.getD col CField.zero))) with
        | none => (rs, pr, piv)
        | some i =>
          -- swap rows `pr` and `i`
          let rowPr := rs[pr]!
          let rowI := rs[i]!
          let rs := rs.set pr rowI |>.set i rowPr
          -- scale pivot row to a leading `1`
          let pivRow := rs[pr]!
          let lead := pivRow.getD col CField.zero
          let pivRow := pivRow.map (fun a => CField.div a lead)
          let rs := rs.set pr pivRow
          -- eliminate `col` from all other rows
          let rs := (List.range rs.length).foldl (fun acc r =>
            if r = pr then acc
            else
              let row := acc[r]!
              let factor := row.getD col CField.zero
              if CField.isZero factor then acc
              else
                let newRow := (List.range nCols).map (fun c =>
                  CField.sub (row.getD c CField.zero) (CField.mul factor (pivRow.getD c CField.zero)))
                acc.set r newRow) rs
          (rs, pr + 1, col :: piv)
  let (rs, _, pivRev) := (List.range nCols).foldl step (rows, 0, [])
  (rs, pivRev.reverse)

/-- A nonzero kernel vector of a `β`-matrix over `[CField β]`: `kernelVector nCols rows = some c` with
`M·c = 0`, `c ≠ 0`, read off the first free column after `gaussElim`, or `none` for a trivial kernel.
The generic analogue of `ratKernelVector`. -/
def kernelVector {β : Type*} [CField β] (nCols : ℕ) (rows : List (List β)) :
    Option (List β) :=
  let (rs, pivots) := gaussElim nCols rows
  let freeCols := (List.range nCols).filter (fun c => ¬ pivots.contains c)
  match freeCols with
  | [] => none
  | fc :: _ =>
    let base : List β := (List.range nCols).map (fun c =>
      if c = fc then (CField.one : β) else CField.zero)
    let withPivots := (List.range pivots.length).foldl (fun (acc : List β) r =>
      let pc := pivots[r]!
      let v := CField.neg ((rs[r]!).getD fc CField.zero)
      acc.set pc v) base
    some withPivots

/-! ### The generic cleared log-derivative residual + matrix over `α = CFrac β`

Over `α = CFrac β = β(x)`, the residual `radDeriv(N)·D − N·D' − radMul(N, integrand)·D` is a pair of
`β(x)` elements; clearing each to a numerator over `β` gives a `β`-matrix solved by
`gaussElim`/`kernelVector`. The generic analogue of `radLogResidualQ`/`radLogMatrixQ`. -/

section
variable {β : Type*} [CField β] [CFieldDomain β] [CDiffField (CFrac β)]

/-- A `β(x)` value from a numerator: `qOfNum num = num/1 ∈ CFrac β`. The generic analogue of
`qxOfNum`. -/
def qOfNum (num : CPoly β) : CFrac β :=
  ⟨(num, [CField.one]), CFrac.cisZeroG_one_singleton⟩

/-- A `β(x)` value `xᵏ`: numerator the `k`-th monomial, denominator `1`. The generic analogue of
`qxMonomial`. -/
def qMonomial (k : ℕ) : CFrac β := qOfNum (cshift k [(CField.one : β)])

/-- The numerator coefficient list of a `β(x)` element: `qNum z = z.1.1 ∈ CPoly β`. -/
def qNum (z : CFrac β) : CPoly β := z.1.1

/-- The denominator coefficient list of a `β(x)` element: `qDen z = z.1.2 ∈ CPoly β`. -/
def qDen (z : CFrac β) : CPoly β := z.1.2

/-- The cleared log-derivative residual over `α = CFrac β`:
`radLogResidual ρ integrand D N = radDeriv(N)·D − N·D' − radMul(N, integrand)·D`, where
`D' = CDiffField.cderiv (qOfNum D)` is the actual base-field derivation (essential over a tower where
`θ' ≠ 1`, unlike the formal `cderiv`). `β`-linear in `N`; the generic analogue of `radLogResidualQ`. -/
def radLogResidual (ρ : CFrac β) (integrand : RadElem (CFrac β)) (D : CPoly β)
    (N : RadElem (CFrac β)) : RadElem (CFrac β) :=
  let Dq : CFrac β := qOfNum D
  let Dpq : CFrac β := CDiffField.cderiv Dq
  radSub (radSub (radScale Dq (radDeriv 2 ρ N)) (radScale Dpq N))
    (radScale Dq (radMul 2 ρ N integrand))

/-- The monomial basis of numerators over `α = CFrac β`: `radLogBasis degBound` gives the
`2·(degBound+1)` elements `[xᵏ, 0]` then `[0, xᵏ]`. The generic analogue of `radLogBasisQ`. -/
def radLogBasis (degBound : ℕ) : List (RadElem (CFrac β)) :=
  ((List.range (degBound + 1)).map
    (fun k => ([qMonomial k, CField.zero] : RadElem (CFrac β)))) ++
  ((List.range (degBound + 1)).map
    (fun k => ([CField.zero, qMonomial k] : RadElem (CFrac β))))

/-- The `β`-matrix of the cleared log-derivative system over `α = CFrac β`: for each basis column, the
residual's cleared numerators (common denominator across columns), one row per `x`-power per component, one
column per basis index; a kernel vector gives a solving `N`. The generic analogue of `radLogMatrixQ`. -/
def radLogMatrix (ρ : CFrac β) (integrand : RadElem (CFrac β)) (D : CPoly β)
    (degBound : ℕ) : List (List β) × ℕ :=
  let basis := radLogBasis (β := β) degBound
  let nCols := basis.length
  let resids : List (RadElem (CFrac β)) := basis.map (radLogResidual ρ integrand D)
  let rowsForComp : ℕ → List (List β) := fun i =>
    let entryOf : ℕ → CFrac β := fun j => (resids[j]!).getD i CField.zero
    let nums : List (CPoly β) := (List.range nCols).map (fun j => cnorm (qNum (entryOf j)))
    let dens : List (CPoly β) := (List.range nCols).map (fun j => cnorm (qDen (entryOf j)))
    let cleared : List (CPoly β) := (List.range nCols).map (fun j =>
      let prod := (List.range nCols).foldl (fun acc k =>
        if k = j then acc else cmul acc (dens[k]!)) [(CField.one : β)]
      cnorm (cmul (nums[j]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun j => (cleared[j]!).getD r CField.zero))
  let allRows := rowsForComp 0 ++ rowsForComp 1
  let nonzero := allRows.filter (fun row => row.any (fun a => !CField.isZero a))
  (nonzero, nCols)

/-- Solve for the log argument over `α = CFrac β`: `radLogArgSolve ρ integrand D degBound = some N`
with `N = a₀ + a₁·y` (degree `≤ degBound`) and `∫(integrand) dx = log(N/D)`, by finding a nonzero kernel
vector of the `β`-matrix `radLogMatrix` and reassembling `N = Σⱼ cⱼ Nⱼ`; `none` on trivial kernel. The
generic analogue of `radLogArgSolveQ` — the whole solve runs over any tower base `β`. -/
def radLogArgSolve (ρ : CFrac β) (integrand : RadElem (CFrac β)) (D : CPoly β)
    (degBound : ℕ) : Option (RadElem (CFrac β)) :=
  let (rows, nCols) := radLogMatrix ρ integrand D degBound
  match kernelVector nCols rows with
  | none => none
  | some c =>
    let a0 : CFrac β := (List.range (degBound + 1)).foldl (fun acc k =>
      CField.add acc (CField.mul (qOfNum [c.getD k CField.zero]) (qMonomial k))) CField.zero
    let a1 : CFrac β := (List.range (degBound + 1)).foldl (fun acc k =>
      CField.add acc (CField.mul (qOfNum [c.getD (degBound + 1 + k) CField.zero]) (qMonomial k)))
      CField.zero
    some [a0, a1]

end

end DeepWiki.SymbolicIntegration
