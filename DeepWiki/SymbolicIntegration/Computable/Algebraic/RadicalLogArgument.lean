import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogIntegral

/-! # Solving for the log argument `u` in `∫ = log u` (principal case)

The log-derivative condition `∫(integrand) dx = log(N/D)` is `ℚ`-linear in the numerator `N = a₀ + a₁·y`:
clearing `D`, it is `radDeriv(N)·D − N·D' − radMul(N, integrand)·D = 0`. `radLogArgSolve` sets up this
finite homogeneous `ℚ`-linear system on a bounded monomial ansatz, finds a nonzero kernel vector by
Gaussian elimination, and returns `N` (so `u = N/D`), or `none` when the principal ansatz has trivial
kernel. Each solve is validated by the log-derivative certificate `radIsLogIntegral`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

/-! ### Gaussian elimination over ℚ: a nonzero kernel vector of a ℚ-matrix

`ratKernelVector` row-reduces the matrix and reads a kernel vector off a free column, or returns `none`
for a trivial kernel. -/

/-- Reduce a `ℚ`-matrix to reduced row-echelon form, returning `(rrefRows, pivotCols)` by Gauss–Jordan
over `nCols` columns. -/
def ratRref (nCols : ℕ) (rows : List (List ℚ)) : List (List ℚ) × List ℕ :=
  -- mutable-style fold over columns, carrying (current rows, next pivot row index, pivot cols rev)
  let step : (List (List ℚ) × ℕ × List ℕ) → ℕ → (List (List ℚ) × ℕ × List ℕ) :=
    fun (rs, pr, piv) col =>
      if pr ≥ rs.length then (rs, pr, piv)
      else
        -- find a row index ≥ pr whose `col`-entry is nonzero
        match (List.range rs.length).find? (fun i => i ≥ pr && (rs[i]!.getD col 0 ≠ 0)) with
        | none => (rs, pr, piv)
        | some i =>
          -- swap rows `pr` and `i`
          let rowPr := rs[pr]!
          let rowI := rs[i]!
          let rs := rs.set pr rowI |>.set i rowPr
          -- scale pivot row to leading 1
          let pivRow := rs[pr]!
          let lead := pivRow.getD col 0
          let pivRow := pivRow.map (fun a => a / lead)
          let rs := rs.set pr pivRow
          -- eliminate `col` from all other rows
          let rs := (List.range rs.length).foldl (fun acc r =>
            if r = pr then acc
            else
              let row := acc[r]!
              let factor := row.getD col 0
              if factor = 0 then acc
              else
                let newRow := (List.range nCols).map (fun c =>
                  (row.getD c 0) - factor * (pivRow.getD c 0))
                acc.set r newRow) rs
          (rs, pr + 1, col :: piv)
  let (rs, _, pivRev) := (List.range nCols).foldl step (rows, 0, [])
  (rs, pivRev.reverse)

/-- A nonzero kernel vector of a `ℚ`-matrix: `ratKernelVector nCols rows = some c` with `M·c = 0`,
`c ≠ 0`, read off the first free column after `ratRref`, or `none` for a trivial kernel. -/
def ratKernelVector (nCols : ℕ) (rows : List (List ℚ)) : Option (List ℚ) :=
  let (rs, pivots) := ratRref nCols rows
  let freeCols := (List.range nCols).filter (fun c => ¬ pivots.contains c)
  match freeCols with
  | [] => none
  | fc :: _ =>
    -- pivot variable `pivots[r]` is determined by row `r`: c[pivots[r]] = − rs[r][fc]
    let base : List ℚ := (List.range nCols).map (fun c => if c = fc then (1 : ℚ) else 0)
    let withPivots := (List.range pivots.length).foldl (fun (acc : List ℚ) r =>
      let pc := pivots[r]!
      let v := - ((rs[r]!).getD fc 0)
      acc.set pc v) base
    some withPivots

/-! ### Extracting the ℚ-linear system from the cleared log-derivative relation

The residual `radLogResidual ρ integrand D N = radDeriv(N)·D − N·D' − radMul(N, integrand)·D` is
`ℚ`-linear in `N`; evaluating it on the monomial basis and clearing each `ℚ(x)` entry to a polynomial
numerator gives the `ℚ`-matrix of the system. -/

/-- The ℚ(x) value `xᵏ`: numerator the `k`-th monomial `[0,…,0,1]`, denominator `1`. -/
def qxMonomial (k : ℕ) : QFunNZG ℚ := qxOfNum (cshiftG k [(1 : ℚ)])

/-- The cleared log-derivative residual `radLogResidual ρ integrand D N = radDeriv(N)·D − N·D' −
radMul(N, integrand)·D` in `(QFunNZG ℚ)[y]/(y² − ρ)`, whose vanishing says `∫(integrand) dx = log(N/D)`;
`ℚ`-linear in `N`. -/
def radLogResidual (ρ : QFunNZG ℚ) (integrand : RadElem (QFunNZG ℚ)) (D : CPolyG ℚ)
    (N : RadElem (QFunNZG ℚ)) : RadElem (QFunNZG ℚ) :=
  let Dq : QFunNZG ℚ := qxOfNum D
  let Dpq : QFunNZG ℚ := qxOfNum (cderivG D)
  radSub (radSub (radScale Dq (radDeriv 2 ρ N)) (radScale Dpq N))
    (radScale Dq (radMul 2 ρ N integrand))

/-- The numerator coefficient list `qxNum z = z.1.1 ∈ ℚ[x]` of a ℚ(x) element. -/
def qxNum (z : QFunNZG ℚ) : CPolyG ℚ := z.1.1

/-- The denominator coefficient list `qxDen z = z.1.2 ∈ ℚ[x]` of a ℚ(x) element. -/
def qxDen (z : QFunNZG ℚ) : CPolyG ℚ := z.1.2

/-- The monomial basis `radLogBasis degBound` for the ansatz `N = a₀ + a₁·y`: the `2·(degBound+1)`
elements `[xᵏ, 0]` then `[0, xᵏ]`, giving the matrix columns. -/
def radLogBasis (degBound : ℕ) : List (RadElem (QFunNZG ℚ)) :=
  ((List.range (degBound + 1)).map (fun k => ([qxMonomial k, CField.zero] : RadElem (QFunNZG ℚ)))) ++
  ((List.range (degBound + 1)).map (fun k => ([CField.zero, qxMonomial k] : RadElem (QFunNZG ℚ))))

/-- Pad a ℚ-list to length `len` with trailing zeros. -/
def ratPadTo (len : ℕ) (p : List ℚ) : List ℚ :=
  p ++ List.replicate (len - p.length) 0

/-- The `ℚ`-matrix of the cleared log-derivative system: for each basis column `Nⱼ`, the residual's
cleared numerators `Pᵢⱼ` (common denominator across columns), one row per `x`-power per component, one
column per basis index; a kernel vector gives the coefficients of a solving `N`. -/
def radLogMatrix (ρ : QFunNZG ℚ) (integrand : RadElem (QFunNZG ℚ)) (D : CPolyG ℚ)
    (degBound : ℕ) : List (List ℚ) × ℕ :=
  let basis := radLogBasis degBound
  let nCols := basis.length
  -- residual of each basis element, as a length-2 RadElem [r₀, r₁]
  let resids : List (RadElem (QFunNZG ℚ)) := basis.map (radLogResidual ρ integrand D)
  -- build the rows for one component `i ∈ {0,1}`
  let rowsForComp : ℕ → List (List ℚ) := fun i =>
    -- the i-th residual entry of column j (default 0/1 fraction if list too short)
    let entryOf : ℕ → QFunNZG ℚ := fun j => (resids[j]!).getD i CField.zero
    -- numerators and denominators per column
    let nums : List (CPolyG ℚ) := (List.range nCols).map (fun j => cnormG (qxNum (entryOf j)))
    let dens : List (CPolyG ℚ) := (List.range nCols).map (fun j => cnormG (qxDen (entryOf j)))
    -- cleared polynomial for column j: num_j · ∏_{k≠j} den_k
    let cleared : List (CPolyG ℚ) := (List.range nCols).map (fun j =>
      let prod := (List.range nCols).foldl (fun acc k =>
        if k = j then acc else cmulG acc (dens[k]!)) [(1 : ℚ)]
      cnormG (cmulG (nums[j]!) prod))
    -- row width = max degree+1 across all cleared polys
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    -- one row per x-power r: [coeff of xʳ in cleared[0], …, cleared[nCols-1]]
    (List.range width).map (fun r =>
      (List.range nCols).map (fun j => (cleared[j]!).getD r 0))
  let allRows := rowsForComp 0 ++ rowsForComp 1
  -- drop all-zero rows (they impose nothing) to keep the rref small
  let nonzero := allRows.filter (fun row => row.any (fun a => a ≠ 0))
  (nonzero, nCols)

/-! ### `radLogArgSolve`: compute the log argument `N` (so `u = N/D`) -/

/-- Solve for the log argument: `radLogArgSolve ρ integrand D degBound = some N` with `N = a₀ + a₁·y`
(degree `≤ degBound`) and `∫(integrand) dx = log(N/D)`, by finding a nonzero kernel vector of the
`ℚ`-matrix `radLogMatrix` and reassembling `N = Σⱼ cⱼ Nⱼ`; `none` on trivial kernel. -/
def radLogArgSolve (ρ : QFunNZG ℚ) (integrand : RadElem (QFunNZG ℚ)) (D : CPolyG ℚ)
    (degBound : ℕ) : Option (RadElem (QFunNZG ℚ)) :=
  let (rows, nCols) := radLogMatrix ρ integrand D degBound
  match ratKernelVector nCols rows with
  | none => none
  | some c =>
    -- assemble a₀ = Σ_{k≤degBound} c[k]·xᵏ, a₁ = Σ_k c[degBound+1+k]·xᵏ
    let a0 : QFunNZG ℚ := (List.range (degBound + 1)).foldl (fun acc k =>
      CField.add acc (CField.mul (qxOfNum [c.getD k 0]) (qxMonomial k))) CField.zero
    let a1 : QFunNZG ℚ := (List.range (degBound + 1)).foldl (fun acc k =>
      CField.add acc (CField.mul (qxOfNum [c.getD (degBound + 1 + k) 0]) (qxMonomial k))) CField.zero
    some [a0, a1]

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
