import DeepWiki.SymbolicIntegration.ComputableRadicalLogIntegral

/-! # Algebraic-function integration: COMPUTING the LOG ARGUMENT `u` for `∫ = log u` (principal case)

`ComputableRadicalLogIntegral` **verifies** a *given* log argument `u`: it checks `∫(integrand) dx =
log u` through the log-derivative certificate `radIsLogIntegral u integrand` (`radDeriv u = radMul u
integrand`). This file takes the next step — **SOLVING** for `u` rather than being handed it — for the
**principal case** (a bounded polynomial ansatz exists, no `(1/m)·log` torsion needed).

**The key insight: the log-derivative condition is LINEAR in `u`.** Write `u = N/D` with `D ∈ ℚ[x]` a
fixed denominator and `N = a₀ + a₁·y` (`a₀, a₁ ∈ ℚ[x]`, the radical-extension numerator). Clearing `D`,
`∫(integrand) dx = log(N/D)` iff

  **`radDeriv(N)·D − N·D' − radMul(N, integrand)·D = 0`**   (in `α[y]/(y² − ρ)`),

the cleared log-derivative relation. Each piece (`radDeriv`, `radMul` by the *fixed* `integrand`,
scaling by `D`/`D'`) is **ℚ-linear in `N`**, so with `a₀, a₁` of bounded degree (an *undetermined-
coefficients* ansatz) the relation is a **finite homogeneous ℚ-linear system** in the coefficients of
`a₀, a₁`. A nonzero kernel vector of that system **is** the answer `N` (hence `u = N/D`) — log arguments
are determined only up to a multiplicative constant (`log(cu) = log c + log u`, same derivative), so a
1-dimensional kernel is exactly right.

**`radLogArgSolve`** sets up this system (by evaluating the residual on the monomial **basis**
`Nⱼ ∈ {[xᵏ, 0], [0, xᵏ]}`, since the residual is ℚ-linear — `residual(Σ cⱼ Nⱼ) = Σ cⱼ·residual(Nⱼ)`),
extracts the ℚ-matrix (clearing each rational-function entry to a polynomial numerator and reading off
`x`-power coefficients), and SOLVES it by a small **custom Gaussian elimination over ℚ** finding a
nonzero kernel vector. It returns `N` (so `u = N/D`), or `none` when the kernel is trivial at the chosen
degree bound (⇒ the principal case fails — `(1/m)·log` torsion is needed, OUT OF SCOPE).

**Compute-then-verify** (`native_decide`): for each worked target, `radLogArgSolve` **computes** `N`, and
then the *same* log-derivative certificate `radIsLogIntegral` of `ComputableRadicalLogIntegral` confirms
the computed `u = N/D` integrates the integrand — `u` is OUTPUT, not input:

* `∫ dx/√(x²+1) = log(x + y)` (`arcsinh`): `ρ = x²+1`, `D = 1`, ansatz degree `1` ⇒ solved `N = x + y`.
* `∫ dx/√(x²−1) = log(x + y)` (`arccosh`): `ρ = x²−1`, `D = 1`, ⇒ solved `N = x + y`.
* `∫ dx/(x√(x²+1)) = log((y − 1)/x)` (finite pole at `x = 0`): `ρ = x²+1`, `D = x`, ⇒ solved `N = y − 1`.

**Negative control.** `∫ dx/(x²·√(x²+1))` has a *double* pole at `x = 0`; its log part (if any) is
non-principal at the bounded ansatz `D = x²`, degree `≤ 1` — `radLogArgSolve` returns `none`, the
**torsion boundary** (a bounded `N/D` with `D = x²` cannot match the double pole through `df/f`).

**Honest scope.** This delivers the *principal-case* log argument `u` by the linear solve, self-validated
by the log-derivative check — the engine now **computes** the actual `∫ = log u` answer for these. The
**general degree bounds** (how large the ansatz must be) and the **non-principal / torsion case**
(Trager Ch. 5 §3 divisors / Ch. 6 points-of-finite-order) remain deferred. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

/-! ### A small Gaussian elimination over ℚ: a nonzero kernel vector of a ℚ-matrix

The undetermined-coefficient system is a tiny homogeneous ℚ-linear system `M · c = 0`; we need a
**nonzero** solution `c` (a kernel vector), which then assembles into the log-argument numerator `N`.
`ratKernelVector` row-reduces `M` (a `List (List ℚ)`, each inner list a row of length `nCols`) to
reduced echelon form, identifies the pivot columns, and reads a kernel vector off a **free** column
(setting that free variable to `1`, the others to `0`, and back-substituting the pivots). Returns the
first such vector, or `none` if every column is a pivot (trivial kernel). All ℚ-arithmetic — exact,
fuel-free, `native_decide`-able. -/

/-- **Reduce a matrix to reduced row-echelon form over ℚ**, returning `(rrefRows, pivotCols)`: the
row-reduced rows and the list of pivot column indices (in increasing order). Standard
Gauss–Jordan — for each column, find a row at or below the current pivot row with a nonzero entry, swap
it up, scale it to a leading `1`, and eliminate that column from every *other* row. `nCols` is the
number of columns. Exact ℚ-arithmetic. -/
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

/-- **A nonzero kernel vector of a ℚ-matrix** `ratKernelVector nCols rows = some c` with `M · c = 0`,
`c ≠ 0`, or `none` if the kernel is trivial (every column a pivot). After `ratRref`, a **free** column
`fc` (not a pivot) yields a kernel vector: set `c[fc] = 1`, each pivot variable `c[pc] = −(entry of its
pivot row at `fc`)`, and all other free variables `0`. Returns the vector for the *first* free column.
Exact ℚ-arithmetic, fuel-free. -/
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

The residual of a numerator `N` (a `RadElem (QFunNZG ℚ)`) against a fixed `(ρ, integrand, D)` is

  `radLogResidual ρ integrand D N = radDeriv(N)·D − N·D' − radMul(N, integrand)·D`,

a `RadElem (QFunNZG ℚ) = [r₀, r₁]` of two ℚ(x) elements; `N` solves the log-derivative condition iff
both `rᵢ = 0`. The residual is ℚ-linear in `N`, so evaluating it on the monomial **basis**
`Nⱼ ∈ {[xᵏ,0]} ∪ {[0,xᵏ]}` (degree `≤ degBound` each side) gives the columns of the matrix. To turn
`Σⱼ cⱼ rᵢⱼ = 0` (an equation between ℚ(x) elements) into ℚ-linear rows, each `rᵢⱼ = nᵢⱼ/dᵢⱼ` is cleared
to the polynomial `Pᵢⱼ = nᵢⱼ · ∏_{k≠j} dᵢₖ ∈ ℚ[x]` (common denominator over the columns), and the rows
are the `x`-power coefficients of `Σⱼ cⱼ Pᵢⱼ`. -/

/-- **A ℚ(x) value `xᵏ`** (`QFunNZG ℚ`) — numerator the `k`-th monomial `[0,…,0,1]`, denominator `1`. -/
def qxMonomial (k : ℕ) : QFunNZG ℚ := qxOfNum (cshiftG k [(1 : ℚ)])

/-- **The cleared log-derivative residual** `radLogResidual ρ integrand D N = radDeriv(N)·D − N·D' −
radMul(N, integrand)·D` in `(QFunNZG ℚ)[y]/(y² − ρ)` (`n = 2`), where `D ∈ ℚ[x]` is lifted to ℚ(x) and
`D' = D.deriv`. The `RadElem` whose vanishing (both coefficients zero as ℚ(x) elements) says
`∫(integrand) dx = log(N/D)`. ℚ-linear in `N`. -/
def radLogResidual (ρ : QFunNZG ℚ) (integrand : RadElem (QFunNZG ℚ)) (D : CPolyG ℚ)
    (N : RadElem (QFunNZG ℚ)) : RadElem (QFunNZG ℚ) :=
  let Dq : QFunNZG ℚ := qxOfNum D
  let Dpq : QFunNZG ℚ := qxOfNum (cderivG D)
  radSub (radSub (radScale Dq (radDeriv 2 ρ N)) (radScale Dpq N))
    (radScale Dq (radMul 2 ρ N integrand))

/-- **The numerator coefficient list of a ℚ(x) element** `qxNum z = z.1.1 ∈ ℚ[x]` (a `List ℚ`) — the
fraction's numerator polynomial. -/
def qxNum (z : QFunNZG ℚ) : CPolyG ℚ := z.1.1

/-- **The denominator coefficient list of a ℚ(x) element** `qxDen z = z.1.2 ∈ ℚ[x]` (a `List ℚ`). -/
def qxDen (z : QFunNZG ℚ) : CPolyG ℚ := z.1.2

/-- **The monomial basis of numerators** `radLogBasis degBound` for the degree-`≤ degBound` ansatz
`N = a₀ + a₁·y`: the `2·(degBound+1)` `RadElem`s `[xᵏ, 0]` (`k = 0…degBound`, the `a₀`-monomials) then
`[0, xᵏ]` (the `a₁`-monomials). Evaluating the residual on these gives the matrix columns (the residual
is ℚ-linear in `N`). -/
def radLogBasis (degBound : ℕ) : List (RadElem (QFunNZG ℚ)) :=
  ((List.range (degBound + 1)).map (fun k => ([qxMonomial k, CField.zero] : RadElem (QFunNZG ℚ)))) ++
  ((List.range (degBound + 1)).map (fun k => ([CField.zero, qxMonomial k] : RadElem (QFunNZG ℚ))))

/-- **Pad a ℚ-list to length `len`** with trailing zeros (so coefficient lists of differing degree align
into matrix rows). -/
def ratPadTo (len : ℕ) (p : List ℚ) : List ℚ :=
  p ++ List.replicate (len - p.length) 0

/-- **The ℚ-matrix of the cleared log-derivative system** `radLogMatrix ρ integrand D degBound`. For each
basis column `Nⱼ` (`radLogBasis`), the residual `radLogResidual … Nⱼ = [r₀ⱼ, r₁ⱼ]` gives, per component
`i`, the cleared numerator `Pᵢⱼ = num(rᵢⱼ)·∏_{k≠j} den(rᵢₖ) ∈ ℚ[x]` (common denominator across columns).
The matrix has one **row per `x`-power per component `i ∈ {0,1}`**, and one **column per basis index**;
entry `(row, j)` is the coefficient of that `x`-power in `Pᵢⱼ`. A kernel vector `c` of this matrix gives
the coefficients of a numerator `N = Σⱼ cⱼ Nⱼ` solving the log-derivative condition. -/
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

/-! ### `radLogArgSolve`: COMPUTE the log argument `N` (so `u = N/D`) -/

/-- **★ Solve for the log argument** `radLogArgSolve ρ integrand D degBound = some N` — the radical-
extension numerator `N = a₀ + a₁·y` (`a₀, a₁ ∈ ℚ[x]`, degree `≤ degBound`) with `∫(integrand) dx =
log(N/D)`, **computed** by solving the cleared log-derivative linear system
`radDeriv(N)·D − N·D' − radMul(N,integrand)·D = 0`. Builds the ℚ-matrix `radLogMatrix` (undetermined
coefficients on the monomial basis), finds a nonzero **kernel vector** `c` by Gaussian elimination
(`ratKernelVector`), and reassembles `N = Σⱼ cⱼ Nⱼ` — the kernel basis `Nⱼ` being `[xᵏ,0]`/`[0,xᵏ]`, so
`a₀ = Σ_{k} c_k·xᵏ`, `a₁ = Σ_k c_{degBound+1+k}·xᵏ`. Returns `none` when the kernel is trivial
(principal-case ansatz fails at this `degBound` ⇒ torsion needed, OUT OF SCOPE). The OUTPUT is `u =
N/D` — `u` is computed, not supplied. -/
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

/-! ### ★ COMPUTE-then-VERIFY: arcsinh / arccosh / finite-pole (`native_decide`)

For each worked target, `radLogArgSolve` **computes** the numerator `N`; the computed `u = N/D` is then
fed to the *same* log-derivative certificate `radIsLogIntegral` (`ComputableRadicalLogIntegral`) and to a
direct comparison against the known closed form. `u` is the engine's OUTPUT. -/

/-- The radicand `ρ = x²+1 ∈ ℚ(x)` (`y = √(x²+1)`), `[1,0,1]`. -/
def radArgRhoArcsinh : QFunNZG ℚ := qxOfNum [1, 0, 1]

/-- The radicand `ρ = x²−1 ∈ ℚ(x)` (`y = √(x²−1)`), `[−1,0,1]`. -/
def radArgRhoArccosh : QFunNZG ℚ := qxOfNum [-1, 0, 1]

/-- The integrand `1/y` of `∫ dx/√(x²+1)`, lifted to `[0, 1/ρ]` over ℚ(x) (`ρ = x²+1`). -/
def radArgIntegrandArcsinh : RadElem (QFunNZG ℚ) := radInvYLift radArgRhoArcsinh CField.one

/-- The integrand `1/y` of `∫ dx/√(x²−1)`, lifted to `[0, 1/ρ]` over ℚ(x) (`ρ = x²−1`). -/
def radArgIntegrandArccosh : RadElem (QFunNZG ℚ) := radInvYLift radArgRhoArccosh CField.one

/-- **The COMPUTED log argument for `∫ dx/√(x²+1)`** — `radLogArgSolve` with `ρ = x²+1`, `D = 1`,
ansatz degree `1`, returning `some N`. Expected (up to a constant) `N = x + y`. -/
def radArgSolvedArcsinh : Option (RadElem (QFunNZG ℚ)) :=
  radLogArgSolve radArgRhoArcsinh radArgIntegrandArcsinh [1] 1

-- Sanity print: the computed numerator `N` for arcsinh (should be a constant multiple of `x + y`).
#eval (radArgSolvedArcsinh.map (fun N => N.map (fun z => ((qxNum z : List ℚ), (qxDen z : List ℚ)))))

/-- **★ `radLogArgSolve` COMPUTES `u = x + y` for `∫ dx/√(x²+1)`** (`native_decide`): the solver returns
`some N`, and the COMPUTED `u = N/1` passes the log-derivative certificate `radIsLogIntegral 2 ρ N
integrand = true` — i.e. `∫ dx/√(x²+1) = log N`. `N` is the solver's OUTPUT (a nonzero kernel vector of
the cleared linear system), not supplied. THE ENGINE COMPUTES THE ALGEBRAIC-LOG ARGUMENT for the
principal case. -/
theorem radArg_arcsinh_compute_verify :
    (radArgSolvedArcsinh.map (fun N =>
      radIsLogIntegral 2 radArgRhoArcsinh N radArgIntegrandArcsinh)) = some true := by
  native_decide

/-- **The COMPUTED log argument for `∫ dx/√(x²−1)`** — `radLogArgSolve` with `ρ = x²−1`, `D = 1`, ansatz
degree `1`. Expected (up to a constant) `N = x + y` (arccosh). -/
def radArgSolvedArccosh : Option (RadElem (QFunNZG ℚ)) :=
  radLogArgSolve radArgRhoArccosh radArgIntegrandArccosh [1] 1

/-- **★ `radLogArgSolve` COMPUTES `u = x + y` for `∫ dx/√(x²−1)`** (`native_decide`): the solver returns
`some N`, and the COMPUTED `u = N/1` passes the log-derivative certificate — `∫ dx/√(x²−1) = log N`. The
arccosh companion: the same linear solve recovers the log argument from `ρ = x²−1`. -/
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

/-- **The COMPUTED log argument for `∫ dx/(x√(x²+1))`** — `radLogArgSolve` with `ρ = x²+1`, **`D = x`**
(the finite pole at `x = 0`), ansatz degree `0` (`a₀, a₁` constants). Expected (up to a constant)
`N = y − 1`, so `u = (y − 1)/x`. -/
def radArgSolvedFinite : Option (RadElem (QFunNZG ℚ)) :=
  radLogArgSolve radArgRhoArcsinh radArgIntegrandFinite [0, 1] 0

-- Sanity print: the computed numerator `N` for the finite-pole case (a constant multiple of `y − 1`).
#eval (radArgSolvedFinite.map (fun N => N.map (fun z => ((qxNum z : List ℚ), (qxDen z : List ℚ)))))

/-- **★ `radLogArgSolve` COMPUTES `u = (y − 1)/x` for `∫ dx/(x√(x²+1))`** (`native_decide`): the solver,
with the FIXED denominator `D = x`, returns `some N` (a constant multiple of `y − 1`), and the COMPUTED
`u = N/x` passes the log-derivative certificate `radIsLogIntegral 2 ρ (N/x) integrand = true` — i.e.
`∫ dx/(x√(x²+1)) = log((y − 1)/x)`. The genuine FINITE-POLE case: the solve picks the correct sign
`(y − 1)` (not the wrong-sign `(y + 1)`) by which kernel vector zeroes the residual. `u` is the solver's
OUTPUT divided by the fixed `D = x`. THE ENGINE COMPUTES THE FINITE-POLE LOG ARGUMENT. -/
theorem radArg_finitePole_compute_verify :
    (radArgSolvedFinite.map (fun N =>
      radIsLogIntegral 2 radArgRhoArcsinh
        [CField.div (N.getD 0 CField.zero) radArgXBaseX,
         CField.div (N.getD 1 CField.zero) radArgXBaseX]
        radArgIntegrandFinite)) = some true := by
  native_decide

/-! #### Matching the computed `N` to the known closed forms -/

/-- **★ The computed arcsinh `N` is a nonzero constant multiple of `x + y`** (`native_decide`): the
solver's `N = [a₀, a₁]` satisfies `a₀ = c·x` and `a₁ = c` for one nonzero `c ∈ ℚ` — i.e. `N = c·(x + y)`
— matching the known closed form `u = x + y` exactly (up to the log argument's intrinsic scalar freedom).
Checked by `a₁ ≠ 0` and `a₀ = a₁·x` (so `a₀/a₁ = x`). -/
theorem radArg_arcsinh_matches_closed_form :
    (radArgSolvedArcsinh.map (fun N =>
      let a0 := N.getD 0 CField.zero
      let a1 := N.getD 1 CField.zero
      (CField.isZero a1 == false) &&
      CField.isZero (CField.sub a0 (CField.mul a1 radArgXBaseX)))) = some true := by
  native_decide

/-! ### ★ Negative control: a non-principal target returns `none` (the torsion boundary, `native_decide`)

`∫ dx/(x²·√(x²+1))` has a **double** pole at `x = 0`. With the bounded ansatz `D = x²`, degree `≤ 1`,
there is no `N/D` whose logarithmic derivative is the integrand (the `df/f` form of a double pole needs a
non-principal divisor — the `(1/m)·log` torsion). So `radLogArgSolve` finds only the trivial kernel and
returns `none` — exactly the principal-case boundary. -/

/-- The field element `x²·ρ = x²·(x²+1) = x² + x⁴ ∈ ℚ(x)`, `[0,0,1,0,1]` — denominator of the lifted
integrand `1/(x²·y)`. -/
def radArgX2Rho : QFunNZG ℚ := qxOfNum [0, 0, 1, 0, 1]

/-- The integrand `1/(x² y)` of `∫ dx/(x²√(x²+1))`, lifted to `[0, 1/(x²·ρ)]` over ℚ(x) — a DOUBLE pole
at `x = 0`. -/
def radArgIntegrandDouble : RadElem (QFunNZG ℚ) := radInvYLift radArgX2Rho CField.one

/-- **The solve for the double-pole target** — `radLogArgSolve` with `ρ = x²+1`, `D = x²`, degree `1`.
Expected `none` (non-principal at this ansatz). -/
def radArgSolvedDouble : Option (RadElem (QFunNZG ℚ)) :=
  radLogArgSolve radArgRhoArcsinh radArgIntegrandDouble [0, 0, 1] 1

/-- **★ Negative control: the double-pole target has NO bounded log argument** (`native_decide`):
`radLogArgSolve (ρ = x²+1) (1/(x²y)) (D = x²) 1 = none` — the cleared linear system has only the trivial
kernel, so no `N/x²` (degree `≤ 1` numerator) satisfies the log-derivative condition. `∫ dx/(x²√(x²+1))`
is **non-principal** at this degree bound: its log part needs the `(1/m)·log` divisor/torsion machinery
(Trager Ch. 5–6), OUT OF SCOPE. This is the boundary of the principal-case linear solve. -/
theorem radArg_double_pole_none :
    radArgSolvedDouble = none := by
  native_decide

/-! ### `#print axioms` — does the engine COMPUTE log arguments?

The compute-then-verify theorems carry the standard `[propext, Classical.choice, Quot.sound]` plus the
`native_decide` compiler axiom — no `sorry`, no extra axiom. **The engine now COMPUTES the log argument
`u`** (the actual `∫ = log u` answer) for the **principal case**, by the linear solve `radLogArgSolve`,
self-validated by the log-derivative certificate `radIsLogIntegral`: `u = x + y` for arcsinh/arccosh
(`D = 1`) and `u = (y − 1)/x` for the finite-pole `∫ dx/(x√(x²+1))` (`D = x`) — each `u` is the solver's
OUTPUT, not input. The negative control (`∫ dx/(x²√(x²+1))`, double pole) returns `none`, the principal /
torsion boundary. The general degree bounds + the non-principal/torsion case remain deferred. -/

-- ★ The deliverable: log arguments `u` COMPUTED by the linear solve, validated by the log-derivative check:
#print axioms radArg_arcsinh_compute_verify
#print axioms radArg_arccosh_compute_verify
#print axioms radArg_finitePole_compute_verify
#print axioms radArg_arcsinh_matches_closed_form
#print axioms radArg_double_pole_none

end DeepWiki.SymbolicIntegration
