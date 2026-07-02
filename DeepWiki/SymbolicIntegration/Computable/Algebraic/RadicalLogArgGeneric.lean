import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalLogIntegral
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalOverTower

/-! # COMPUTING the LOG ARGUMENT `u` over a TRANSCENDENTAL TOWER (the grand unification, log part)

`ComputableRadicalLogArgument` **computes** the log argument `u` for `∫(integrand) dx = log u` — but only
over the *single* base level `ℚ(x)`: its Gaussian elimination `ratRref`/`ratKernelVector` is hard-wired to
**ℚ** (the matrix entries are `ℚ` scalars). `ComputableRadicalOverTower` carries the radical's *rational*
part over a genuine transcendental tower (`α = ℚ(x)(eˣ)`), but hands the log argument in by hand. This file
closes the gap: it **COMPUTES the log argument over a tower base**, extending the grand unification from the
rational part to the log part.

**The same linear ansatz; only the SCALAR FIELD generalizes.** The cleared log-derivative relation

  **`radDeriv(N)·D − N·D' − radMul(N, integrand)·D = 0`**   (in `α[y]/(y² − ρ)`),

is linear in `N = a₀ + a₁·y` (`a₀, a₁, D ∈ α`). When the base field is itself a fraction field
`α = QFunNZG β = β(x)` (numerators `CPolyG β`, `x`-power coefficients `β`-elements), the undetermined-
coefficient system is a **homogeneous `β`-linear system** — the matrix entries are `β`-elements, NOT
necessarily ℚ. Extracting it (clear each `α`-component to its numerator over `β`, read off `x`-power
coefficients) and a nonzero **kernel vector** over `β` is the answer `N` (hence `u = N/D`):

* `β = ℚ`, base `α = ℚ(x)`: the original `ComputableRadicalLogArgument` case (matrix over `ℚ`).
* `β = ℚ(x)`, base `α = ℚ(x)(eˣ) = Lvl2`: the **transcendental tower** case (matrix over `ℚ(x)`).

**`gaussElimG`/`kernelVectorG`** mirror `ratRref`/`ratKernelVector` but run over any `[CField β]` — the ℚ
ops (`= 0`, `/`, `*`, `-`) become the engine ops (`CField.isZero`, `cdivG`/`CField.div`, `CField.mul`,
`CField.sub`), so they `native_decide` at `β = ℚ(x)` (a tower level) just as at `β = ℚ`. **`radLogArgSolveG`**
builds the residual/matrix over `α = QFunNZG β` and solves it with `kernelVectorG`, returning `N` or `none`.

**The headline** (`native_decide`): over `α = ℚ(x)(eˣ)`, `θ = eˣ`, `ρ = θ+1`, `y² = ρ`,
`radLogArgSolveG` **computes** `N = (θ+2) − 2y` for `∫ dx/√(eˣ+1)` (`D = θ`), and the computed `u = N/θ`
passes the log-derivative certificate `radIsLogIntegral 2 ρ (N/θ) integrand` — i.e.
`∫ dx/√(eˣ+1) = log((y−1)/(y+1))` **COMPUTED over the transcendental tower**. (`(y−1)/(y+1) = (y−1)²/(ρ−1) =
(ρ−2y+1)/θ`, so `N = (θ+2) − 2y`, `D = θ`.) The ℚ-base classics (arcsinh `u = x + y`) solve identically
under `radLogArgSolveG`, confirming the generalization is conservative.

**Honest scope.** The generic solver + the log-over-tower example is the milestone: the engine now
**computes** log arguments over a transcendental tower (the grand unification extended from rational to log
parts). The general degree bounds and the non-principal / torsion case remain deferred, as in the ℚ-base
file. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

/-! ### Generic Gaussian elimination over `[CField β]`: a nonzero kernel vector of a `β`-matrix

`ratRref`/`ratKernelVector` (`ComputableRadicalLogArgument`) row-reduce a `ℚ`-matrix; `gaussElimG`/
`kernelVectorG` do the same over **any** `[CField β]`. Every ℚ-operation is replaced by the corresponding
engine op — `a ≠ 0 ↦ ¬ CField.isZero a`, `a / lead ↦ CField.div a lead`, `a - factor·b ↦
CField.sub a (CField.mul factor b)`, `0 ↦ CField.zero`, `1 ↦ CField.one` — so the row reduction is pure
`CField`-arithmetic, fuel-free, and `native_decide`-able. No `DecidableEq β` is needed (zero is tested by
`CField.isZero`; the index comparisons are on `ℕ`). The matrix is a `List (List β)`, each inner list a row
of length `nCols`. -/

/-- **Reduce a `β`-matrix to reduced row-echelon form over `[CField β]`**, returning `(rrefRows,
pivotCols)`: the row-reduced rows and the increasing list of pivot column indices. The `[CField β]`-generic
analogue of `ratRref` — Gauss–Jordan with `CField.isZero` for the nonzero test, `CField.div` for the
pivot scaling, and `CField.sub`/`CField.mul` for the elimination. `nCols` is the column count. Pure
`CField`-arithmetic, so it reduces under `native_decide` at any computable tower level `β`. -/
def gaussElimG {β : Type*} [CField β] (nCols : ℕ) (rows : List (List β)) :
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

/-- **A nonzero kernel vector of a `β`-matrix over `[CField β]`** `kernelVectorG nCols rows = some c` with
`M · c = 0`, `c ≠ 0`, or `none` if every column is a pivot (trivial kernel). The `[CField β]`-generic
analogue of `ratKernelVector`: after `gaussElimG`, a **free** column `fc` yields `c[fc] = 1`, each pivot
variable `c[pc] = −(entry of its pivot row at `fc`)` (via `CField.neg`), other free variables `0`. Returns
the vector for the *first* free column. Pure `CField`-arithmetic, fuel-free. -/
def kernelVectorG {β : Type*} [CField β] (nCols : ℕ) (rows : List (List β)) :
    Option (List β) :=
  let (rs, pivots) := gaussElimG nCols rows
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

/-! ### The generic cleared log-derivative residual + matrix over `α = QFunNZG β`

The base field is `α = QFunNZG β = β(x)` (a fraction field whose numerators are `CPolyG β`, whose `x`-power
coefficients are `β`-elements). The numerator `N = a₀ + a₁·y` is a `RadElem (QFunNZG β)`; the residual
`radDeriv(N)·D − N·D' − radMul(N, integrand)·D` is a `RadElem (QFunNZG β) = [r₀, r₁]` of two `β(x)`
elements. Clearing each `rᵢ = nᵢ/dᵢ` to a numerator polynomial over `β` and reading off `x`-power
coefficients gives a **`β`-matrix** — solved by `gaussElimG`/`kernelVectorG`. (At `β = ℚ` this is exactly
`radLogResidual`/`radLogMatrix`; only the scalar field generalizes.) -/

section
variable {β : Type*} [CField β] [CFieldDomain β] [CDiffField (QFunNZG β)]

/-- **A `β(x)` value from a numerator** `qOfNumG num = num/1 ∈ QFunNZG β` (denominator `[1]`,
`cisZeroG`-nonzero by `CFieldDomain`). The `[CField β]`-generic analogue of `qxOfNum` (which is the `β = ℚ`
case). -/
def qOfNumG (num : CPolyG β) : QFunNZG β :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- **A `β(x)` value `xᵏ`** (`QFunNZG β`) — numerator the `k`-th monomial `[0,…,0,1]`, denominator `1`. The
generic analogue of `qxMonomial`. -/
def qMonomialG (k : ℕ) : QFunNZG β := qOfNumG (cshiftG k [(CField.one : β)])

/-- **The numerator coefficient list of a `β(x)` element** `qNumG z = z.1.1 ∈ CPolyG β` (a `List β`). -/
def qNumG (z : QFunNZG β) : CPolyG β := z.1.1

/-- **The denominator coefficient list of a `β(x)` element** `qDenG z = z.1.2 ∈ CPolyG β` (a `List β`). -/
def qDenG (z : QFunNZG β) : CPolyG β := z.1.2

/-- **The cleared log-derivative residual over `α = QFunNZG β`** `radLogResidualG ρ integrand D N =
radDeriv(N)·D − N·D' − radMul(N, integrand)·D` in `(QFunNZG β)[y]/(y² − ρ)`, where `D ∈ CPolyG β` is
lifted to `α = β(x)` (`qOfNumG`) and **`D' = CDiffField.cderiv (qOfNumG D)` is the ACTUAL base-field
derivation** of `D` (NOT the formal `cderivG`). The distinction is invisible at `β = ℚ` (`α = ℚ(x)`,
`x' = 1`, where `cderivG` agrees) but **essential over a transcendental tower**: when `D` is a polynomial in
`θ = t₁` with `θ' ≠ 1` (e.g. `θ = eˣ`, `θ' = θ`), the formal `cderivG` gives the wrong `D'`; routing through
`CDiffField.cderiv` uses the genuine tower derivation (`towerDerivQFunNZG`). The `RadElem` whose vanishing
(both coefficients zero as `β(x)` elements) says `∫(integrand) dx = log(N/D)`. `β`-linear in `N`. The
generic analogue of `radLogResidual`. -/
def radLogResidualG (ρ : QFunNZG β) (integrand : RadElem (QFunNZG β)) (D : CPolyG β)
    (N : RadElem (QFunNZG β)) : RadElem (QFunNZG β) :=
  let Dq : QFunNZG β := qOfNumG D
  let Dpq : QFunNZG β := CDiffField.cderiv Dq
  radSub (radSub (radScale Dq (radDeriv 2 ρ N)) (radScale Dpq N))
    (radScale Dq (radMul 2 ρ N integrand))

/-- **The monomial basis of numerators over `α = QFunNZG β`** `radLogBasisG degBound` for the
degree-`≤ degBound` ansatz `N = a₀ + a₁·y`: the `2·(degBound+1)` `RadElem`s `[xᵏ, 0]` (the `a₀`-monomials)
then `[0, xᵏ]` (the `a₁`-monomials). Evaluating the residual on these gives the matrix columns. The generic
analogue of `radLogBasis`. -/
def radLogBasisG (degBound : ℕ) : List (RadElem (QFunNZG β)) :=
  ((List.range (degBound + 1)).map
    (fun k => ([qMonomialG k, CField.zero] : RadElem (QFunNZG β)))) ++
  ((List.range (degBound + 1)).map
    (fun k => ([CField.zero, qMonomialG k] : RadElem (QFunNZG β))))

/-- **The `β`-matrix of the cleared log-derivative system over `α = QFunNZG β`** `radLogMatrixG ρ integrand
D degBound`. For each basis column `Nⱼ` (`radLogBasisG`), the residual `radLogResidualG … Nⱼ = [r₀ⱼ, r₁ⱼ]`
gives, per component `i`, the cleared numerator `Pᵢⱼ = num(rᵢⱼ)·∏_{k≠j} den(rᵢₖ) ∈ CPolyG β` (common
denominator across columns). One **row per `x`-power per component `i ∈ {0,1}`**, one **column per basis
index**; entry `(row, j)` is the `β`-coefficient of that `x`-power in `Pᵢⱼ`. A kernel vector `c` (over `β`)
gives the numerator `N = Σⱼ cⱼ Nⱼ` solving the log-derivative condition. The generic analogue of
`radLogMatrix` (the matrix is over `β`, not `ℚ`). -/
def radLogMatrixG (ρ : QFunNZG β) (integrand : RadElem (QFunNZG β)) (D : CPolyG β)
    (degBound : ℕ) : List (List β) × ℕ :=
  let basis := radLogBasisG (β := β) degBound
  let nCols := basis.length
  let resids : List (RadElem (QFunNZG β)) := basis.map (radLogResidualG ρ integrand D)
  let rowsForComp : ℕ → List (List β) := fun i =>
    let entryOf : ℕ → QFunNZG β := fun j => (resids[j]!).getD i CField.zero
    let nums : List (CPolyG β) := (List.range nCols).map (fun j => cnormG (qNumG (entryOf j)))
    let dens : List (CPolyG β) := (List.range nCols).map (fun j => cnormG (qDenG (entryOf j)))
    let cleared : List (CPolyG β) := (List.range nCols).map (fun j =>
      let prod := (List.range nCols).foldl (fun acc k =>
        if k = j then acc else cmulG acc (dens[k]!)) [(CField.one : β)]
      cnormG (cmulG (nums[j]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun j => (cleared[j]!).getD r CField.zero))
  let allRows := rowsForComp 0 ++ rowsForComp 1
  let nonzero := allRows.filter (fun row => row.any (fun a => !CField.isZero a))
  (nonzero, nCols)

/-- **★ Solve for the log argument over `α = QFunNZG β`** `radLogArgSolveG ρ integrand D degBound = some N`
— the radical-extension numerator `N = a₀ + a₁·y` (`a₀, a₁ ∈ β(x)`, degree `≤ degBound`) with
`∫(integrand) dx = log(N/D)`, **computed** by solving the cleared log-derivative `β`-linear system
`radDeriv(N)·D − N·D' − radMul(N,integrand)·D = 0`. Builds the `β`-matrix `radLogMatrixG`, finds a nonzero
**kernel vector** `c` over `β` (`kernelVectorG`), and reassembles `N = Σⱼ cⱼ Nⱼ` (`a₀ = Σ_k c_k·xᵏ`,
`a₁ = Σ_k c_{degBound+1+k}·xᵏ`). Returns `none` when the kernel is trivial. The `[CField β]`-generic analogue
of `radLogArgSolve` — the **whole linear solve runs over the tower field `β`**, so it computes log
arguments over a transcendental tower (`β = ℚ(x)`, `α = ℚ(x)(eˣ)`), not just over `ℚ`. -/
def radLogArgSolveG (ρ : QFunNZG β) (integrand : RadElem (QFunNZG β)) (D : CPolyG β)
    (degBound : ℕ) : Option (RadElem (QFunNZG β)) :=
  let (rows, nCols) := radLogMatrixG ρ integrand D degBound
  match kernelVectorG nCols rows with
  | none => none
  | some c =>
    let a0 : QFunNZG β := (List.range (degBound + 1)).foldl (fun acc k =>
      CField.add acc (CField.mul (qOfNumG [c.getD k CField.zero]) (qMonomialG k))) CField.zero
    let a1 : QFunNZG β := (List.range (degBound + 1)).foldl (fun acc k =>
      CField.add acc (CField.mul (qOfNumG [c.getD (degBound + 1 + k) CField.zero]) (qMonomialG k)))
      CField.zero
    some [a0, a1]

end

/-! ### Sanity: the ℚ-base classics solve identically under `radLogArgSolveG` (`native_decide`)

At `β = ℚ`, `α = QFunNZG ℚ ≅ ℚ(x)`, the generic solver is the original `radLogArgSolve`. We re-confirm the
arcsinh classic `∫ dx/√(x²+1) = log(x + y)`: `radLogArgSolveG` computes `N` and the computed `u = N/1`
passes the log-derivative certificate — the generalization is conservative (it specializes back to the
ℚ-base case). -/

/-- The radicand `ρ = x²+1 ∈ ℚ(x)` (`y = √(x²+1)`), `[1,0,1]` — the arcsinh case at `β = ℚ`. -/
def genArgRhoArcsinh : QFunNZG ℚ := qxOfNum [1, 0, 1]

/-- The integrand `1/y` of `∫ dx/√(x²+1)`, lifted to `[0, 1/ρ]` over ℚ(x). -/
def genArgIntegrandArcsinh : RadElem (QFunNZG ℚ) := radInvYLift genArgRhoArcsinh CField.one

/-- The field element `x ∈ ℚ(x)`, `[0,1]` — for matching `N = c·(x + y)`. -/
def genArgX : QFunNZG ℚ := qxOfNum [0, 1]

/-- **The COMPUTED arcsinh log argument under the GENERIC solver** — `radLogArgSolveG` at `β = ℚ`,
`ρ = x²+1`, `D = 1`, ansatz degree `1`. Expected (up to a constant) `N = x + y`. -/
def genArgSolvedArcsinh : Option (RadElem (QFunNZG ℚ)) :=
  radLogArgSolveG genArgRhoArcsinh genArgIntegrandArcsinh [1] 1

-- Sanity print: the computed numerator `N` for arcsinh under the generic solver (a multiple of `x + y`).
#eval (genArgSolvedArcsinh.map (fun N => N.map (fun z => ((qNumG z : List ℚ), (qDenG z : List ℚ)))))

/-- **★ `radLogArgSolveG` COMPUTES `u = x + y` for `∫ dx/√(x²+1)` at `β = ℚ`** (`native_decide`): the
generic solver returns `some N` and the COMPUTED `u = N/1` passes the log-derivative certificate
`radIsLogIntegral 2 ρ N integrand = true`. So the ℚ → generic-`CField` generalization is conservative: at
the base level it reproduces `radLogArgSolve` exactly. `N` is the solver's OUTPUT. -/
theorem genArg_arcsinh_compute_verify :
    (genArgSolvedArcsinh.map (fun N =>
      radIsLogIntegral 2 genArgRhoArcsinh N genArgIntegrandArcsinh)) = some true := by
  native_decide

/-- **★ The generic-solved arcsinh `N` is a nonzero constant multiple of `x + y`** (`native_decide`):
`N = [a₀, a₁]` with `a₁ ≠ 0` and `a₀ = a₁·x`, matching the known `u = x + y` (up to the log argument's
scalar freedom) — identical to the ℚ-specific `radLogArgSolve` output. -/
theorem genArg_arcsinh_matches_closed_form :
    (genArgSolvedArcsinh.map (fun N =>
      let a0 := N.getD 0 CField.zero
      let a1 := N.getD 1 CField.zero
      (CField.isZero a1 == false) &&
      CField.isZero (CField.sub a0 (CField.mul a1 genArgX)))) = some true := by
  native_decide

/-! ### ★★ THE HEADLINE: COMPUTE `∫ dx/√(eˣ+1) = log((y−1)/(y+1))` over `α = ℚ(x)(eˣ)` (`native_decide`)

`β = ℚ(x) = QFunNZG ℚ`, `α = QFunNZG β = ℚ(x)(eˣ) = Lvl2`, `θ = eˣ`, `ρ = θ+1`, `y² = ρ`, with the
**exponential** derivation `expTowerDiff` (`t₁' = t₁`, reused from `ComputableRadicalOverTower`). The
integrand `1/√(eˣ+1) = 1/y` lifts to `[0, 1/ρ]`. The log argument is `u = (y−1)/(y+1)`; rationalizing,
`(y−1)/(y+1) = (y−1)²/(ρ−1) = (ρ−2y+1)/(ρ−1)` and `ρ−1 = θ`, so `u = ((θ+2) − 2y)/θ`, i.e. `N = (θ+2) − 2y`
(`a₀ = θ+2`, `a₁ = −2`), `D = θ`.

The **whole linear solve runs over `β = ℚ(x)`** — the matrix entries are `ℚ(x)` elements, row-reduced by
`gaussElimG` over `ℚ(x)`. The solver outputs `N`; the computed `u = N/θ` then passes the log-derivative
certificate at the exponential instance — `∫ dx/√(eˣ+1) = log((y−1)/(y+1))` COMPUTED over the transcendental
tower. -/

/-- The fixed denominator `D = θ = eˣ ∈ ℚ(x)(eˣ)` as a `CPolyG β` (`β = ℚ(x)`): the polynomial `θ = t₁` in
the level-2 fraction-field variable `t₁ = eˣ`, i.e. `[0, 1]` (coefficient of `t₁` is `1 ∈ ℚ(x)`). Lifted to
`α = QFunNZG β` by `qOfNumG`, this is the genuine `θ ∈ ℚ(x)(eˣ)`. The denominator of `u = (y−1)/(y+1) =
((θ+2)−2y)/θ`. -/
def expDenTheta : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- The radicand `ρ = θ+1 = eˣ+1 ∈ ℚ(x)(eˣ) = α` for the generic solve — the same carrier value as
`expRadicand` (`ComputableRadicalOverTower`). -/
def expArgRho : Lvl2 := expRadicand

/-- The integrand `1/√(eˣ+1) = 1/y` lifted to `[0, 1/ρ]` over `α = ℚ(x)(eˣ)` (`ρ = eˣ+1`), the `R/y` form
for the log-derivative system. -/
def expArgIntegrand : RadElem Lvl2 := radInvYLift expArgRho CField.one

/-- **★★ The COMPUTED log argument for `∫ dx/√(eˣ+1)` OVER THE TOWER** — `radLogArgSolveG` at
`β = ℚ(x)`, `α = ℚ(x)(eˣ)`, with the **exponential** derivation `expTowerDiff` supplied via `@`,
`ρ = eˣ+1`, `D = θ`, ansatz degree `1` in `θ = t₁` (`a₀ = θ+2` is degree-1 in `t₁`, `a₁ = −2` is a
constant; their `x`-level coefficients `2, 1, −2` are constants of `β = ℚ(x)`). The kernel vector is found
by `gaussElimG` over `ℚ(x)`. Expected (up to a constant) `N = (θ+2) − 2y`, so `u = N/θ = (y−1)/(y+1)`. -/
def expArgSolved : Option (RadElem Lvl2) :=
  @radLogArgSolveG _ _ _ expTowerDiff expArgRho expArgIntegrand expDenTheta 1

-- Sanity print: the computed numerator `N` for `∫ dx/√(eˣ+1)` over the tower (a multiple of `(θ+2) − 2y`).
#eval (expArgSolved.map (fun N => N.map (fun z =>
  ((qNumG (β := QFunNZG ℚ) z).map (fun w => (w.1.1 : List ℚ)),
   (qDenG (β := QFunNZG ℚ) z).map (fun w => (w.1.1 : List ℚ))))))

/-- **★★ `radLogArgSolveG` COMPUTES the log argument for `∫ dx/√(eˣ+1)` OVER ℚ(x)(eˣ)** (`native_decide`):
the generic solver — its **entire Gaussian elimination running over `β = ℚ(x)`** — returns `some N` for the
transcendental-tower base `α = ℚ(x)(eˣ)`. THE ENGINE COMPUTES A LOG ARGUMENT OVER A TRANSCENDENTAL TOWER:
the linear solve `radLogArgSolveG` is no longer pinned to ℚ; its matrix entries are `ℚ(x)` elements,
row-reduced by `gaussElimG` over `ℚ(x)`, and it produces a nonzero kernel vector `N`. -/
theorem expArg_solves :
    (expArgSolved.map (fun _ => true)) = some true := by native_decide

/-- **★★ THE GRAND UNIFICATION (LOG PART): the COMPUTED `u = N/θ` integrates `∫ dx/√(eˣ+1)` over
ℚ(x)(eˣ)** (`native_decide`) — the log argument `N` **computed** by `radLogArgSolveG` (a kernel vector of
the cleared linear system, solved over `β = ℚ(x)`) yields `u = N/θ` that passes the log-derivative
certificate `radIsLogIntegral 2 ρ (N/θ) integrand = true` at the **exponential** instance `expTowerDiff`.
Since `u = ((θ+2)−2y)/θ = (y−1)/(y+1)` and `d/dx log u = y'·2/(ρ−1) = (θ/(2y))·2/θ = 1/y = 1/√(eˣ+1)`, this
is `∫ dx/√(eˣ+1) = log((y−1)/(y+1))` **COMPUTED over the transcendental tower** — the grand unification
extended from the rational part to the LOG part, the log argument now an OUTPUT of the engine over
`α = ℚ(x)(eˣ)`, not a supplied closed form. Checked by dividing the computed `N` by the fixed `D = θ` and
running the certificate. -/
theorem expArg_compute_verify :
    (expArgSolved.map (fun N =>
      @radIsLogIntegral _ _ expTowerDiff 2 expArgRho
        [CField.div (N.getD 0 CField.zero) expTheta,
         CField.div (N.getD 1 CField.zero) expTheta]
        expArgIntegrand)) = some true := by native_decide

/-- **★ The computed tower `N` is a nonzero constant multiple of `(θ+2) − 2y`** (`native_decide`): the
solver's `N = [a₀, a₁]` over `α = ℚ(x)(eˣ)` satisfies `a₁ ≠ 0` and `a₀·(−2) = a₁·(θ+2)` — i.e.
`N = c·((θ+2) − 2y)` for one nonzero `c ∈ ℚ(x)(eˣ)` — matching the rationalized closed form `u =
(y−1)/(y+1)` exactly (up to the log argument's scalar freedom). Confirms the kernel vector is the *expected*
one, computed over the tower. -/
theorem expArg_matches_closed_form :
    (expArgSolved.map (fun N =>
      let a0 := N.getD 0 CField.zero
      let a1 := N.getD 1 CField.zero
      (CField.isZero a1 == false) &&
      CField.isZero (CField.sub (CField.mul a0 (CField.neg (CField.add CField.one CField.one)))
        (CField.mul a1 (CField.add expTheta (CField.add CField.one CField.one)))))) = some true := by
  native_decide

/-! ### `#print axioms` — does the engine COMPUTE log arguments over a TRANSCENDENTAL TOWER?

Each compute-then-verify theorem carries the standard `[propext, Classical.choice, Quot.sound]` plus the
`native_decide` compiler axiom — no `sorry`, no extra axiom. **The engine now COMPUTES the log argument `u`
over a transcendental tower.** The generic Gaussian elimination `gaussElimG`/`kernelVectorG` and the generic
solve `radLogArgSolveG` run over any `[CField β]`: at `β = ℚ` they reproduce the ℚ-base `radLogArgSolve`
(arcsinh `u = x + y`, conservative), and at `β = ℚ(x)` they COMPUTE the log argument `N = (θ+2) − 2y` for
`∫ dx/√(eˣ+1)` over `α = ℚ(x)(eˣ)` — with the **whole linear solve over `ℚ(x)`** — whose computed `u = N/θ =
(y−1)/(y+1)` passes the log-derivative certificate. The grand unification is extended from the rational part
to the LOG part. The general degree bounds + the non-principal/torsion case remain deferred. -/

-- ℚ-base sanity (conservative): the generic solver reproduces `radLogArgSolve` at `β = ℚ`:
#print axioms genArg_arcsinh_compute_verify
#print axioms genArg_arcsinh_matches_closed_form

-- ★★ The headline: log argument COMPUTED over the transcendental tower `α = ℚ(x)(eˣ)`:
#print axioms expArg_solves
#print axioms expArg_compute_verify
#print axioms expArg_matches_closed_form

end DeepWiki.SymbolicIntegration
