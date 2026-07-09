import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgFunctionField
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGeneric
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # The Ford–Zassenhaus Round-2 step: p-trace-radical + idealizer

Starting from the equation order `O = [1, y, …, yⁿ⁻¹]` of `K(x, y) = K(x)[y]/(f)`, one enlargement
toward the maximal (integral-basis) order: the bad primes `p` with `p² ∣ disc f` (`badPrimes`), the
p-trace-radical `I_p` (`pTraceRadical`, the residue-field trace-matrix kernel), and the idealizer
`Î = (I_p : I_p)` (`round2Step`). On the cusp `y² − x³` it enlarges `[1, y] → [1, y/x]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPoly

variable {α : Type*} [CField α]

/-! ### Residue-field reduction at a linear prime `p = x − a`

For a linear prime `p = x − a`, the residue field `K[x]/(p) = K` and reduction mod `p` is evaluation at
the root `a` (`qEvalAtRoot`). -/

/-- Evaluate a `ℚ(x)` element at a root `a`: `qEvalAtRoot z a = num(a)/den(a) ∈ ℚ`, Horner-evaluating the
numerator and denominator of `z : CFrac ℚ` and dividing. The reduction `z mod (x − a)`. -/
def qEvalAtRoot (z : CFrac ℚ) (a : ℚ) : ℚ :=
  CField.div (ceval (z.1.1 : CPoly ℚ) a) (ceval (z.1.2 : CPoly ℚ) a)

/-! ### A full kernel basis of a `β`-matrix (`kernelBasis`) -/

/-- A basis of the kernel of a `β`-matrix `kernelBasis nCols rows`: one vector per free (non-pivot) column
of the `gaussElim` reduction — for free column `fc`, a `1` at `fc` with each pivot variable set to the
negated pivot-row entry — the reduced-row-echelon nullspace basis. Fuel-free. -/
def kernelBasis {β : Type*} [CField β] (nCols : ℕ) (rows : List (List β)) :
    List (List β) :=
  let (rs, pivots) := gaussElim nCols rows
  let freeCols := (List.range nCols).filter (fun c => ¬ pivots.contains c)
  freeCols.map (fun fc =>
    let base : List β := (List.range nCols).map (fun c =>
      if c = fc then (CField.one : β) else CField.zero)
    (List.range pivots.length).foldl (fun (acc : List β) r =>
      let pc := pivots[r]!
      let v := CField.neg ((rs[r]!).getD fc CField.zero)
      acc.set pc v) base)

end CPoly

/-! ### Bad primes: squarefree factors of the discriminant with `p² ∣ d` (`badPrimes`) -/

open CPoly

/-- The numerator of the discriminant as a `ℚ[x]` polynomial `discNum f = (discriminant f).1.1` (the
denominator is `1` for a monic `f`), whose squarefree part bounds the bad primes. -/
def discNum (f : CPoly (CFrac ℚ)) : CPoly ℚ := (discriminant f).1.1

/-- The bad primes of `f` `badPrimes f`: the distinct monic squarefree factors of the discriminant
numerator (Yun factorization) with `p² ∣ d` (tested by `cisZero (cmodWf d (p·p))`) — the primes where the
equation order may be non-maximal. -/
def badPrimes (f : CPoly (CFrac ℚ)) : List (CPoly ℚ) :=
  let d := discNum f
  let sqf := cSqfreeYunFF d
  -- distinct nonconstant squarefree factors, each made monic
  let distinct := (sqf.map cmonic).filter (fun p => 0 < cdeg p)
  distinct.filter (fun p => cisZero (cmodWf d (cmul p p)))

/-! ### The cusp `f = y² − x³` over `ℚ(x)`

`n = 2`, discriminant `4x³`, bad prime `x`; the order `[1, y]` is non-maximal since `y/x` is integral
(`(y/x)² = x`). -/

/-- The cusp curve `f = y² − x³ ∈ ℚ(x)[y]` (`a₀ = −x³`, monic), `CPoly (CFrac ℚ)` `[−x³, 0, 1]`. The
equation order `[1, y]` is non-maximal at `x`. -/
def cuspF : CPoly (CFrac ℚ) :=
  [qxOfNum [0, 0, 0, -1], CField.zero, CField.one]

/-- The generator `y` of `ℚ(x)[y]/(y² − x³)` (`afBasisElem 1 = [0, 1]`). -/
def cuspY : CPoly (CFrac ℚ) := afBasisElem 1

/-- The bad prime of the cusp is `x`: `badPrimes cuspF = [x]` (the single monic factor `x = [0, 1]` with
`x² ∣ 4x³`). -/
theorem cusp_badPrimes_eq :
    (badPrimes cuspF).map cmonic = [([0, 1] : CPoly ℚ)] := by native_decide

/-! ### The p-trace-radical `I_p` at a linear prime (`pTraceRadical`)

For a linear bad prime `p = x − a`, `I_p = { z ∈ O : p ∣ Tr(z·ωⱼ) ∀j }` is the kernel of the trace
matrix reduced mod `p` (evaluated at `a`), lifted and Hermite-reduced to a `K[x]`-basis. -/

namespace CPoly

/-- The power-basis coordinate row of an order element `afCoordRow n z = [num(c₀), …, num(c_{n−1})]`: the
first `n` coefficients of `z : CPoly (CFrac ℚ)` read as `ℚ[x]` numerators. -/
def afCoordRow (n : ℕ) (z : CPoly (CFrac ℚ)) : List (CPoly ℚ) :=
  (List.range n).map (fun i => ((z.getD i CField.zero : CFrac ℚ).1.1 : CPoly ℚ))

/-- The trace matrix reduced at a linear prime root `a` `traceMatrixAtRoot f a`: the `n×n` `ℚ`-matrix
`traceMatrix f (powerBasis f)` with every entry evaluated at `x = a` (`qEvalAtRoot`), i.e. `T mod (x − a)`.
Its kernel is the p-trace-radical mod `p`. -/
def traceMatrixAtRoot (f : CPoly (CFrac ℚ)) (a : ℚ) : List (List ℚ) :=
  (traceMatrix f (powerBasis f)).map (fun row => row.map (fun e => qEvalAtRoot e a))

/-- The p-trace-radical `I_p` at a linear prime `p = x − a` `pTraceRadical f p a`: a `K[x]`-basis of
`I_p = { z ∈ O : p ∣ Tr(z·ωⱼ) ∀j }` as a `PolyMatrix ℚ` (rows = basis vectors in power-basis coordinates).
The kernel of `traceMatrixAtRoot f a` (`kernelBasis`) lifts to constant coordinate rows which, with the
`p·ωᵢ` rows, generate `I_p ⊇ p·O`; `hermiteRowReduce` triangularizes to the basis. -/
def pTraceRadical (f : CPoly (CFrac ℚ)) (p : CPoly ℚ) (a : ℚ) : PolyMatrix ℚ :=
  let n := cdeg f
  let kers : List (List ℚ) := kernelBasis n (traceMatrixAtRoot f a)
  -- lift each kernel vector to a constant `ℚ[x]` coordinate row (the residue generators)
  let kerRows : PolyMatrix ℚ := kers.map (fun v => (List.range n).map (fun i => [v.getD i 0]))
  -- the `p·ωᵢ` rows: `p` in column `i`, zero elsewhere
  let pRows : PolyMatrix ℚ := (List.range n).map (fun i =>
    (List.range n).map (fun j => if i = j then p else ([] : CPoly ℚ)))
  let gens : PolyMatrix ℚ := kerRows ++ pRows
  let reduced := hermiteRowReduce gens
  reduced.filter (fun row => !row.all cisZero)

end CPoly

/-! ### The cusp p-trace-radical `I_x = ⟨x, y⟩`

For `f = y² − x³`, `p = x`: the trace matrix `[[2, 0], [0, 2x³]]` at `x = 0` is `[[2, 0], [0, 0]]`, kernel
`{(0, 1)} = y`; Hermite-reduces to the `K[x]`-basis `[x, y]`, strictly containing `x·O`. -/

open CPoly

/-- The cusp trace matrix mod `x` is `[[2, 0], [0, 0]]`: `traceMatrix (y² − x³) = [[2, 0], [0, 2x³]]`
evaluated at `x = 0`, a rank-`1` matrix with kernel `{(0, 1)} = y`. -/
theorem cusp_traceMatrixAtRoot_eq :
    traceMatrixAtRoot cuspF 0 = [[2, 0], [0, 0]] := by native_decide

/-- The cusp p-trace-radical kernel is `(0, 1) = y`: the kernel basis of the reduced trace matrix mod `x`
is the single vector `(0, 1)`, the order element `y`. -/
theorem cusp_pTraceRadical_kernel_eq :
    kernelBasis (cdeg cuspF) (traceMatrixAtRoot cuspF 0) = [[0, 1]] := by native_decide

/-- The cusp p-trace-radical has `K[x]`-basis `[x, y]`: `pTraceRadical (y² − x³) x` Hermite-reduces
`{y, x·1, x·y}` to the rows `[x, 0]` and `[0, 1]`, i.e. `I_x = ⟨x, y⟩`, strictly larger than `x·O`. -/
theorem cusp_pTraceRadical_basis :
    (pTraceRadical cuspF [0, 1] 0).map (fun row => row.map cmonic) =
      [[[0, 1], []], [[], [1]]] := by native_decide

/-! ### The idealizer `Î = (I_p : I_p)` — one Round-2 enlargement (`round2Step`)

The enlarged order `Î = (I_p : I_p) = { z ∈ K(x, y) : z·I_p ⊆ I_p }`. With the `I_p`-basis as columns of
`B`, the condition `z·I_p ⊆ I_p` reduces to a Hermite-mod-`δ` solve over `K[x]`; the columns of the reduced
`M̂⁻¹` are the idealizer basis, carrying the enlarging denominators. -/

namespace CPoly

/-! #### Field matrix algebra over `K(x) = CFrac ℚ` (inverse, product) -/

/-- Matrix product over a `[CField β]` `matMul A Bm`: the `(i, j)` entry is `Σₖ A[i][k]·Bm[k][j]`. -/
def matMul {β : Type*} [CField β] (A Bm : List (List β)) : List (List β) :=
  let r := (Bm.headD []).length
  A.map (fun rowA =>
    (List.range r).map (fun j =>
      ((List.range rowA.length).foldl (fun acc k =>
        CField.add acc (CField.mul (rowA.getD k CField.zero) ((Bm.getD k []).getD j CField.zero)))
        CField.zero)))

/-- Inverse of a square `n×n` matrix over a `[CField β]` `matInv n M = some M⁻¹` (or `none` if singular):
Gauss–Jordan on the augmented `[M | Iₙ]`, reading the right half. Fuel-free. -/
def matInv {β : Type*} [CField β] (n : ℕ) (M : List (List β)) : Option (List (List β)) :=
  -- augment each row with the identity
  let aug : List (List β) := (List.range n).map (fun i =>
    (M.getD i []) ++ (List.range n).map (fun j => if i = j then (CField.one : β) else CField.zero))
  -- Gauss–Jordan over the 2n columns, pivoting on columns 0 … n−1
  let step : Option (List (List β)) → ℕ → Option (List (List β)) :=
    fun st col =>
      match st with
      | none => none
      | some rs =>
        match (List.range n).find?
            (fun i => i ≥ col && (!CField.isZero ((rs.getD i []).getD col CField.zero))) with
        | none => none
        | some i =>
          let rowCol := rs.getD col []
          let rowI := rs.getD i []
          let rs := (rs.set col rowI).set i rowCol
          let pivRow := rs.getD col []
          let lead := pivRow.getD col CField.zero
          let pivRow := pivRow.map (fun a => CField.div a lead)
          let rs := rs.set col pivRow
          let rs := (List.range n).foldl (fun acc rr =>
            if rr = col then acc
            else
              let row := acc.getD rr []
              let factor := row.getD col CField.zero
              if CField.isZero factor then acc
              else
                let newRow := (List.range (2 * n)).map (fun c =>
                  CField.sub (row.getD c CField.zero) (CField.mul factor (pivRow.getD c CField.zero)))
                acc.set rr newRow) rs
          some rs
  match (List.range n).foldl step (some aug) with
  | none => none
  | some rs => some (rs.map (fun row => (List.range n).map (fun j => row.getD (n + j) CField.zero)))

/-! #### `K(x) ↔ K[x]` denominator clearing and lifts -/

/-- Lift a `K[x]` coordinate row to a `K(x, y)` element `rowToAf row = Σᵢ qxOfNum(rowᵢ)·yⁱ`, turning an
`I_p`-basis row into the order element it represents. -/
def rowToAf (row : List (CPoly ℚ)) : CPoly (CFrac ℚ) := row.map qxOfNum

/-- The `I_p`-basis matrix `B` over `K(x)` `ipBasisMatrix n ipRows`: the `n×n` `CFrac ℚ`-matrix whose
column `k` is the `k`-th `I_p`-basis row, `B[r][k] = qxOfNum (ipRows[k][r])` — the change of basis from the
`I_p` basis to the power basis. -/
def ipBasisMatrix (n : ℕ) (ipRows : PolyMatrix ℚ) : List (List (CFrac ℚ)) :=
  (List.range n).map (fun r =>
    (List.range n).map (fun k => qxOfNum ((ipRows.getD k []).getD r [])))

/-- The common denominator of a `K(x)`-matrix `commonDenomQ M`: the product over all entries of their
normalized denominators (`z.1.2`), a coarse common multiple used to clear `M` to `K[x]`. -/
def commonDenomQ (M : List (List (CFrac ℚ))) : CPoly ℚ :=
  M.foldl (fun acc row =>
    row.foldl (fun a z =>
      let den := cnorm (z.1.2 : CPoly ℚ)
      if cisZero den || cisZero (csub den [CField.one]) then a else cmul a den)
      acc) [CField.one]

/-- Clear a `K(x)`-row to a `K[x]`-row at denominator `δ` `clearRow δ row = [num(δ·zᵢ)]`: multiply each
entry by `δ` and take the numerator; the integral row `δ·row` when `δ` is a common denominator. -/
def clearRow (δ : CPoly ℚ) (row : List (CFrac ℚ)) : List (CPoly ℚ) :=
  row.map (fun z => (CField.mul (qxOfNum δ) z).1.1)

/-! #### The idealizer of `I_p`, given an order basis (`idealizerBasis`) -/

/-- The idealizer `Î = (I_p : I_p)` as a new `K(x)` order basis `idealizerBasis f orderBasis ipRows`, given
the current order basis and the `I_p` `K[x]`-basis (`pTraceRadical` output). Forms `B = ipBasisMatrix`,
`Mⱼ = B⁻¹ · multMatrix f ιⱼ` for each `ιⱼ`, stacks into `M`, clears to `N = δ·M` over `K[x]`, Hermite-reduces,
inverts the first `n` rows, and scales by `δ`: the columns of `δ·N̂⁻¹` are the idealizer basis. Returns
`orderBasis` unchanged if any inverse is singular. -/
def idealizerBasis (f : CPoly (CFrac ℚ)) (orderBasis : List (CPoly (CFrac ℚ)))
    (ipRows : PolyMatrix ℚ) : List (CPoly (CFrac ℚ)) :=
  let n := cdeg f
  let B : List (List (CFrac ℚ)) := ipBasisMatrix n ipRows
  match matInv n B with
  | none => orderBasis
  | some Binv =>
    -- stack the `Mⱼ = Binv · multMatrix f ιⱼ` (each `n×n` over K(x))
    let M : List (List (CFrac ℚ)) :=
      (List.range n).foldr (fun j acc =>
        let ιj : CPoly (CFrac ℚ) := rowToAf ((ipRows.getD j []))
        let Mj := matMul Binv (multMatrix f ιj)
        Mj ++ acc) []
    -- clear to K[x] by a common denominator δ
    let δ : CPoly ℚ := commonDenomQ M
    let N : PolyMatrix ℚ := M.map (clearRow δ)
    -- Hermite-reduce N over K[x]; the first n rows are the upper-triangular invertible part
    let reduced := hermiteRowReduce N
    let Nhat : List (List (CFrac ℚ)) :=
      (List.range n).map (fun i => (List.range n).map (fun j => qxOfNum ((reduced.getD i []).getD j [])))
    match matInv n Nhat with
    | none => orderBasis
    | some NhatInv =>
      -- columns of δ·N̂⁻¹ are the new basis vectors (in the [1,y,…] order/power basis)
      let δq : CFrac ℚ := qxOfNum δ
      (List.range n).map (fun col =>
        (List.range n).map (fun row => CField.mul δq ((NhatInv.getD row []).getD col CField.zero)))

end CPoly

/-! #### `round2Step`: one enlargement of the equation order at all bad primes -/

namespace CPoly

/-- `true` iff a `K(x, y)` order basis equals the power basis `[1, y, …, yⁿ⁻¹]` `isPowerBasis n basis`:
each `basisᵢ` is `cisZero`-equal to `yⁱ`. Tests whether `round2Step` grew the order. -/
def isPowerBasis (n : ℕ) (basis : List (CPoly (CFrac ℚ))) : Bool :=
  (List.range n).all (fun i =>
    cisZero (csub (basis.getD i []) (afBasisElem i)))

/-- One Ford–Zassenhaus Round-2 enlargement `round2Step f = (newBasis, grew)`. From the equation order
`O = powerBasis f`, for the first bad prime `p = x − a`, computes the p-trace-radical `I_p` and the idealizer
`Î = (I_p : I_p)`, returning `Î`'s basis and whether it strictly enlarged `O`. With no bad prime, returns the
power basis with `grew = false`. -/
def round2Step (f : CPoly (CFrac ℚ)) :
    List (CPoly (CFrac ℚ)) × Bool :=
  let n := cdeg f
  let O := powerBasis f
  match (badPrimes f) with
  | [] => (O, false)
  | p :: _ =>
    let pm := cmonic p
    -- root of a monic linear prime `p = [−a, 1]` is `a = −p₀`
    let a : ℚ := CField.neg (pm.getD 0 CField.zero)
    let ip := pTraceRadical f pm a
    let newBasis := idealizerBasis f O ip
    (newBasis, !isPowerBasis n newBasis)

end CPoly

/-! ### `round2Step` enlarges `[1, y] → [1, y/x]` for `y² = x³`

For the cusp `f = y² − x³`, bad prime `p = x`, `I_x = ⟨x, y⟩`, and the idealizer gives the new basis
`[1, y/x]` (integral: `(y/x)² = x`); a second step does not grow it, so `[1, y/x]` is the maximal order. -/

open CPoly

/-- The enlarged generator `y/x ∈ ℚ(x)[y]/(y² − x³)`, the second basis vector of `round2Step`
(`[0, 1/x]` in the `[1, y]` order basis). -/
def cuspNewGen : CPoly (CFrac ℚ) := (round2Step cuspF).1.getD 1 []

/-- `round2Step` enlarges the cusp order: `(round2Step cuspF).2 = true`, the idealizer strictly contains
`[1, y]`. -/
theorem cusp_round2_grew :
    (round2Step cuspF).2 = true := by native_decide

/-- The enlarged generator is `y/x`: `round2Step cuspF` produces `[1, y/x]` (second vector `[0, 1/x]`, first
`[1]`), checked by `cisZero (cuspNewGen − [0, 1/x])`. -/
theorem cusp_round2_newGen_eq :
    (cisZero (csub cuspNewGen [CField.zero, qxOfFrac [1] [0, 1] (by decide)])
      && cisZero (csub ((round2Step cuspF).1.getD 0 []) [CField.one])) = true := by native_decide

/-- The enlarged generator `y/x` is integral: `afMul f (y/x) (y/x) = x` in `ℚ(x)[y]/(y² − x³)`, checked by
`cisZero (afMul f (y/x) (y/x) − x)`. -/
theorem cusp_newGen_integral :
    cisZero (csub (afMul cuspF cuspNewGen cuspNewGen) [qxOfNum [0, 1]]) = true := by native_decide

/-- `[1, y/x]` is the maximal order — a second `round2Step` does not grow it: the idealizer against the
enlarged basis `[1, y/x]` returns `[1, y/x]` again, a fixed point. -/
theorem cusp_secondStep_stable :
    let O2 := (round2Step cuspF).1
    let ip2 := pTraceRadical cuspF [0, 1] 0
    let O3 := idealizerBasis cuspF O2 ip2
    (List.range 2).all (fun i =>
      cisZero (csub (O3.getD i []) (O2.getD i []))) = true := by native_decide

/-! ### A second curve: the node `f = y² − x²(x + 1)` enlarges `[1, y] → [1, y/x]`

The node `f = y² − x³ − x²`: discriminant `4x²(x + 1)`, bad prime `x`; `round2Step` enlarges to
`[1, y/x]` with the relation `(y/x)² = x + 1`, so `[1, y/x]` is its maximal order too. -/

/-- The node curve `f = y² − x²(x + 1) = y² − x³ − x² ∈ ℚ(x)[y]` (`a₀ = −(x³ + x²)`, monic), `CPoly
(CFrac ℚ)` `[−(x³ + x²), 0, 1]`. An ordinary double point; `[1, y]` is non-maximal at `x`. -/
def nodeF : CPoly (CFrac ℚ) :=
  [qxOfNum [0, 0, -1, -1], CField.zero, CField.one]

/-- The enlarged generator `y/x ∈ ℚ(x)[y]/(y² − x²(x+1))`, the second basis vector of `round2Step nodeF`
(`[0, 1/x]`). -/
def nodeNewGen : CPoly (CFrac ℚ) := (round2Step nodeF).1.getD 1 []

/-- The node bad prime is `x`, and `round2Step` enlarges to `[1, y/x]`: `badPrimes nodeF = [x]`, `.2 = true`,
new generator `[0, 1/x] = y/x`, first vector `1`. -/
theorem node_round2_newGen_eq :
    ((badPrimes nodeF).map cmonic = [([0, 1] : CPoly ℚ)]
      && (round2Step nodeF).2
      && cisZero (csub nodeNewGen [CField.zero, qxOfFrac [1] [0, 1] (by decide)])
      && cisZero (csub ((round2Step nodeF).1.getD 0 []) [CField.one])) = true := by
  native_decide

/-- The node's enlarged generator is integral with relation `(y/x)² = x + 1`: `afMul f (y/x) (y/x) = x + 1`
in `ℚ(x)[y]/(y² − x²(x+1))`, checked by `cisZero (afMul f (y/x) (y/x) − (x + 1))`. -/
theorem node_newGen_integral :
    cisZero (csub (afMul nodeF nodeNewGen nodeNewGen) [qxOfNum [1, 1]]) = true := by native_decide

/-- `[1, y/x]` is the maximal order of the node — a second `round2Step` does not grow it: the idealizer
against `[1, y/x]` returns `[1, y/x]` again. -/
theorem node_secondStep_stable :
    let O2 := (round2Step nodeF).1
    let ip2 := pTraceRadical nodeF [0, 1] 0
    let O3 := idealizerBasis nodeF O2 ip2
    (List.range 2).all (fun i =>
      cisZero (csub (O3.getD i []) (O2.getD i []))) = true := by native_decide

/-! ### Scope of `round2Step`

`round2Step` is one enlargement at the first linear bad prime. The full integral-basis algorithm
iterates it to a fixed point: over all bad primes simultaneously, re-basing the trace matrix after each
enlargement, and using residue-field linear algebra over `K[x]/(p)` for higher-degree bad primes. -/

end DeepWiki.SymbolicIntegration
