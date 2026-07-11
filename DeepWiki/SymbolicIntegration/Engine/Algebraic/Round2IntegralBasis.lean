import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgFunctionField
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGeneric
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.ComputableAlgebra.FracLinearAlgebra
import DeepWiki.ComputableAlgebra.LinearAlgebraRat

/-! # The Ford–Zassenhaus Round-2 step: p-trace-radical + idealizer

Starting from the equation order `O = [1, y, …, yⁿ⁻¹]` of `K(x, y) = K(x)[y]/(f)`, one enlargement
toward the maximal (integral-basis) order: the bad primes `p` with `p² ∣ disc f` (`badPrimes`), the
p-trace-radical `I_p` (`pTraceRadical`, the residue-field trace-matrix kernel), and the idealizer
`Î = (I_p : I_p)` (`round2Step`). On the cusp `y² − x³` it enlarges `[1, y] → [1, y/x]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

/-! ### Residue-field reduction at a linear prime `p = x − a`

For a linear prime `p = x − a`, the residue field `K[x]/(p) = K` and reduction mod `p` is
`CFrac.eval` at the root `a`. -/

/-! ### Bad primes: squarefree factors of the discriminant with `p² ∣ d` (`badPrimes`) -/

open DensePoly

/-- The numerator of the discriminant as a `ℚ[x]` polynomial `discNum f = (discriminant f).num` (the
denominator is `1` for a monic `f`), whose squarefree part bounds the bad primes. -/
def discNum (f : DensePoly (DenseFrac ℚ)) : DensePoly ℚ :=
  CFrac.num (CFrac.discriminant f)

/-- The bad primes of `f` `badPrimes f`: the distinct monic squarefree factors of the discriminant
numerator (Yun factorization) with `p² ∣ d` (tested by the selected remainder) — the primes where the
equation order may be non-maximal. -/
def badPrimes (f : DensePoly (DenseFrac ℚ)) : List (DensePoly ℚ) :=
  let d := discNum f
  let sqf := CPoly.squarefreeYun d
  -- distinct nonconstant squarefree factors, each made monic
  let distinct := (sqf.map cmonic).filter (fun p => 0 < cdeg p)
  distinct.filter (fun p => cisZero (CPolyEuclidean.mod d (cmul p p)))

/-! ### The cusp `f = y² − x³` over `ℚ(x)`

`n = 2`, discriminant `4x³`, bad prime `x`; the order `[1, y]` is non-maximal since `y/x` is integral
(`(y/x)² = x`). -/

/-- The cusp curve `f = y² − x³ ∈ ℚ(x)[y]` (`a₀ = −x³`, monic), `DensePoly (DenseFrac ℚ)` `[−x³, 0, 1]`. The
equation order `[1, y]` is non-maximal at `x`. -/
def cuspF : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [0, 0, 0, -1], CCommRing.zero, CCommRing.one]

/-- The generator `y` of `ℚ(x)[y]/(y² − x³)` (`CPoly.afBasisElem 1 = [0, 1]`). -/
def cuspY : DensePoly (DenseFrac ℚ) := CPoly.afBasisElem 1

/-- The bad prime of the cusp is `x`: `badPrimes cuspF = [x]` (the single monic factor `x = [0, 1]` with
`x² ∣ 4x³`). -/
theorem cusp_badPrimes_eq :
    (badPrimes cuspF).map cmonic = [([0, 1] : DensePoly ℚ)] := by native_decide

/-! ### The p-trace-radical `I_p` at a linear prime (`pTraceRadical`)

For a linear bad prime `p = x − a`, `I_p = { z ∈ O : p ∣ Tr(z·ωⱼ) ∀j }` is the kernel of the trace
matrix reduced mod `p` (evaluated at `a`), lifted and Hermite-reduced to a `K[x]`-basis. -/

namespace DensePoly

/-- The trace matrix reduced at a linear prime root `a` `traceMatrixAtRoot f a`: the `n×n` `ℚ`-matrix
`CPoly.traceMatrix f (CPoly.powerBasis f)` with every entry evaluated at `x = a` (`CFrac.eval`), i.e. `T mod (x − a)`.
Its kernel is the p-trace-radical mod `p`. -/
def traceMatrixAtRoot (f : DensePoly (DenseFrac ℚ)) (a : ℚ) : List (List ℚ) :=
  (CPoly.traceMatrix f (CPoly.powerBasis f)).map (fun row => row.map (fun e => CFrac.eval e a))

/-- The p-trace-radical `I_p` at a linear prime `p = x − a` `pTraceRadical f p a`: a `K[x]`-basis of
`I_p = { z ∈ O : p ∣ Tr(z·ωⱼ) ∀j }` as a `PolyMatrix DensePoly ℚ` (rows = basis vectors in power coordinates).
The selected kernel of `traceMatrixAtRoot f a` (`CLinearSolve.nullspaceBasis`) lifts to constant coordinate rows which, with the
`p·ωᵢ` rows, generate `I_p ⊇ p·O`; `hermiteRowReduce` triangularizes to the basis. -/
def pTraceRadical [CLinearSolve ℚ]
    (f : DensePoly (DenseFrac ℚ)) (p : DensePoly ℚ) (a : ℚ) :
    PolyMatrix DensePoly ℚ :=
  let n := cdeg f
  let kers : List (List ℚ) := CLinearSolve.nullspaceBasis (traceMatrixAtRoot f a) n
  -- lift each kernel vector to a constant `ℚ[x]` coordinate row (the residue generators)
  let kerRows : PolyMatrix DensePoly ℚ := kers.map (fun v => (List.range n).map (fun i => [v.getD i 0]))
  -- the `p·ωᵢ` rows: `p` in column `i`, zero elsewhere
  let pRows : PolyMatrix DensePoly ℚ := (List.range n).map (fun i =>
    (List.range n).map (fun j => if i = j then p else ([] : DensePoly ℚ)))
  let gens : PolyMatrix DensePoly ℚ := kerRows ++ pRows
  let reduced := CPoly.hermiteRowReduce gens
  reduced.filter (fun row => !row.all cisZero)

end DensePoly

/-! ### The cusp p-trace-radical `I_x = ⟨x, y⟩`

For `f = y² − x³`, `p = x`: the trace matrix `[[2, 0], [0, 2x³]]` at `x = 0` is `[[2, 0], [0, 0]]`, kernel
`{(0, 1)} = y`; Hermite-reduces to the `K[x]`-basis `[x, y]`, strictly containing `x·O`. -/

open DensePoly

/-- The cusp trace matrix mod `x` is `[[2, 0], [0, 0]]`: `CPoly.traceMatrix (y² − x³) = [[2, 0], [0, 2x³]]`
evaluated at `x = 0`, a rank-`1` matrix with kernel `{(0, 1)} = y`. -/
theorem cusp_traceMatrixAtRoot_eq :
    traceMatrixAtRoot cuspF 0 = [[2, 0], [0, 0]] := by native_decide

/-- The cusp p-trace-radical kernel is `(0, 1) = y`: the kernel basis of the reduced trace matrix mod `x`
is the single vector `(0, 1)`, the order element `y`. -/
theorem cusp_pTraceRadical_kernel_eq :
    CLinearSolve.nullspaceBasis (traceMatrixAtRoot cuspF 0) (cdeg cuspF) = [[0, 1]] := by
  native_decide

/-- The cusp p-trace-radical has `K[x]`-basis `[x, y]`: `pTraceRadical (y² − x³) x` Hermite-reduces
`{y, x·1, x·y}` to the rows `[x, 0]` and `[0, 1]`, i.e. `I_x = ⟨x, y⟩`, strictly larger than `x·O`. -/
theorem cusp_pTraceRadical_basis :
    (pTraceRadical cuspF [0, 1] 0).map (fun row => row.map cmonic) =
      [[[0, 1], []], [[], [1]]] := by native_decide

/-! ### The idealizer `Î = (I_p : I_p)` — one Round-2 enlargement (`round2Step`)

The enlarged order `Î = (I_p : I_p) = { z ∈ K(x, y) : z·I_p ⊆ I_p }`. With the `I_p`-basis as columns of
`B`, the condition `z·I_p ⊆ I_p` reduces to a Hermite-mod-`δ` solve over `K[x]`; the columns of the reduced
`M̂⁻¹` are the idealizer basis, carrying the enlarging denominators. -/

namespace DensePoly

/-! #### Field matrix multiplication over `K(x) = DenseFrac ℚ` -/

/-- Matrix product over a `[CField β]` `matMul A Bm`: the `(i, j)` entry is `Σₖ A[i][k]·Bm[k][j]`. -/
def matMul {β : Type*} [CField β] (A Bm : List (List β)) : List (List β) :=
  let r := (Bm.headD []).length
  A.map (fun rowA =>
    (List.range r).map (fun j =>
      ((List.range rowA.length).foldl (fun acc k =>
        CCommRing.add acc (CCommRing.mul (rowA.getD k CCommRing.zero) ((Bm.getD k []).getD j CCommRing.zero)))
        CCommRing.zero)))

/-! #### `K(x) ↔ K[x]` denominator clearing and lifts -/

/-- Lift a `K[x]` coordinate row to a `K(x, y)` element `rowToAf row = Σᵢ CFrac.ofPoly(rowᵢ)·yⁱ`, turning an
`I_p`-basis row into the order element it represents. -/
def rowToAf (row : List (DensePoly ℚ)) : DensePoly (DenseFrac ℚ) := row.map CFrac.ofPoly

/-- The `I_p`-basis matrix `B` over `K(x)` `ipBasisMatrix n ipRows`: the `n×n` `DenseFrac ℚ`-matrix whose
column `k` is the `k`-th `I_p`-basis row, `B[r][k] = CFrac.ofPoly (ipRows[k][r])` — the change of basis from the
`I_p` basis to the power basis. -/
def ipBasisMatrix (n : ℕ) (ipRows : PolyMatrix DensePoly ℚ) : List (List (DenseFrac ℚ)) :=
  (List.range n).map (fun r =>
    (List.range n).map (fun k => CFrac.ofPoly ((ipRows.getD k []).getD r [])))

/-- Product of the nontrivial normalized denominators in a represented-fraction matrix. -/
private def commonDenom {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {F : (α : Type u) → [CField α] → Type u} [CFrac F P]
    {α : Type u} [CField α] (M : List (List (F α))) : P α :=
  M.foldl (fun acc row =>
    row.foldl (fun a z =>
      let den := CPolyEngine.cnorm (CFrac.den z)
      if CPolyEngine.cisZero den ||
          CPolyEngine.cisZero (CPolyEngine.sub den CPoly.one) then a
      else CPolyEngine.mul a den)
      acc) CPoly.one

/-- Clear a represented-fraction row by multiplying every stored numerator by `δ`. -/
private def clearRow {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {F : (α : Type u) → [CField α] → Type u} [CFrac F P]
    {α : Type u} [CField α] (δ : P α) (row : List (F α)) : List (P α) :=
  row.map (fun z => CPolyEngine.mul δ (CFrac.num z))

example :
    let den := CPoly.SparsePoly.ofList [(0, 1), (1, 1)]
    let z : SparseFrac ℚ := CFrac.ofFraction (CPoly.one : CPoly.SparsePoly ℚ) den
      (by cfrac_nonzero)
    CPolyEngine.cisZero (CPolyEngine.sub (commonDenom [[z]]) den) = true := by
  ccompute

example :
    let δ := CPoly.SparsePoly.ofList [(0, 1), (1, 1)]
    let z : SparseFrac ℚ := CFrac.ofPoly (CPoly.SparsePoly.ofList [(1, 1)])
    CPolyEngine.cisZero (CPolyEngine.sub ((clearRow δ [z]).getD 0 CPoly.czero)
      (CPoly.SparsePoly.ofList [(1, 1), (2, 1)])) = true := by
  ccompute

/-! #### The idealizer of `I_p`, given an order basis (`idealizerBasis`) -/

/-- The idealizer `Î = (I_p : I_p)` as a new `K(x)` order basis `idealizerBasis f orderBasis ipRows`, given
the current order basis and the `I_p` `K[x]`-basis (`pTraceRadical` output). Forms `B = ipBasisMatrix`,
`Mⱼ = B⁻¹ · CPoly.multMatrix f ιⱼ` for each `ιⱼ`, stacks into `M`, clears to `N = δ·M` over `K[x]`, Hermite-reduces,
inverts the first `n` rows, and scales by `δ`: the columns of `δ·N̂⁻¹` are the idealizer basis. Returns
`orderBasis` unchanged if any inverse is singular. -/
def idealizerBasis [CLinearSolve (DenseFrac ℚ)]
    (f : DensePoly (DenseFrac ℚ)) (orderBasis : List (DensePoly (DenseFrac ℚ)))
    (ipRows : PolyMatrix DensePoly ℚ) : List (DensePoly (DenseFrac ℚ)) :=
  let n := cdeg f
  let B : List (List (DenseFrac ℚ)) := ipBasisMatrix n ipRows
  match CLinearSolve.matrixInverse n B with
  | none => orderBasis
  | some Binv =>
    -- stack the `Mⱼ = Binv · CPoly.multMatrix f ιⱼ` (each `n×n` over K(x))
    let M : List (List (DenseFrac ℚ)) :=
      (List.range n).foldr (fun j acc =>
        let ιj : DensePoly (DenseFrac ℚ) := rowToAf ((ipRows.getD j []))
        let Mj := matMul Binv (CPoly.multMatrix f ιj)
        Mj ++ acc) []
    -- clear to K[x] by a common denominator δ
    let δ : DensePoly ℚ := commonDenom M
    let N : PolyMatrix DensePoly ℚ := M.map (clearRow δ)
    -- Hermite-reduce N over K[x]; the first n rows are the upper-triangular invertible part
    let reduced := CPoly.hermiteRowReduce N
    let Nhat : List (List (DenseFrac ℚ)) :=
      (List.range n).map (fun i => (List.range n).map (fun j => CFrac.ofPoly ((reduced.getD i []).getD j [])))
    match CLinearSolve.matrixInverse n Nhat with
    | none => orderBasis
    | some NhatInv =>
      -- columns of δ·N̂⁻¹ are the new basis vectors (in the [1,y,…] order/power basis)
      let δq : DenseFrac ℚ := CFrac.ofPoly δ
      (List.range n).map (fun col =>
        (List.range n).map (fun row => CCommRing.mul δq ((NhatInv.getD row []).getD col CCommRing.zero)))

end DensePoly

/-! #### `round2Step`: one enlargement of the equation order at all bad primes -/

namespace DensePoly

/-- `true` iff a `K(x, y)` order basis equals the power basis `[1, y, …, yⁿ⁻¹]` `isPowerBasis n basis`:
each `basisᵢ` is `cisZero`-equal to `yⁱ`. Tests whether `round2Step` grew the order. -/
def isPowerBasis (n : ℕ) (basis : List (DensePoly (DenseFrac ℚ))) : Bool :=
  (List.range n).all (fun i =>
    cisZero (csub (basis.getD i []) (CPoly.afBasisElem i)))

/-- One Ford–Zassenhaus Round-2 enlargement `round2Step f = (newBasis, grew)`. From the equation order
`O = CPoly.powerBasis f`, for the first bad prime `p = x − a`, computes the p-trace-radical `I_p` and the idealizer
`Î = (I_p : I_p)`, returning `Î`'s basis and whether it strictly enlarged `O`. With no bad prime, returns the
power basis with `grew = false`. -/
def round2Step [CLinearSolve ℚ] [CLinearSolve (DenseFrac ℚ)]
    (f : DensePoly (DenseFrac ℚ)) :
    List (DensePoly (DenseFrac ℚ)) × Bool :=
  let n := cdeg f
  let O := CPoly.powerBasis f
  match (badPrimes f) with
  | [] => (O, false)
  | p :: _ =>
    let pm := cmonic p
    -- root of a monic linear prime `p = [−a, 1]` is `a = −p₀`
    let a : ℚ := CCommRing.neg (pm.getD 0 CCommRing.zero)
    let ip := pTraceRadical f pm a
    let newBasis := idealizerBasis f O ip
    (newBasis, !isPowerBasis n newBasis)

end DensePoly

/-! ### `round2Step` enlarges `[1, y] → [1, y/x]` for `y² = x³`

For the cusp `f = y² − x³`, bad prime `p = x`, `I_x = ⟨x, y⟩`, and the idealizer gives the new basis
`[1, y/x]` (integral: `(y/x)² = x`); a second step does not grow it, so `[1, y/x]` is the maximal order. -/

open DensePoly

/-- The enlarged generator `y/x ∈ ℚ(x)[y]/(y² − x³)`, the second basis vector of `round2Step`
(`[0, 1/x]` in the `[1, y]` order basis). -/
def cuspNewGen : DensePoly (DenseFrac ℚ) := (round2Step cuspF).1.getD 1 []

/-- `round2Step` enlarges the cusp order: `(round2Step cuspF).2 = true`, the idealizer strictly contains
`[1, y]`. -/
theorem cusp_round2_grew :
    (round2Step cuspF).2 = true := by native_decide

/-- The enlarged generator is `y/x`: `round2Step cuspF` produces `[1, y/x]` (second vector `[0, 1/x]`, first
`[1]`), checked by `cisZero (cuspNewGen − [0, 1/x])`. -/
theorem cusp_round2_newGen_eq :
    (cisZero (csub cuspNewGen [CCommRing.zero, CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)])
      && cisZero (csub ((round2Step cuspF).1.getD 0 []) [CCommRing.one])) = true := by native_decide

/-- The enlarged generator `y/x` is integral: `CPoly.mulMod f (y/x) (y/x) = x` in `ℚ(x)[y]/(y² − x³)`, checked by
`cisZero (CPoly.mulMod f (y/x) (y/x) − x)`. -/
theorem cusp_newGen_integral :
    cisZero (csub (CPoly.mulMod cuspF cuspNewGen cuspNewGen) [CFrac.ofPoly [0, 1]]) = true := by native_decide

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

/-- The node curve `f = y² − x²(x + 1) = y² − x³ − x² ∈ ℚ(x)[y]` (`a₀ = −(x³ + x²)`, monic), `DensePoly
(DenseFrac ℚ)` `[−(x³ + x²), 0, 1]`. An ordinary double point; `[1, y]` is non-maximal at `x`. -/
def nodeF : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [0, 0, -1, -1], CCommRing.zero, CCommRing.one]

/-- The enlarged generator `y/x ∈ ℚ(x)[y]/(y² − x²(x+1))`, the second basis vector of `round2Step nodeF`
(`[0, 1/x]`). -/
def nodeNewGen : DensePoly (DenseFrac ℚ) := (round2Step nodeF).1.getD 1 []

/-- The node bad prime is `x`, and `round2Step` enlarges to `[1, y/x]`: `badPrimes nodeF = [x]`, `.2 = true`,
new generator `[0, 1/x] = y/x`, first vector `1`. -/
theorem node_round2_newGen_eq :
    ((badPrimes nodeF).map cmonic = [([0, 1] : DensePoly ℚ)]
      && (round2Step nodeF).2
      && cisZero (csub nodeNewGen [CCommRing.zero, CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)])
      && cisZero (csub ((round2Step nodeF).1.getD 0 []) [CCommRing.one])) = true := by
  native_decide

/-- The node's enlarged generator is integral with relation `(y/x)² = x + 1`: `CPoly.mulMod f (y/x) (y/x) = x + 1`
in `ℚ(x)[y]/(y² − x²(x+1))`, checked by `cisZero (CPoly.mulMod f (y/x) (y/x) − (x + 1))`. -/
theorem node_newGen_integral :
    cisZero (csub (CPoly.mulMod nodeF nodeNewGen nodeNewGen) [CFrac.ofPoly [1, 1]]) = true := by native_decide

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
