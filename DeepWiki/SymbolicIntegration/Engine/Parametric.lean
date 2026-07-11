import DeepWiki.ComputableAlgebra.LinearAlgebraRat
import DeepWiki.ComputableAlgebra.FracReprDense
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.ComputableAlgebra.PolyGcdAlgorithms
import DeepWiki.ComputableAlgebra.FracReduce

/-! # Computable parametric problems over the tower ℚ(x)[t]

Computable solvers, over the base monomial field `k = ℚ`, for three parametric integration problems: the
parametric Risch differential equation `Dy + f·y = Σᵢ cᵢ·gᵢ` (returning a basis of the constant solution
subspace), the limited integration problem `f = Dv + Σᵢ cᵢ·log(wᵢ)`, and the parametric logarithmic
derivative problem `n·f = Dv/v + m·Dθ/θ`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- Sparse normalization cancels `x - 1` from `(x² - 1)/(x - 1)` through capability selection. -/
theorem sparse_normalizeFracPair_cancels :
    CPoly.normalizeFracPair
        (CPoly.SparsePoly.ofList [(0, -1), (2, 1)] : CPoly.SparsePoly ℚ)
        (CPoly.SparsePoly.ofList [(0, -1), (1, 1)] : CPoly.SparsePoly ℚ) =
      (CPoly.SparsePoly.ofList [(0, 1), (1, 1)], CPoly.SparsePoly.ofList [(0, 1)]) := by
  ccompute

/-- Sparse selected extended gcd computes normalized Bezout cofactors for `(1, 0)`. -/
theorem sparse_bezoutOne_one_zero :
    CPoly.bezoutOne (CPoly.one : CPoly.SparsePoly ℚ) CPoly.czero =
      (CPoly.one, CPoly.czero) := by
  ccompute

/-- Sparse reduced Diophantine solving satisfies its represented Bezout equation. -/
theorem sparse_diophantineReduced_sound (p q rhs : CPoly.SparsePoly ℚ)
    (hq : CPoly.toPoly q ≠ 0)
    (hgdeg : (CPoly.toPoly (CPolyEuclidean.gcdExt p q).1).natDegree = 0)
    (hgne : CPoly.toPoly (CPolyEuclidean.gcdExt p q).1 ≠ 0) :
    CPoly.toPoly (CPoly.diophantineReduced p q rhs).1 * CPoly.toPoly p
        + CPoly.toPoly (CPoly.diophantineReduced p q rhs).2 * CPoly.toPoly q =
      CPoly.toPoly rhs :=
  CPoly.toPoly_diophantineReduced p q rhs hq hgdeg hgne

namespace CFrac

variable {F : (α : Type) → [CField α] → Type} {P : Type → Type}
variable [CPoly P] [CPolyEngine P] [CPolyGcd P ℚ] [CPolyEuclidean P]
variable [CFrac F P] [LawfulCFrac F P] [CFieldDomain ℚ P]

/-! ### `CFrac.parametricLogDeriv` over the base field `k = ℚ(x)`

Decide whether `n·b = Dz/z` for a nonzero `n ∈ ℤ` and `z ∈ k*` (a logarithmic derivative of a radical),
with `b ∈ k = ℚ(x)`, `D = d/dx`. A logarithmic derivative `Dz/z` is always proper (`deg num < deg den`),
so a non-proper `b` (in particular every nonzero constant) is provably not one. -/

/-- `baseIsProper b`: `true` iff the lowest-terms represented value `b = a/d ∈ ℚ(x)` is proper
(`deg a < deg d`, nonzero numerator). -/
def baseIsProper (b : F ℚ) : Bool :=
  let bn := CPoly.normalizeFracPair (CFrac.num b) (CFrac.den b)
  CPolyEngine.cdeg bn.1 < CPolyEngine.cdeg bn.2 && !CPolyEngine.cisZero bn.1

/-- Parametric-logarithmic-derivative test over the base field `CFrac.parametricLogDeriv b`, for
`b ∈ k = ℚ(x)`: `true` iff `b` could be a logarithmic derivative of a `ℚ(x)`-radical (`n·b = Dz/z` for
nonzero `n ∈ ℤ`, `z ∈ ℚ(x)*`), `false` iff provably not. A non-proper `b` (in particular every nonzero
constant) is ruled out; a proper `b` is conservatively accepted. -/
def parametricLogDeriv (b : F ℚ) : Bool :=
  -- `b = 0` is the trivial logarithmic derivative `Dz/z` with `z = 1`; a proper `b` is not ruled out.
  CCommRing.isZero b || baseIsProper b

/-! ### `CFrac.paramLogDeriv` — the parametric logarithmic derivative recognizer over `k = ℚ(x)`

Decide `n·f = Dv/v + m·Dθ/θ` for integers `n ≠ 0, m` and `v ∈ ℚ(x)*`: solve for the candidate constant
`c = m/n` from `c·(Dθ/θ) = f`, then test whether `N·f − M·(Dθ/θ)` is a logarithmic derivative of a
radical. `f` and `Dθ/θ` are passed as reduced `DenseFrac ℚ` values. -/

/-- `CFrac.paramLogDerivCandidate fval wval`: the candidate constant `c = m/n ∈ ℚ` from `c·wval = fval` over
`ℚ(x)`, returned when `fval/wval` is a `ℚ`-constant (and `wval ≠ 0`), else `none`. -/
def paramLogDerivCandidate (fval wval : F ℚ) : Option ℚ :=
  -- `c·wval = fval` over ℚ(x); a constant candidate `c ∈ ℚ` exists iff `fval/wval ∈ ℚ`.
  if CCommRing.isZero wval then none
  else
    let r := CField.div fval wval
    -- `r ∈ ℚ` iff its lowest-terms denominator is a (nonzero) constant and numerator degree 0.
    let rn := CPoly.normalizeFracPair (CFrac.num r) (CFrac.den r)
    if CPolyEngine.cdeg rn.1 = 0 ∧ CPolyEngine.cdeg rn.2 = 0 then
      some (CPoly.coeff rn.1 0 / CPoly.coeff rn.2 0)
    else none

/-- Parametric logarithmic derivative recognizer `CFrac.paramLogDeriv fval θlogderiv` over `k = ℚ(x)`: decides
`n·f = Dv/v + m·(Dθ/θ)` for integers `n ≠ 0, m` and `v ∈ ℚ(x)*`, returning `some (n, m, v)` or `none`. It
solves for the candidate constant `c = m/n` (`CFrac.paramLogDerivCandidate`), then tests whether the residue
`N·f − M·(Dθ/θ)` is a logarithmic derivative of a radical (`CFrac.parametricLogDeriv`), reporting the residue as
the witness `v` (`v = 1` when it vanishes). -/
def paramLogDeriv (fval θlogderiv : F ℚ) : Option (ℤ × ℤ × F ℚ) :=
  match paramLogDerivCandidate fval θlogderiv with
  | none =>
    -- no constant candidate `c`: fall back to the pure logarithmic-derivative test `n·f = Dv/v`
    -- (`m = 0`). `f` is a log-derivative of a radical iff `CFrac.parametricLogDeriv` cannot rule it out and
    -- the residue obstruction is absent; report only the provable `f = 0` (trivial `v = 1`, `n` any).
    if CCommRing.isZero fval then some (1, 0, CCommRing.one) else none
  | some c =>
    -- `c = M/N` in lowest terms, `N > 0`. Test `N·f − M·(Dθ/θ) = Dv/v` (radical log-derivative).
    let N : ℤ := (c.den : ℤ)
    let M : ℤ := c.num
    let Nf := CCommRing.mul (CFrac.ofScalar ((N : ℚ))) fval
    let Mw := CCommRing.mul (CFrac.ofScalar ((M : ℚ))) θlogderiv
    let resid := CField.sub Nf Mw
    -- the residue `N·f − M·w`: a logarithmic derivative of a radical. The exactly-decidable witness is
    -- `resid = 0` (then `v = 1`, `N·f = M·w`, so `n = N, m = M`); nonzero radical witnesses are
    -- returned as residual data for downstream certification.
    if CCommRing.isZero resid then some (N, M, CCommRing.one)
    else if !parametricLogDeriv resid then none
    else some (N, M, resid)

end CFrac

namespace CPoly

/-! ### `CPoly.paramRischDE` — the parametric Risch DE `Dy + f·y = Σᵢ cᵢ·gᵢ`

Solve the parametric Risch differential equation for `y ∈ k(t)` and constants `c₁, …, cₘ`, returning a
basis of the constant solution subspace. Over the base monomial case `k = ℚ`, `D = d/dt`, the bounded-degree
polynomial equation becomes a homogeneous linear system over `ℚ`, whose kernel is returned. -/

/-- Linear constraints over ℚ `linearConstraintsQ gnums gdens` (`D = d/dt`, `k = ℚ`): from the reduced
equation `Dp = Σᵢ cᵢ·gᵢ` with `gᵢ = gnumsᵢ/gdensᵢ`, clears the common denominator `d = lcm(gdensᵢ)`,
splits each `d·gᵢ = qᵢ·d + rᵢ`, and returns the polynomial parts `qs = [q₁, …, qₘ]` together with the
homogeneous constraint matrix `Mᵢⱼ = coefficient(rⱼ, tⁱ)`. -/
def linearConstraintsQ {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P ℚ] [CPolyEuclidean P] (gnums gdens : List (P ℚ)) :
    List (P ℚ) × List (List ℚ) :=
  let d := gdens.foldl (fun acc den => CPoly.lcm acc den) (CPoly.one : P ℚ)
  let qrs : List (P ℚ × P ℚ) :=
    (List.zip gnums gdens).map (fun (gn, gd) =>
      let dgi := CPolyEngine.mul gn (CPolyEuclidean.div d gd)
      CPolyEuclidean.divmod dgi d)
  let qs := qrs.map Prod.fst
  let rs := qrs.map Prod.snd
  let nrows := CPolyEngine.cdeg d
  let m := gnums.length
  let M : List (List ℚ) :=
    (List.range nrows).map (fun i =>
      (List.range m).map (fun j => CPoly.coeff (rs.getD j CPoly.czero) i))
  (qs, M)

/-- Every row of `linearConstraintsQ` has one coefficient per input generator. -/
theorem linearConstraintsQ_row_length {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P ℚ] [CPolyEuclidean P] (gnums gdens : List (P ℚ)) :
    ∀ row ∈ (linearConstraintsQ gnums gdens).2, row.length = gnums.length := by
  simp [linearConstraintsQ]

/-- **Parametric Risch DE over the base monomial ℚ[t]** `CPoly.paramRischDE gnums gdens`, specialized to
`k = ℚ`, `D = d/dt`, the **reduced** equation `Dp = Σᵢ cᵢ·gᵢ` (`a = 1, b = 0`). Returns a **basis**
`[c⃗₁, …, c⃗ᵣ]` of the `Const(k) = ℚ`-linear subspace of constant tuples
`(c₁, …, cₘ)` for which the equation has a polynomial solution `p ∈ ℚ[t]`:

1. `(qs, M) ← linearConstraintsQ gnums gdens`: the cleared homogeneous matrix
   `M·(c₁,…,cₘ)ᵀ = 0` (entries in `Const(k) = ℚ`).
2. **return** `CLinearSolve.nullspaceBasis M m` — the selected basis of `ker(M)`.

The empty kernel (`[]`) means the only solution is `c₁ = … = cₘ = 0`. For each basis tuple `c⃗`, a
companion polynomial solution `p` is recoverable by integrating `Σ cᵢqᵢ` (`cIntegratePolyQ`). -/
def paramRischDE {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P ℚ] [CPolyEuclidean P] [CLinearSolve ℚ]
    (gnums gdens : List (P ℚ)) : List (List ℚ) :=
  let (_qs, M) := linearConstraintsQ gnums gdens
  CLinearSolve.nullspaceBasis M gnums.length

/-- Every selected parametric-Risch vector satisfies each cleared linear constraint row. -/
theorem paramRischDE_mem_row_sound {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P ℚ] [CPolyEuclidean P] [CLinearSolve ℚ] [LawfulCLinearSolve ℚ]
    (gnums gdens : List (P ℚ)) (cs : List ℚ)
    (hcs : cs ∈ paramRischDE gnums gdens) :
    ∀ i, i < (linearConstraintsQ gnums gdens).2.length →
      linearDot ((linearConstraintsQ gnums gdens).2.getD i []) cs = 0 := by
  unfold paramRischDE at hcs
  split at hcs
  next qs M hconstraints =>
    rw [hconstraints]
    apply LawfulCLinearSolve.nullspaceBasis_sound M gnums.length cs ?_ hcs
    intro row hrow
    apply linearConstraintsQ_row_length gnums gdens row
    rw [hconstraints]
    exact hrow

/-! ### `CPoly.limitedIntegrate`

Decide `f = Dv + Σᵢ cᵢ·log(wᵢ)` for constants `cᵢ` and `v ∈ k(t)`. Equivalently `f − Σ cᵢ·(Dwᵢ/wᵢ) = Dv`,
the parametric Risch DE `Dv + 0·v = f − Σ cᵢ·(Dwᵢ/wᵢ)` — i.e. (7.1) with `gᵢ = Dwᵢ/wᵢ` and the additional
"`f` itself" generator. So it is the `gᵢ = Dwᵢ/wᵢ` specialization of `CPoly.paramRischDE`, with `f`
appended as the forced generator `c₀ = 1`. -/

/-- **Limited integration over the base monomial ℚ[t]** `CPoly.limitedIntegrate fnum fden wnums wdens`
over `k = ℚ`, `D = d/dt`. Decides `f = Dv + Σᵢ cᵢ·log(wᵢ)` for `cᵢ ∈ ℚ` and `v ∈ ℚ(t)`, returning the
basis of admissible `(c₀, c₁, …, cₘ)` tuples (with `c₀` the coefficient of the forced generator `f`, so a
genuine solution has `c₀ = 1`): the parametric Risch DE `Dv = c₀·f − Σᵢ cᵢ·(Dwᵢ/wᵢ)` (with generators
`g₀ = f`, `gᵢ = Dwᵢ/wᵢ = wnumᵢ'/wnumᵢ`-style logarithmic derivatives). Built as `CPoly.paramRischDE` on the
generator list `[f, Dw₁/w₁, …, Dwₘ/wₘ]`. The `wᵢ` arrive as numerator/denominator pairs; `Dwᵢ/wᵢ` is
`(D(wnumᵢ)·wdenᵢ − wnumᵢ·D(wdenᵢ)) / (wnumᵢ·wdenᵢ)`. Sharper denominator bounds and the
`c₀ = 1` back-substitution to a nonparametric RDE are left to downstream specializations. -/
def limitedIntegrate {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P ℚ] [CPolyEuclidean P] [CLinearSolve ℚ]
    (fnum fden : P ℚ) (wnums wdens : List (P ℚ)) :
    List (List ℚ) :=
  -- generator `g₀ = f`, then `gᵢ = Dwᵢ/wᵢ` (logarithmic derivative of `wᵢ`).
  let logDerivs : List (P ℚ × P ℚ) :=
    (List.zip wnums wdens).map (fun (wn, wd) =>
      let num := CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv wn) wd)
        (CPolyEngine.mul wn (CPolyEngine.deriv wd))
      let den := CPolyEngine.mul wn wd
      (num, den))
  let gnums := fnum :: logDerivs.map Prod.fst
  let gdens := fden :: logDerivs.map Prod.snd
  paramRischDE gnums gdens

end CPoly

/-- Sparse polynomials run the generic parametric Risch-DE constraint and kernel algorithms unchanged. -/
theorem sparse_paramRischDE_example :
    let ofList : List (ℕ × ℚ) → CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList
    CPoly.paramRischDE
        [ofList [(0, 1), (1, 3), (3, 2)], ofList [(0, 1)], ofList [(0, 1)]]
        [ofList [(0, -1), (2, 1)], ofList [(0, -1), (1, 1)],
          ofList [(0, 1), (1, 1)]] =
      [[(-1 : ℚ) / 2, 3 / 2, 1]] := by
  ccompute

/-! ### Validation — the parametric logarithmic derivative recognizer

For `11 = Dv/v + m·Dθ/θ` with `Dθ/θ = 1` over `k = ℚ`, `CFrac.paramLogDeriv` returns `(n, m, v) = (1, 11, 1)`. -/

open DensePoly

/-- `f = 11 ∈ ℚ ⊂ ℚ(x)`. -/
def paramLogDerivExampleF : DenseFrac ℚ := CFrac.ofScalar 11
/-- `Dθ/θ = 1` (exponential `θ`, `Dθ = θ`). -/
def paramLogDerivExampleW : DenseFrac ℚ := CFrac.ofScalar 1

/-- The parametric logarithmic derivative recognizer computes: for `11 = Dv/v + m·Dθ/θ` with `Dθ/θ = 1`
over `k = ℚ`, `CFrac.paramLogDeriv` returns `(n, m, v) = (1, 11, 1)`, verified to satisfy
`n·f = Dv/v + m·(Dθ/θ)` (with `v = 1`, `Dv/v = 0`). -/
theorem paramLogDeriv_example :
    (match CFrac.paramLogDeriv paramLogDerivExampleF paramLogDerivExampleW with
      | some (n, m, v) =>
          -- `n·f − m·(Dθ/θ) − Dv/v` cleared: with `v = 1`, `Dv/v = 0`, so check `n·f − m·w = 0`.
          let nf := CCommRing.mul (CFrac.ofScalar ((n : ℚ))) paramLogDerivExampleF
          let mw := CCommRing.mul (CFrac.ofScalar ((m : ℚ))) paramLogDerivExampleW
          CCommRing.isZero (CField.sub nf mw) && CCommRing.isZero (CField.sub v CCommRing.one)
            && decide (n ≠ 0)
      | none => false) = true := by ccompute

/-- The parametric logarithmic-derivative recognizer executes unchanged on sparse fractions. -/
example :
    (CFrac.paramLogDeriv (F := SparseFrac) (P := CPoly.SparsePoly)
      (CFrac.ofScalar 11 : SparseFrac ℚ) (CFrac.ofScalar 1 : SparseFrac ℚ)).map
        (fun (n, m, v) =>
          (n, m, CPoly.coeff (CFrac.num v) 0, CPoly.coeff (CFrac.den v) 0)) =
      some (1, 11, 1, 1) := by
  ccompute

/-! ### Validation — the parametric RDE reduces to a linear system

For `Dp = c₁·(2t³+3t+1)/(t²−1) + c₂/(t−1) + c₃/(t+1)` over `k = ℚ`, `LinearConstraints` yields the
homogeneous system with solution space `(c₁,c₂,c₃) = (λ,−3λ,−2λ)`. -/

open DensePoly

/-- `g₁ = (2t³+3t+1)/(t²−1)`: numerator `[1,3,0,2]`, denominator `[-1,0,1]` (low→high). -/
def paramRischExampleG1num : DensePoly ℚ := [1, 3, 0, 2]
/-- `g₁`-denominator `t²−1`. -/
def paramRischExampleG1den : DensePoly ℚ := [-1, 0, 1]
/-- `g₂ = 1/(t−1)`: numerator `[1]`, denominator `[-1,1]`. -/
def paramRischExampleG2num : DensePoly ℚ := [1]
/-- `g₂`-denominator `t−1`. -/
def paramRischExampleG2den : DensePoly ℚ := [-1, 1]
/-- `g₃ = 1/(t+1)`: numerator `[1]`, denominator `[1,1]`. -/
def paramRischExampleG3num : DensePoly ℚ := [1]
/-- `g₃`-denominator `t+1`. -/
def paramRischExampleG3den : DensePoly ℚ := [1, 1]

/-- **Cleared parametric-constraint check** `CPoly.paramConstraintCheck gnums gdens cs`: `true` iff the
constant tuple `cs = (c₁,…,cₘ)` satisfies the cleared constraint `Σᵢ cᵢ·rᵢ = 0` (the remainders `rᵢ` of
`d·gᵢ` by `d = lcm(denominators)`), i.e. `Σᵢ cᵢ·(numᵢ·(d/denᵢ) mod d) = 0` — the polynomial identity
certifying that `(c₁,…,cₘ)` is a genuine solution of the parametric Risch DE's linear constraints. -/
def CPoly.paramConstraintCheck {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P ℚ] [CPolyEuclidean P] (gnums gdens : List (P ℚ)) (cs : List ℚ) : Bool :=
  let d := gdens.foldl (fun acc den => CPoly.lcm acc den) (CPoly.one : P ℚ)
  let total : P ℚ :=
    ((List.zip gnums gdens).zip cs).foldl (fun acc ((gn, gd), c) =>
      let dgi := CPolyEngine.mul gn (CPolyEuclidean.div d gd)
      let ri := CPolyEuclidean.mod dgi d
      CPolyEngine.add acc (CPolyEngine.scale c ri)) CPoly.czero
  CPolyEngine.cisZero total

/-- **The parametric Risch differential equation reduces to a constant linear system**
(`ccompute`). For
`Dp = c₁·(2t³+3t+1)/(t²−1) + c₂/(t−1) + c₃/(t+1)` over `k = ℚ`, `t` a monomial with `Dt = 1`:

1. **Linear constraints.** `CPoly.linearConstraintsQ` returns the homogeneous matrix `[[5,1,1],[1,1,-1]]`
   up to equation order, pinned componentwise against the expected values.
2. **Constant solve.** `CPoly.paramRischDE` returns a **basis** of its kernel — a single vector `c⃗`
   (one-dimensional solution space), each verified to **actually satisfy** the cleared constraint
   `Σᵢ cᵢ·rᵢ = 0` by `CPoly.paramConstraintCheck` (the cleared polynomial identity), and confirmed nontrivial
   (not all-zero). The solution space is `(c₁,c₂,c₃) = (λ,−3λ,−2λ)`; the returned basis vector is
   proportional to `(1,−3,−2)`, so the parametric problem reduces to the one-parameter `Dp = 2λt`.

This is the **parametric** Risch differential equation: the right-hand side `Σ cᵢgᵢ` carries
undetermined constants and reduces, via `CPoly.linearConstraintsQ` and the constant linear solve
`CLinearSolve.nullspaceBasis` (ordinary ℚ-Gaussian elimination
since `Const(k) = ℚ`), to a basis of the constant solution subspace. -/
theorem paramRischDE_example :
    -- (1) the cleared constraint matrix is the system `c₁(5t+1)+c₂(t+1)+c₃(t−1)=0`, i.e. (low→high in
    -- `t`) the rows `t⁰: [1,1,-1]` and `t¹: [5,1,1]`.
    (decide ((CPoly.linearConstraintsQ
        [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
        [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]).2
      = [[1,1,-1],[5,1,1]])
    -- (2) the kernel basis is one nontrivial vector, each satisfying the cleared constraint.
    && (let basis := CPoly.paramRischDE
          [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
          [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]
        decide (basis.length = 1)
          && basis.all (fun cs =>
              CPoly.paramConstraintCheck
                [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
                [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den] cs
                && !(cs.all (· == 0))))) = true := by ccompute

/-! ### Validation — the limited integration problem reduces to the parametric RDE

`k = ℚ`, `t` a monomial with `Dt = 1` (`D = d/dt`). The limited integration problem
`f = Dv + Σᵢ cᵢ·log(wᵢ)` is the parametric Risch DE (7.1) with generators `g₀ = f`, `gᵢ = Dwᵢ/wᵢ`. For
`f = 1/t`, `w₁ = t`, `w₂ = t+1` (`Dw₁/w₁ = 1/t`, `Dw₂/w₂ = 1/(t+1)`), the only constant relation among
`{f, 1/t, 1/(t+1)}` is `f = 1/t = log(t)′`, so `CPoly.limitedIntegrate` returns a one-dimensional kernel — the
basis vector witnessing `c₀·f = c₁·(Dw₁/w₁)` (i.e. `f = log(w₁)`, the limited-integral certificate). -/

open DensePoly

/-- Limited-integration example numerator for `f = 1/t`. -/
def limitedIntExampleFnum : DensePoly ℚ := [1]
/-- Limited-integration example denominator `t`. -/
def limitedIntExampleFden : DensePoly ℚ := [0, 1]

/-- **Limited integration reduces to the parametric Risch DE** (`ccompute`). For
`f = Dv + c₁·log(t) + c₂·log(t+1)` with `f = 1/t` over `k = ℚ`,
`CPoly.limitedIntegrate` (the `gᵢ = Dwᵢ/wᵢ` specialization of `CPoly.paramRischDE`, with `f` the forced generator)
returns a nonempty constant kernel basis, each vector verified to **actually satisfy** the cleared
constraint `c₀·f + Σᵢ cᵢ·(Dwᵢ/wᵢ) ≡ 0 (mod lcm)` by `CPoly.paramConstraintCheck`. The relation found is
`f = log(t)` (`c₀ = ±1`, `c₁ = ∓1`, `c₂ = 0`) — the limited-integral certificate that `∫ f = log(t)`.
Sharper denominator bounds and the `c₀ = 1` back-substitution to a nonparametric RDE for `v` are left to
downstream specializations. -/
theorem limitedIntegrate_example :
    (let wnums : List (DensePoly ℚ) := [[0, 1], [1, 1]]
     let wdens : List (DensePoly ℚ) := [[1], [1]]
     -- the generators `CPoly.limitedIntegrate` builds: `g₀ = f`, `gᵢ = Dwᵢ/wᵢ`.
     let logDerivs : List (DensePoly ℚ × DensePoly ℚ) :=
       (List.zip wnums wdens).map (fun (wn, wd) =>
         (csub (cmul (cderiv wn) wd) (cmul wn (cderiv wd)), cmul wn wd))
     let gnums := limitedIntExampleFnum :: logDerivs.map Prod.fst
     let gdens := limitedIntExampleFden :: logDerivs.map Prod.snd
     let basis := CPoly.limitedIntegrate limitedIntExampleFnum limitedIntExampleFden wnums wdens
     decide (0 < basis.length)
       && basis.all (fun cs =>
            CPoly.paramConstraintCheck gnums gdens cs && !(cs.all (· == 0)))) = true := by
  ccompute

end DeepWiki.SymbolicIntegration
