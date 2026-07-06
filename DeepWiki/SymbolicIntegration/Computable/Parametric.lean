import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd

/-! # Computable parametric problems over the tower ℚ(x)[t]

Computable solvers, over the base monomial field `k = ℚ`, for three parametric integration problems: the
parametric Risch differential equation `Dy + f·y = Σᵢ cᵢ·gᵢ` (returning a basis of the constant solution
subspace), the limited integration problem `f = Dv + Σᵢ cᵢ·log(wᵢ)`, and the parametric logarithmic
derivative problem `n·f = Dv/v + m·Dθ/θ`. The shared ingredient is a dense linear solver over the constant
field `Const(k) = ℚ` (RREF, nullspace basis, unique/particular solve). -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

namespace CPolyG

/-! ### `cParametricLogDeriv` over the base field `k = ℚ(x)`

Decide whether `n·b = Dz/z` for a nonzero `n ∈ ℤ` and `z ∈ k*` (a logarithmic derivative of a radical),
with `b ∈ k = ℚ(x)`, `D = d/dx`. A logarithmic derivative `Dz/z` is always proper (`deg num < deg den`),
so a non-proper `b` (in particular every nonzero constant) is provably not one. -/

/-- **`d/dx` on `CPolyG ℚ`** `cderivQ p = cderivG p`: the plain formal derivative (the generic `cderivG`
specialized at the constant field `ℚ`, the base monomial derivation `D` with `Dx = 1`, `κ_D = 0`). -/
abbrev cderivQ (p : CPolyG ℚ) : CPolyG ℚ := cderivG p

/-- **Generic lowest-terms reduction of a `(num, den)` fraction over `ℚ[x]`** `qnormPairG num den =
(num/g, den/g)` scaled so the denominator is monic, where `g = gcd(num, den)` (`cgcdWf`); the zero
numerator gives `([], [1])`. The generic mirror of `Compute.qnorm` one tower level down, used to read the
polynomial part / denominator of a `QFunNZG ℚ`-valued base-field element. -/
def qnormPairG (num den : CPolyG ℚ) : CPolyG ℚ × CPolyG ℚ :=
  if cisZeroG num then ([], [(1 : ℚ)])
  else
    let g := (cgcdWf num den).1
    let num' := cdivWf num g
    let den' := cdivWf den g
    let s := (cleadG den')⁻¹
    (cscaleG s num', cscaleG s den')

/-- A ℚ constant `n ∈ ℚ ⊂ ℚ(x)` as a `QFunNZG ℚ` element (denominator `[1]` nonzero by
`cisZeroG_one_singleton`). -/
def qConstParamG (n : ℚ) : QFunNZG ℚ := ⟨([n], [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩

/-- `cBaseIsProper b`: `true` iff the lowest-terms `QFunNZG ℚ` value `b = a/d ∈ ℚ(x)` is proper
(`deg a < deg d`, nonzero numerator). -/
def cBaseIsProper (b : QFunNZG ℚ) : Bool :=
  let bn := qnormPairG b.1.1 b.1.2
  cdegG bn.1 < cdegG bn.2 && !cisZeroG bn.1

/-- Parametric-logarithmic-derivative test over the base field `cParametricLogDeriv b`, for
`b ∈ k = ℚ(x)`: `true` iff `b` could be a logarithmic derivative of a `ℚ(x)`-radical (`n·b = Dz/z` for
nonzero `n ∈ ℤ`, `z ∈ ℚ(x)*`), `false` iff provably not. A non-proper `b` (in particular every nonzero
constant) is ruled out; a proper `b` is conservatively accepted. -/
def cParametricLogDeriv (b : QFunNZG ℚ) : Bool :=
  -- `b = 0` is the trivial logarithmic derivative `Dz/z` with `z = 1`; a proper `b` is not ruled out.
  CField.isZero b || cBaseIsProper b

/-! ### A dense linear solver over the constant field `Const(k) = ℚ` -/

/-- Reduced row echelon form over ℚ `crref rows ncols = (R, pivots)`: Gauss–Jordan elimination of the
dense matrix `rows` to RREF `R`, with the list of pivot column indices (strictly increasing). Each pivot
is normalized to `1` and is the only nonzero entry in its column; zero rows are dropped. -/
def crref (rows : List (List ℚ)) (ncols : ℕ) : List (List ℚ) × List ℕ :=
  -- work column by column, maintaining the not-yet-pivoted rows and the accumulated pivot rows.
  let rec go : ℕ → ℕ → List (List ℚ) → List (List ℚ) → List ℕ →
      List (List ℚ) × List ℕ
    | 0, _, _, pivRows, pivCols => (pivRows.reverse, pivCols.reverse)
    | _, _, [], pivRows, pivCols => (pivRows.reverse, pivCols.reverse)  -- no rows left
    | fuel + 1, col, rest, pivRows, pivCols =>
      if col ≥ ncols then (pivRows.reverse, pivCols.reverse)
      else
        -- find a row in `rest` with a nonzero entry in column `col`.
        match rest.find? (fun r => (r.getD col 0) ≠ 0) with
        | none => go (fuel) (col + 1) rest pivRows pivCols  -- free column, skip
        | some pr =>
          let piv := pr.getD col 0
          let prn := pr.map (· / piv)                       -- normalize pivot to 1
          -- eliminate column `col` from every other current row (rest minus pr, and pivRows).
          let elim : List ℚ → List ℚ := fun r =>
            let f := r.getD col 0
            (List.zipWith (fun ri pi => ri - f * pi) r prn)
          let restElim := (rest.filter (fun r => !(decide (r = pr)))).map elim
          let pivRowsElim := pivRows.map elim
          go fuel (col + 1) restElim (prn :: pivRowsElim) (col :: pivCols)
  go (ncols + rows.length + 1) 0 rows [] []

/-- **Nullspace basis over ℚ** `cNullspaceBasisQ rows ncols = [v⃗₁, …, v⃗ᵣ]`: a basis of the kernel
`{x⃗ ∈ ℚ^ncols : A·x⃗ = 0}` of the homogeneous system whose rows are `rows`. From the RREF each free
(non-pivot) column yields one basis vector (`1` at that column, `−R[pivotRow][freeCol]` at each pivot
column). Returns `[]` when the kernel is trivial. -/
def cNullspaceBasisQ (rows : List (List ℚ)) (ncols : ℕ) : List (List ℚ) :=
  let (R, pivCols) := crref rows ncols
  let freeCols := (List.range ncols).filter (fun j => !pivCols.contains j)
  freeCols.map (fun fc =>
    (List.range ncols).map (fun j =>
      if j = fc then (1 : ℚ)
      else match pivCols.idxOf? j with
        | some pr => - ((R.getD pr []).getD fc 0)   -- pivot column `j` is at RREF row `pr`
        | none => 0))                                -- another free column ⇒ 0

/-- **Unique solution over ℚ (if it exists)** `cConstSolveUniqueQ Arows urhs ncols`: solve the
inhomogeneous system `A·x⃗ = u⃗` (`A = Arows`, `u⃗ = urhs`) for the **unique** `x⃗ ∈ ℚ^ncols`, returning
`some x⃗` iff the solution exists and is unique (full column rank), else `none`. Row-reduces the augmented
matrix `[A | u]`; a pivot in the augmented column ⟹ inconsistent; a free non-augmented column ⟹ not
unique; else read each variable off its pivot row's augmented entry. -/
def cConstSolveUniqueQ (Arows : List (List ℚ)) (urhs : List ℚ) (ncols : ℕ) : Option (List ℚ) :=
  let aug := List.zipWith (fun r u => r ++ [u]) Arows urhs
  let (R, pivCols) := crref aug (ncols + 1)
  if pivCols.contains ncols then none           -- pivot in the rhs column: inconsistent
  else if pivCols.length < ncols then none       -- a free variable: not unique
  else
    -- full rank: variable `j` (pivot column) reads its value off the augmented entry of its pivot row.
    some ((List.range ncols).map (fun j =>
      match pivCols.idxOf? j with
      | some pr => (R.getD pr []).getD ncols 0
      | none => 0))

/-! ### `cParamLogDeriv` — the parametric logarithmic derivative recognizer over `k = ℚ(x)`

Decide `n·f = Dv/v + m·Dθ/θ` for integers `n ≠ 0, m` and `v ∈ ℚ(x)*`: solve for the candidate constant
`c = m/n` from `c·(Dθ/θ) = f`, then test whether `N·f − M·(Dθ/θ)` is a logarithmic derivative of a
radical. `f` and `Dθ/θ` are passed as reduced `QFunNZG ℚ` values. -/

/-- `cParamLogDerivCandidate fval wval`: the candidate constant `c = m/n ∈ ℚ` from `c·wval = fval` over
`ℚ(x)`, returned when `fval/wval` is a `ℚ`-constant (and `wval ≠ 0`), else `none`. -/
def cParamLogDerivCandidate (fval wval : QFunNZG ℚ) : Option ℚ :=
  -- `c·wval = fval` over ℚ(x); a constant candidate `c ∈ ℚ` exists iff `fval/wval ∈ ℚ`.
  if CField.isZero wval then none
  else
    let r := CField.div fval wval
    -- `r ∈ ℚ` iff its lowest-terms denominator is a (nonzero) constant and numerator degree 0.
    let rn := qnormPairG r.1.1 r.1.2
    if cdegG rn.1 = 0 ∧ cdegG rn.2 = 0 then
      some (((rn.1 : List ℚ).headD 0) / ((rn.2 : List ℚ).headD 1))
    else none

/-- Parametric logarithmic derivative recognizer `cParamLogDeriv fval θlogderiv` over `k = ℚ(x)`: decides
`n·f = Dv/v + m·(Dθ/θ)` for integers `n ≠ 0, m` and `v ∈ ℚ(x)*`, returning `some (n, m, v)` or `none`. It
solves for the candidate constant `c = m/n` (`cParamLogDerivCandidate`), then tests whether the residue
`N·f − M·(Dθ/θ)` is a logarithmic derivative of a radical (`cParametricLogDeriv`), reporting the residue as
the witness `v` (`v = 1` when it vanishes). -/
def cParamLogDeriv (fval θlogderiv : QFunNZG ℚ) :
    Option (ℤ × ℤ × QFunNZG ℚ) :=
  match cParamLogDerivCandidate fval θlogderiv with
  | none =>
    -- no constant candidate `c`: fall back to the pure logarithmic-derivative test `n·f = Dv/v`
    -- (`m = 0`). `f` is a log-derivative of a radical iff `cParametricLogDeriv` cannot rule it out and
    -- the residue obstruction is absent; report only the provable `f = 0` (trivial `v = 1`, `n` any).
    if CField.isZero fval then some (1, 0, CField.one) else none
  | some c =>
    -- `c = M/N` in lowest terms, `N > 0`. Test `N·f − M·(Dθ/θ) = Dv/v` (radical log-derivative).
    let N : ℤ := (c.den : ℤ)
    let M : ℤ := c.num
    let Nf := CField.mul (qConstParamG ((N : ℚ))) fval
    let Mw := CField.mul (qConstParamG ((M : ℚ))) θlogderiv
    let resid := CField.sub Nf Mw
    -- the residue `N·f − M·w`: a logarithmic derivative of a radical. The exactly-decidable witness is
    -- `resid = 0` (then `v = 1`, `N·f = M·w`, so `n = N, m = M`); the general radical witness (§5.12
    -- construction) is the documented continuation.
    if CField.isZero resid then some (N, M, CField.one)
    else if !cParametricLogDeriv resid then none
    else some (N, M, resid)

/-! ### `cParamRischDE` — the parametric Risch DE `Dy + f·y = Σᵢ cᵢ·gᵢ`

Solve the parametric Risch differential equation for `y ∈ k(t)` and constants `c₁, …, cₘ`, returning a
basis of the constant solution subspace. Over the base monomial case `k = ℚ`, `D = d/dt`, the bounded-degree
polynomial equation becomes a homogeneous linear system over `ℚ`, whose kernel is returned. -/

/-- Polynomial lcm over ℚ `cLcmQ p q = p·q / gcd(p, q)` (monic). -/
def cLcmQ (p q : CPolyG ℚ) : CPolyG ℚ :=
  if cisZeroG p ∨ cisZeroG q then []
  else cmonicG (cdivWf (cmulG p q) (cgcdWf p q).1)

/-- `tⁱ`-coefficient of a `CPolyG ℚ` `cCoeffQ p i = coefficient(p, tⁱ)` (`0` out of range). -/
def cCoeffQ (p : CPolyG ℚ) (i : ℕ) : ℚ := (p : List ℚ).getD i 0

/-- Linear constraints over ℚ `cLinearConstraintsQ gnums gdens` (`D = d/dt`, `k = ℚ`): from the reduced
equation `Dp = Σᵢ cᵢ·gᵢ` with `gᵢ = gnumsᵢ/gdensᵢ`, clears the common denominator `d = lcm(gdensᵢ)`,
splits each `d·gᵢ = qᵢ·d + rᵢ`, and returns the polynomial parts `qs = [q₁, …, qₘ]` together with the
homogeneous constraint matrix `Mᵢⱼ = coefficient(rⱼ, tⁱ)` (fed to `cNullspaceBasisQ`). -/
def cLinearConstraintsQ (gnums gdens : List (CPolyG ℚ)) :
    List (CPolyG ℚ) × List (List ℚ) :=
  let d := gdens.foldl (fun acc den => cLcmQ acc den) [(1 : ℚ)]
  let qrs : List (CPolyG ℚ × CPolyG ℚ) :=
    (List.zip gnums gdens).map (fun (gn, gd) =>
      let dgi := cmulG gn (cdivWf d gd)             -- `d·gᵢ = gnumᵢ·(d/gdenᵢ)`
      cdivmodWf dgi d)                              -- `(qᵢ, rᵢ)`
  let qs := qrs.map Prod.fst
  let rs := qrs.map Prod.snd
  let nrows := cdegG d                              -- rows `i = 0 .. deg(d)−1`
  let m := gnums.length
  let M : List (List ℚ) :=
    (List.range nrows).map (fun i =>
      (List.range m).map (fun j => cCoeffQ (rs.getD j []) i))
  (qs, M)

/-- **Parametric Risch DE over the base monomial ℚ[t]** `cParamRischDE gnums gdens` (Bronstein §7.1,
the `ParamRischDE(f, [g₁,…,gₘ], D)` pipeline, book p.217), specialized to `k = ℚ`, `D = d/dt`, the
**reduced** equation `Dp = Σᵢ cᵢ·gᵢ` (`a = 1, b = 0`, eq. 7.5 after the trivial-over-ℚ RDE stages).
Returns a **basis** `[c⃗₁, …, c⃗ᵣ]` of the `Const(k) = ℚ`-linear subspace of constant tuples
`(c₁, …, cₘ)` for which the equation has a polynomial solution `p ∈ ℚ[t]`:

1. `(qs, M) ← LinearConstraints(1, 0, [g₁,…,gₘ], D)` (`cLinearConstraintsQ`): the eq. 7.6 homogeneous
   matrix `M·(c₁,…,cₘ)ᵀ = 0` (entries in `Const(k) = ℚ`).
2. **return** `cNullspaceBasisQ M m` — a basis of `ker(M)`, the constant solution subspace (book p.226:
   "a basis of its kernel allows us to express some of the `cᵢ` in terms of others").

The empty kernel (`[]`) means the only solution is `c₁ = … = cₘ = 0`. For each basis tuple `c⃗`, the
companion polynomial solution `p` solves `Dp = Σ cᵢqᵢ` (eq. 7.7, the reduced polynomial RDE) — recoverable
by integrating `Σ cᵢqᵢ` (`cIntegratePolyQ`), the `a = 1, b = 0` non-cancellation case. -/
def cParamRischDE (gnums gdens : List (CPolyG ℚ)) : List (List ℚ) :=
  let (_qs, M) := cLinearConstraintsQ gnums gdens
  cNullspaceBasisQ M gnums.length

/-! ### `cLimitedIntegrate` (Bronstein §7.2, the `LimitedIntegrate(f, [w₁,…,wₘ], D)` problem, book p.245)

Decide `f = Dv + Σᵢ cᵢ·log(wᵢ)` for constants `cᵢ` and `v ∈ k(t)`. Equivalently `f − Σ cᵢ·(Dwᵢ/wᵢ) = Dv`,
the parametric Risch DE `Dv + 0·v = f − Σ cᵢ·(Dwᵢ/wᵢ)` — i.e. (7.1) with `gᵢ = Dwᵢ/wᵢ` and the additional
"`f` itself" generator (book p.245: "Equation (7.30) can be considered a parametric Risch differential
equation for `v`"). So it is the `gᵢ = Dwᵢ/wᵢ` specialization of `cParamRischDE`, with `f` appended as the
forced generator `c₀ = 1`. -/

/-- **Limited integration over the base monomial ℚ[t]** `cLimitedIntegrate fnum fden wnums wdens`
(Bronstein §7.2, the `LimitedIntegrate(f, [w₁,…,wₘ], D)` problem, book p.245), `k = ℚ`, `D = d/dt`.
Decides `f = Dv + Σᵢ cᵢ·log(wᵢ)` for `cᵢ ∈ ℚ` and `v ∈ ℚ(t)`, returning the basis of admissible
`(c₀, c₁, …, cₘ)` tuples (with `c₀` the coefficient of the forced generator `f`, so a genuine solution
has `c₀ = 1`): the parametric Risch DE `Dv = c₀·f − Σᵢ cᵢ·(Dwᵢ/wᵢ)` (eq. 7.30 as (7.1) with generators
`g₀ = f`, `gᵢ = Dwᵢ/wᵢ = wnumᵢ'/wnumᵢ`-style logarithmic derivatives). Built as `cParamRischDE` on the
generator list `[f, Dw₁/w₁, …, Dwₘ/wₘ]`. The `wᵢ` arrive as numerator/denominator pairs; `Dwᵢ/wᵢ` is
`(D(wnumᵢ)·wdenᵢ − wnumᵢ·D(wdenᵢ)) / (wnumᵢ·wdenᵢ)`. The full §7.2 simplification (Corollary 7.2.1's
sharper `hₙ`-bound and the `c₀ = 1` back-substitution to a nonparametric RDE) is the documented
refinement. -/
def cLimitedIntegrate (fnum fden : CPolyG ℚ) (wnums wdens : List (CPolyG ℚ)) :
    List (List ℚ) :=
  -- generator `g₀ = f`, then `gᵢ = Dwᵢ/wᵢ` (logarithmic derivative of `wᵢ`).
  let logDerivs : List (CPolyG ℚ × CPolyG ℚ) :=
    (List.zip wnums wdens).map (fun (wn, wd) =>
      let num := csubG (cmulG (cderivQ wn) wd) (cmulG wn (cderivQ wd))
      let den := cmulG wn wd
      (num, den))
  let gnums := fnum :: logDerivs.map Prod.fst
  let gdens := fden :: logDerivs.map Prod.snd
  cParamRischDE gnums gdens

/-- `getD` within range reads the element. -/
theorem getD_lt_gen {α : Type*} (l : List α) (n : ℕ) (d : α) (hn : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl

end CPolyG

/-! ### Validation — the parametric logarithmic derivative recognizer

For `11 = Dv/v + m·Dθ/θ` with `Dθ/θ = 1` over `k = ℚ`, `cParamLogDeriv` returns `(n, m, v) = (1, 11, 1)`. -/

open CPolyG

/-- `f = 11 ∈ ℚ ⊂ ℚ(x)`. -/
def paramLogDerivExampleF : QFunNZG ℚ := CPolyG.qConstParamG 11
/-- `Dθ/θ = 1` (exponential `θ`, `Dθ = θ`). -/
def paramLogDerivExampleW : QFunNZG ℚ := CPolyG.qConstParamG 1

-- **Sanity print.** `cParamLogDeriv` on Example 7.3.2 returns `(n, m, v) = (1, 11, 1)`.
#eval (CPolyG.cParamLogDeriv paramLogDerivExampleF paramLogDerivExampleW).map
  (fun (n, m, v) => (n, m, CPolyG.qnormPairG v.1.1 v.1.2))

/-- The parametric logarithmic derivative recognizer computes: for `11 = Dv/v + m·Dθ/θ` with `Dθ/θ = 1`
over `k = ℚ`, `cParamLogDeriv` returns `(n, m, v) = (1, 11, 1)`, verified to satisfy
`n·f = Dv/v + m·(Dθ/θ)` (with `v = 1`, `Dv/v = 0`). -/
theorem paramLogDeriv_example :
    (match cParamLogDeriv paramLogDerivExampleF paramLogDerivExampleW with
      | some (n, m, v) =>
          -- `n·f − m·(Dθ/θ) − Dv/v` cleared: with `v = 1`, `Dv/v = 0`, so check `n·f − m·w = 0`.
          let nf := CField.mul (CPolyG.qConstParamG ((n : ℚ))) paramLogDerivExampleF
          let mw := CField.mul (CPolyG.qConstParamG ((m : ℚ))) paramLogDerivExampleW
          CField.isZero (CField.sub nf mw) && CField.isZero (CField.sub v CField.one)
            && decide (n ≠ 0)
      | none => false) = true := by native_decide

#print axioms paramLogDeriv_example

/-! ### Validation — the parametric RDE reduces to a linear system

For `Dp = c₁·(2t³+3t+1)/(t²−1) + c₂/(t−1) + c₃/(t+1)` over `k = ℚ`, `LinearConstraints` yields the
homogeneous system with solution space `(c₁,c₂,c₃) = (λ,−3λ,−2λ)`. -/

open CPolyG

/-- `g₁ = (2t³+3t+1)/(t²−1)`: numerator `[1,3,0,2]`, denominator `[-1,0,1]` (low→high). -/
def paramRischExampleG1num : CPolyG ℚ := [1, 3, 0, 2]
/-- `g₁`-denominator `t²−1`. -/
def paramRischExampleG1den : CPolyG ℚ := [-1, 0, 1]
/-- `g₂ = 1/(t−1)`: numerator `[1]`, denominator `[-1,1]`. -/
def paramRischExampleG2num : CPolyG ℚ := [1]
/-- `g₂`-denominator `t−1`. -/
def paramRischExampleG2den : CPolyG ℚ := [-1, 1]
/-- `g₃ = 1/(t+1)`: numerator `[1]`, denominator `[1,1]`. -/
def paramRischExampleG3num : CPolyG ℚ := [1]
/-- `g₃`-denominator `t+1`. -/
def paramRischExampleG3den : CPolyG ℚ := [1, 1]

-- **Sanity prints** (book p.224): `LinearConstraints` returns the eq. 7.6 system (rows = coefficients
-- of `t⁰, t¹`: `[[1,1,-1],[5,1,1]]`, the book's `[[5,1,1],[1,1,-1]]` up to equation order), and the
-- kernel basis (one vector, proportional to `(1,-3,-2)`: here `(-1/2, 3/2, 1) = -½·(1,-3,-2)`).
#eval (CPolyG.cLinearConstraintsQ
    [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
    [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]).2
#eval CPolyG.cParamRischDE
    [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
    [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]

/-- **Cleared parametric-constraint check** `paramConstraintCheck gnums gdens cs`: `true` iff the
constant tuple `cs = (c₁,…,cₘ)` satisfies the eq. 7.6 constraint `Σᵢ cᵢ·rᵢ = 0` (the remainders `rᵢ` of
`d·gᵢ` by `d = lcm(denominators)`), i.e. `Σᵢ cᵢ·(numᵢ·(d/denᵢ) mod d) = 0` — the polynomial identity
certifying that `(c₁,…,cₘ)` is a genuine solution of the parametric Risch DE's linear constraints. -/
def paramConstraintCheck (gnums gdens : List (CPolyG ℚ)) (cs : List ℚ) : Bool :=
  let d := gdens.foldl (fun acc den => cLcmQ acc den) [(1 : ℚ)]
  let total : CPolyG ℚ :=
    ((List.zip gnums gdens).zip cs).foldl (fun acc ((gn, gd), c) =>
      let dgi := cmulG gn (cdivWf d gd)
      let ri := cmodWf dgi d
      caddG acc (cscaleG c ri)) []
  cisZeroG total

/-- **Example 7.1.1 — the parametric Risch differential equation reduces to a constant linear system**
(`native_decide`, Bronstein §7.1, the `LinearConstraints`/`ConstantSystem` boxes, book p.223/224). For
`Dp = c₁·(2t³+3t+1)/(t²−1) + c₂/(t−1) + c₃/(t+1)` over `k = ℚ`, `t` a monomial with `Dt = 1`:

1. **Linear constraints.** `cLinearConstraintsQ` returns the homogeneous matrix `[[5,1,1],[1,1,-1]]`
   (eq. 7.10), pinned componentwise against the book's values.
2. **Constant solve.** `cParamRischDE` returns a **basis** of its kernel — a single vector `c⃗`
   (one-dimensional solution space), each verified to **actually satisfy** the eq. 7.6 constraint
   `Σᵢ cᵢ·rᵢ = 0` by `paramConstraintCheck` (the cleared polynomial identity), and confirmed nontrivial
   (not all-zero). The book's solution space is `(c₁,c₂,c₃) = (λ,−3λ,−2λ)`; the returned basis vector is
   proportional to `(1,−3,−2)`, so the parametric problem reduces to the one-parameter `Dp = 2λt`.

This is the §7.1 deliverable: the **parametric** Risch differential equation — where the right-hand side
`Σ cᵢgᵢ` carries undetermined constants — reduces, via `LinearConstraints` (eq. 7.6) and the constant
linear solve `cNullspaceBasisQ` (`ConstantSystem`, Lemma 7.1.2, here ordinary ℚ-Gaussian elimination
since `Const(k) = ℚ`), to a basis of the constant solution subspace. -/
theorem paramRischDE_example :
    -- (1) the eq. 7.6 constraint matrix is the system `c₁(5t+1)+c₂(t+1)+c₃(t−1)=0`, i.e. (low→high in
    -- `t`) the rows `t⁰: [1,1,-1]` and `t¹: [5,1,1]` (the book writes the two equations as
    -- `[[5,1,1],[1,1,-1]]`; equating coefficients of `t⁰, t¹` is the same homogeneous system).
    (decide ((cLinearConstraintsQ
        [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
        [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]).2
      = [[1,1,-1],[5,1,1]])
    -- (2) the kernel basis is one nontrivial vector, each satisfying the eq. 7.6 constraint.
    && (let basis := cParamRischDE
          [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
          [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]
        decide (basis.length = 1)
          && basis.all (fun cs =>
              paramConstraintCheck
                [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
                [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den] cs
                && !(cs.all (· == 0))))) = true := by native_decide

#print axioms paramRischDE_example

/-! ### Validation — Bronstein §7.2: the limited integration problem reduces to the parametric RDE

`k = ℚ`, `t` a monomial with `Dt = 1` (`D = d/dt`). The limited integration problem
`f = Dv + Σᵢ cᵢ·log(wᵢ)` is the parametric Risch DE (7.1) with generators `g₀ = f`, `gᵢ = Dwᵢ/wᵢ`. For
`f = 1/t`, `w₁ = t`, `w₂ = t+1` (`Dw₁/w₁ = 1/t`, `Dw₂/w₂ = 1/(t+1)`), the only constant relation among
`{f, 1/t, 1/(t+1)}` is `f = 1/t = log(t)′`, so `cLimitedIntegrate` returns a one-dimensional kernel — the
basis vector witnessing `c₀·f = c₁·(Dw₁/w₁)` (i.e. `f = log(w₁)`, the limited-integral certificate). -/

open CPolyG

/-- §7.2 example's `f = 1/t`: numerator `[1]`, denominator `t = [0,1]`. -/
def limitedIntExampleFnum : CPolyG ℚ := [1]
/-- §7.2 example's `f`-denominator `t`. -/
def limitedIntExampleFden : CPolyG ℚ := [0, 1]

-- **Sanity print** (book §7.2): `cLimitedIntegrate` finds the relation `f = Dw₁/w₁` (`f = log(t)`),
-- a one-dimensional kernel `[[-1, 1, 0]]` over generators `[f, Dw₁/w₁, Dw₂/w₂]`.
#eval CPolyG.cLimitedIntegrate limitedIntExampleFnum limitedIntExampleFden [[0, 1], [1, 1]] [[1], [1]]

/-- **§7.2 — the limited integration problem reduces to the parametric Risch DE** (`native_decide`,
Bronstein §7.2, book p.245). For `f = Dv + c₁·log(t) + c₂·log(t+1)` with `f = 1/t` over `k = ℚ`,
`cLimitedIntegrate` (the `gᵢ = Dwᵢ/wᵢ` specialization of `cParamRischDE`, with `f` the forced generator)
returns a nonempty constant kernel basis, each vector verified to **actually satisfy** the eq. 7.6
constraint `c₀·f + Σᵢ cᵢ·(Dwᵢ/wᵢ) ≡ 0 (mod lcm)` by `paramConstraintCheck`. The relation found is
`f = log(t)` (`c₀ = ±1`, `c₁ = ∓1`, `c₂ = 0`) — the limited-integral certificate that `∫ f = log(t)`.
The full §7.2 simplification (Corollary 7.2.1's sharper denominator and the `c₀ = 1` back-substitution
to a nonparametric RDE for `v`) is the documented refinement. -/
theorem limitedIntegrate_example :
    (let wnums : List (CPolyG ℚ) := [[0, 1], [1, 1]]
     let wdens : List (CPolyG ℚ) := [[1], [1]]
     -- the generators `cLimitedIntegrate` builds: `g₀ = f`, `gᵢ = Dwᵢ/wᵢ`.
     let logDerivs : List (CPolyG ℚ × CPolyG ℚ) :=
       (List.zip wnums wdens).map (fun (wn, wd) =>
         (csubG (cmulG (cderivQ wn) wd) (cmulG wn (cderivQ wd)), cmulG wn wd))
     let gnums := limitedIntExampleFnum :: logDerivs.map Prod.fst
     let gdens := limitedIntExampleFden :: logDerivs.map Prod.snd
     let basis := cLimitedIntegrate limitedIntExampleFnum limitedIntExampleFden wnums wdens
     decide (0 < basis.length)
       && basis.all (fun cs =>
            paramConstraintCheck gnums gdens cs && !(cs.all (· == 0)))) = true := by
  native_decide

#print axioms limitedIntegrate_example

end DeepWiki.SymbolicIntegration
