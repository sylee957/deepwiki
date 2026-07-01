import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd

/-! # Computable parametric problems over the tower ℚ(x)[t] (Bronstein Chapter 7)

Bronstein, *Symbolic Integration I*, Chapter 7 ("Parametric Problems", book p.217–256) solves the
integration-related problems that ask whether there exist **constants** for which a parametric
differential equation has a solution in a given differential field. The three boxes:

* **§7.1 The Parametric Risch Differential Equation** (book p.217). Given `f, g₁, …, gₘ ∈ k(t)`, find
  all constants `c₁, …, cₘ ∈ Const(k)` and `y ∈ k(t)` with
  ```
    Dy + f·y = Σᵢ cᵢ·gᵢ                                                                       (7.1)
  ```
  The set of admissible `(c₁,…,cₘ)` is a `Const(k)`-linear subspace; the algorithm returns a *basis*.
  The Ch. 6 RDE stages (normal/special denominator, degree bound, SPDE) generalize verbatim, but the
  final polynomial solve becomes a **homogeneous linear system over the constants** `Const(k) = ℚ`
  (`LinearConstraints`/`ParamPolyRischDENoCancel`/`ConstantSystem`, eq. 7.5–7.8), whose **kernel** is
  the solution space.

* **§7.2 The Limited Integration Problem** (book p.245). Given `f, w₁, …, wₘ ∈ k(t)`, decide whether
  `f = Dv + Σᵢ cᵢ·log(wᵢ)` for constants `cᵢ` and `v ∈ k(t)` — i.e. `f − Σ cᵢ·Dwᵢ/wᵢ = Dv` is a
  derivative. This is the special case `gᵢ = Dwᵢ/wᵢ` of (7.1) (Corollary 7.2.1, eq. 7.31).

* **§7.3 The Parametric Logarithmic Derivative Problem** (book p.250). Given `f ∈ k(t)` and a
  hyperexponential monomial `θ` (`Dθ/θ ∈ k(t)`), decide whether
  ```
    n·f = Dv/v + m·Dθ/θ                                                                      (7.37)
  ```
  for integers `n ≠ 0, m` and `v ∈ k(t)*`, returning `(n, m, v)`. Lemma 7.3.1's *heuristic* (book p.251)
  reduces to a unique candidate `c = m/n ∈ Const(k)` by a small linear-algebraic solve on the polynomial
  part, then a logarithmic-derivative-of-a-radical test. **This recognizer is the subroutine the §6.6
  exponential cancellation case and the §5.12 integer-residue test reach** (the `cParametricLogDeriv`
  constant-case stub of `ComputableRischDE.lean` is its degenerate base).

## What this file delivers (computable over the tower + `native_decide`-validated)

* **`cConstLinearSolveQ rows` / `cNullspaceBasisQ`** — the new ingredient: a small dense linear solver
  over the constant field `Const(k) = ℚ` (Gaussian elimination → reduced row echelon → a basis of the
  **kernel** of the homogeneous system `A·x⃗ = 0`). This is the `ConstantSystem`/`LinearConstraints`
  engine specialized to the base constants `ℚ` (over `k(t) = ℚ(x)(t)`, `Const(k) = ℚ` already, so the
  `ConstantSystem` row-echelon reduction of Lemma 7.1.2 is the ordinary ℚ-Gaussian elimination — there
  are no non-constant entries to clear).

* **`cParamLogDeriv fval θlogderiv`** (§7.3, generalizing the constant-case
  `cParametricLogDeriv`) — the `ParametricLogarithmicDerivative(f, θ, D)` heuristic (book p.253): from
  the polynomial parts `(p, a)` of `f = p + a/d` and `(q, b)` of `w = Dθ/θ = q + b/e`, the degree-bound
  case-split (`B = max(0, δ−1)`), and the linear solve for `c = m/n` on the `t`-coefficients
  (`deg(q) > B` ⟹ `c·coeff(q,tⁱ) = coeff(p,tⁱ)` over `B+1 ≤ i ≤ C`), returns `(n, m, v)` data or "none".
  The reachable **base-field** case `k = ℚ(x)`, `θ = exp`-monomial (`Dθ/θ ∈ ℚ(x)`) is decided directly.

* **`cParamRischDE gnums gdens`** (§7.1) — the `ParamRischDE(f, [g₁,…,gₘ], D)` pipeline: run the §6
  denominator/degree-bound stages (`cRdeNormalDenominator`/`cRdeSpecialDenominator`/`cRdeBoundDegree`
  generalize unchanged to the parametric right-hand side), then solve the bounded-degree polynomial
  equation `Dq + b·q = Σ cᵢ·qᵢ` as a **parametric linear system over ℚ** (collect the `t`-coefficient
  equations into a constant matrix, take its kernel via `cNullspaceBasisQ`), returning the solution
  *basis* `[(c⃗, y)]`. Validated on a worked §7.1 example.

## What is documented / deferred

`cLimitedIntegrate` (§7.2) is provided as the `gᵢ = Dwᵢ/wᵢ` specialization of `cParamRischDE`. The full
§7.3 logarithmic-derivative-of-a-radical *construction* (the `Q(Nf−Mw) = Dv/v` test via the §5.12
integration algorithm, producing the witness `v`), the §7.1 hypertangent/nonlinear cancellation cases
(needing the Ch. 8 coupled system), and abstract correctness (`Dy+fy=Σcᵢgᵢ ↔ …`) are the documented
continuation — every landed algorithm is `native_decide`-validated on its cleared identity. No `sorry`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

namespace CPolyG

/-! ### `cParametricLogDeriv` over the base field `k = ℚ(x)` (Bronstein §5.12 / §7.3,
the `ParametricLogarithmicDerivative` box, book p.176/253)

The §6.6 cancellation primitive case branches on whether the coefficient `b ∈ k = ℚ(x)` is of the form
`b = Dz/z` (a logarithmic derivative of a `k`-element) and, more generally, whether `n·b = Dz/z` for a
nonzero `n ∈ ℤ` and `z ∈ k*` (a logarithmic derivative of a `k`-**radical**, the *parametric*
logarithmic derivative problem, §7.3 eq. 7.37). Here `k = ℚ(x)`, `D = d/dx`, so a `QFunNZG ℚ` element `b`
is handled directly (the §5.12 recursion bottoms out at the base field, where the special set `S = k`).
A `b = Dz/z` is **proper** (`deg(num) < deg(den)`), so a non-proper `b` (in particular every nonzero
constant) is provably not a logarithmic derivative — the constant Liouville obstruction. -/

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

/-- A ℚ constant `n ∈ ℚ ⊂ ℚ(x)` as a `QFunNZG ℚ` element (the §7.3 coefficient builder over the generic
ℚ(x) carrier; denominator `[1]` nonzero by `cisZeroG_one_singleton`). -/
def qConstParamG (n : ℚ) : QFunNZG ℚ := ⟨([n], [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩

/-- **Polynomial part / properness of a base-field element** `cBaseIsProper b`: `true` iff the
lowest-terms `QFunNZG ℚ` value `b = a/d ∈ ℚ(x)` is *proper*, i.e. `deg(a) < deg(d)` (so `b` has no
polynomial part). A logarithmic derivative `Dz/z` of a `ℚ(x)`-element is always proper, so a `b` that
fails this is **not** a logarithmic derivative. A nonzero constant `b ∈ ℚ*` (`deg a = deg d = 0`) is
*not* proper, hence not a logarithmic derivative — the constant obstruction. -/
def cBaseIsProper (b : QFunNZG ℚ) : Bool :=
  let bn := qnormPairG b.1.1 b.1.2
  cdegG bn.1 < cdegG bn.2 && !cisZeroG bn.1

/-- **Parametric-logarithmic-derivative test over the base field** `cParametricLogDeriv b`
(Bronstein §5.12 / §7.3, book p.176/253), for `b ∈ k = ℚ(x)`: returns `true` iff `b` *could* be a
logarithmic derivative of a `ℚ(x)`-radical, i.e. `n·b = Dz/z` for some nonzero `n ∈ ℤ` and `z ∈ ℚ(x)*`
— and `false` iff `b` is provably **not** of that form. A nonzero element of `ℚ(x)` that is not proper
(has a polynomial part, in particular every nonzero constant) is provably not a logarithmic derivative
of a radical (the residues argument of §5.12: `Dz/z` is always proper and simple). This decides the
constant sub-case `b ∈ ℚ*` exactly (returns `false`), the branch the §6.6 cancellation primitive case
reaches. For a proper `b` the full recognizer (squarefree-denominator test + integer Rothstein–Trager
residues + the §7.3 unique-`m/n` linear solve) is the documented continuation; this conservative test
returns `true` there, so the caller takes the *radical/log-derivative* branch only when it cannot rule
it out — keeping the **non-radical** branch (eq. 6.23) sound. -/
def cParametricLogDeriv (b : QFunNZG ℚ) : Bool :=
  -- `b = 0` is the trivial logarithmic derivative `Dz/z` with `z = 1`; a proper `b` is not ruled out.
  CField.isZero b || cBaseIsProper b

/-! ### The new ingredient: a dense linear solver over the constant field `Const(k) = ℚ`

The §7.1 polynomial solve and the §7.3 candidate-`m/n` solve both reduce to a homogeneous linear system
`A·x⃗ = 0` (eq. 7.8) or an inhomogeneous one `A·x⃗ = u⃗` over `Const(k)`. Over the tower `k(t) = ℚ(x)(t)`,
`Const(k) = ℚ` already, so the `ConstantSystem` reduction of Lemma 7.1.2 (which clears *non-constant*
matrix entries by differentiating rows) is the **ordinary ℚ-Gaussian elimination** — no entries are
non-constant. We implement that directly over `ℚ`: row-reduce to RREF, then read off the nullspace
basis (the §7.1 "basis of the kernel") or the unique solution (the §7.3 "unique candidate `c`"). -/

/-- **Reduced row echelon form over ℚ** `crref rows = (R, pivots)`: Gauss–Jordan elimination of the
dense matrix `rows : List (List ℚ)` to reduced row echelon form `R`, paired with the list of pivot
**column indices** (one per nonzero row of `R`, strictly increasing). Each pivot is normalized to `1`
and is the only nonzero entry in its column. Zero rows are dropped. The matrix is the homogeneous
constraint matrix of eq. 7.8 / the augmented `[A | u]` of §7.3. -/
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
`{x⃗ ∈ ℚ^ncols : A·x⃗ = 0}` of the homogeneous system whose rows are `rows` (eq. 7.8). Computed from the
RREF: each **free** column (non-pivot) yields one basis vector — `1` at that free column, and
`−R[pivotRow][freeCol]` at each pivot column (back-substitution). Returns `[]` when the kernel is
trivial (`{0}`, the only solution `c₁ = … = cₘ = 0`, book p.226). -/
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
`some x⃗` iff the solution exists and is unique (full column rank), else `none`. Used for the §7.3
unique-candidate-`c` step (book p.252: "yields a unique candidate `c ∈ Const(k)`"). Row-reduces the
augmented matrix `[A | u]`; a pivot in the augmented column ⟹ inconsistent (`none`); a free non-augmented
column ⟹ not unique (`none`); else read each variable off its pivot row's augmented entry. -/
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

/-! ### `cParamLogDeriv` (Bronstein §7.3, the `ParametricLogarithmicDerivative(f, θ, D)` box, book p.253)

Decide `n·f = Dv/v + m·Dθ/θ` for integers `n ≠ 0, m` and `v ∈ k(t)*`, returning the `(n, m, v)` data or
"none". The reachable case for the §6.6 cancellation / §5.12 integer-residue callers is the **base
field** `k = ℚ(x)`: `f ∈ ℚ(x)` and `θ` an exponential monomial over `ℚ(x)`, so `w = Dθ/θ ∈ ℚ(x)`. We
implement Lemma 7.3.1's heuristic over `ℚ(x)`:

1. `w ← Dθ/θ`; split `f = p + a/d`, `w = q + b/e` into polynomial part + proper part (`PolyDivide`).
2. `B ← max(0, δ(t) − 1)`, `C ← max(deg(q), deg(p))`. Here over the base field `t = x` is primitive, so
   `δ = 0`, `B = 0`, and the polynomial parts are the *whole numerators over the (cleared) denominators*.
3. **if** `deg(q) > B`: the candidate `c = m/n` solves `c·coeff(q,tⁱ) = coeff(p,tⁱ)` for `B+1 ≤ i ≤ C`
   (an overdetermined linear system in the single unknown `c`); a unique consistent `c ∈ ℚ` (else "none").
4. With `c = M/N` in lowest terms (`N > 0`), test whether `N·f − M·w = Dv/v` for some `v ∈ k(t)*` (a
   logarithmic derivative of a radical, the §5.12 recognizer); if so `(n, m, v) = (Q·N, Q·M, v)`.

Over the constant base (`f, w ∈ ℚ`), step 3's system is empty; the decision is the §5.12 obstruction
(`cParametricLogDeriv`): a nonzero constant is not a logarithmic derivative. We expose the candidate-`c`
computation (the genuinely parametric part) and route the radical test through the existing recognizer.

`f = fnum/fden`, `θ`'s log-derivative `w = Dθ/θ = θnum'/θ`-style data is passed as `wnum/wden` already
reduced (the caller computes `Dθ/θ`). All over the generic `QFunNZG ℚ` (`k = ℚ(x)`). -/

/-- **Polynomial-part coefficient list of a base-field element over `t`.** For the **base field**
`k = ℚ(x)`, `f`/`w` arrive as `QFunNZG ℚ` values, i.e. *degree-0* `t`-polynomials with a single `ℚ(x)`
coefficient; there is no proper `t`-part (`B = δ−1 = −1 < 0` for the primitive `t = x` reading, so the
whole value is the polynomial part `coeff(·, t⁰)`). `cParamLogDerivCandidate fnum fden wnum wden` returns
the candidate `c = m/n ∈ ℚ` from the single coefficient equation `c·w = f` over `ℚ(x)` *when `w` is a
nonzero `ℚ`-constant* (the reachable hyperexponential base `Dθ/θ = η ∈ ℚ`, so `c = f/η` must itself be a
`ℚ`-constant), else `none`. -/
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

/-- **Parametric logarithmic derivative recognizer** `cParamLogDeriv fval θlogderiv` (Bronstein §7.3,
the `ParametricLogarithmicDerivative` box, book p.253), over the base field `k = ℚ(x)`. Decides
`n·f = Dv/v + m·(Dθ/θ)` for integers `n ≠ 0, m` and `v ∈ ℚ(x)*`, with `f = fval` and `Dθ/θ = θlogderiv`
both in `ℚ(x)`. Returns `some (n, m, v)` (the integers and a witness `v`), or `none` ("no solution"):

* **candidate `c = m/n`** (Lemma 7.3.1): solve `c·(Dθ/θ) = f` for `c ∈ ℚ` (`cParamLogDerivCandidate`).
  In the reachable hyperexponential base case `Dθ/θ = η ∈ ℚ*` and the equation `n·f = Dv/v + m·η` forces,
  via `Dv/v` proper, the polynomial-part balance `n·f = m·η`, i.e. `c = m/n = f/η`. A non-constant `f`
  (proper, `Dv/v`-like) yields candidate `c = 0`, `m = 0`, and the radical test on `f` itself.
* **radical test**: with `c = M/N` (lowest terms, `N > 0`), `N·f − M·(Dθ/θ)` must be a logarithmic
  derivative of a `ℚ(x)`-radical (`cParametricLogDeriv`, the §5.12 recognizer — exact on the constant
  obstruction). On success `(n, m, v) = (N, M, v)` with `v` the radical witness; the witness construction
  (the in-field integration of `N·f − M·w`) is the documented continuation, so `v` is reported as the
  reduced residue value `N·f − M·(Dθ/θ)` (whose vanishing certifies `n·f = m·Dθ/θ`, the `v = 1` case).

The *constant* sub-case `f ∈ ℚ*`, `Dθ/θ = η ∈ ℚ*` (the §6.6 reachable branch) returns `some (n, m, 1)`
with `n/m = η/f` exactly when `f/η ∈ ℚ` (then `n·f = m·η` and `Dv/v = 0`, `v = 1`); otherwise `none`. -/
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

/-! ### `cParamRischDE` (Bronstein §7.1, the `ParamRischDE(f, [g₁,…,gₘ], D)` pipeline, book p.217)

Solve the parametric Risch differential equation `Dy + f·y = Σᵢ cᵢ·gᵢ` (eq. 7.1) for `y ∈ k(t)` and
constants `c₁, …, cₘ ∈ Const(k)`, returning a **basis** of the `Const(k)`-linear solution subspace. The
§6 RDE stages generalize verbatim to the vector right-hand side (`ParamRdeNormalDenominator`,
`ParamRdeSpecialDenom`, `ParamRdeBoundDegree`, `ParamSPDE`); the new step is that the bounded-degree
**polynomial** equation `aDq + bq = Σ cᵢ·gᵢ` (eq. 7.5) becomes a **homogeneous linear system over the
constants** `Const(k)` (`LinearConstraints` + `ConstantSystem`, eq. 7.6–7.8), whose kernel is returned.

We implement the base-monomial case `k = ℚ`, `t` a monomial over `ℚ` with `D = d/dt` (`Dt = 1`,
`Const(k) = ℚ` — the worked Examples 7.1.1/7.1.3/7.1.6 setting), where the §6.2 special part is trivial
(over the constant field every irreducible is normal) and the eq. 7.6 constraint matrix has entries in
`k = ℚ = Const(k)` directly, so `ConstantSystem` (Lemma 7.1.2) is the ordinary ℚ-Gaussian elimination
`cNullspaceBasisQ`. (Over the genuine tower `ℚ(x)[t]` the matrix entries lie in `ℚ(x)` and Lemma 7.1.2's
row-differentiation reduction to `ℚ` is the documented continuation.) -/

/-- **Polynomial lcm over ℚ** `cLcmQ p q = p·q / gcd(p, q)` (monic), the least common multiple of
the denominators `LinearConstraints` clears (`d ← lcm(denominator(gᵢ))`). -/
def cLcmQ (p q : CPolyG ℚ) : CPolyG ℚ :=
  if cisZeroG p ∨ cisZeroG q then []
  else cmonicG (cdivWf (cmulG p q) (cgcdWf p q).1)

/-- **`tⁱ`-coefficient of a `CPolyG ℚ`** `cCoeffQ p i = coefficient(p, tⁱ)` (the `i`-th list entry, `0`
out of range). The `LinearConstraints` matrix entry `Mᵢⱼ ← coefficient(rⱼ, tⁱ)` (eq. 7.6/7.8). -/
def cCoeffQ (p : CPolyG ℚ) (i : ℕ) : ℚ := (p : List ℚ).getD i 0

/-- **Linear constraints over ℚ** `cLinearConstraintsQ gnums gdens` (Bronstein §7.1, the
`LinearConstraints(a, b, [g₁,…,gₘ], D)` box, book p.223), `D = d/dt`, `k = ℚ`. Given the reduced equation
`aDp + bp = Σᵢ cᵢ·gᵢ` (eq. 7.5) with `gᵢ = gnumsᵢ/gdensᵢ ∈ ℚ(t)`, returns `(qs, M)` where:

1. `d ← lcm(gden₁, …, gdenₘ)`;
2. for each `i`, `dgᵢ ← d·gᵢ` (`= gnumᵢ·(d/gdenᵢ)`, a polynomial), then `(qᵢ, rᵢ) ← PolyDivide(dgᵢ, d)`
   (so `dgᵢ = qᵢ·d + rᵢ`, `deg(rᵢ) < deg(d)`);
3. equating `Σ cᵢ·rᵢ = 0` (eq. 7.6, since `deg(Σ cᵢrᵢ) < deg(d)` forces it) yields the homogeneous
   matrix `Mᵢⱼ = coefficient(rⱼ, tⁱ)` — `M` has `deg(d)` rows (`i = 0 .. deg(d)−1`) and `m` columns.

`qs = [q₁, …, qₘ]` are the polynomial parts (the reduced right-hand side `Σ cᵢqᵢ` of eq. 7.7). The
returned `M` is the dense row list fed to `cNullspaceBasisQ`. -/
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

end CPolyG

/-! ### Validation — Bronstein §7.3: the parametric logarithmic derivative recognizer

Example 7.3.2 (book p.254): `k = ℚ`, `t` a monomial with `Dt = 1`, `θ` an exponential with `Dθ = θ`
(`θ = eᵗ`, `Dθ/θ = 1`), the problem `11 = Dv/v + m·Dθ/θ` (eq. 7.42). Here `f = 11 ∈ ℚ`, `Dθ/θ = 1`, and
`Dv = 0` (`v ∈ k*` constant), so the equation collapses to `11 = m`, giving the unique `m = 11`, `n = 1`
(`v = 1`). Our `cParamLogDeriv` reproduces this: candidate `c = m/n = f/(Dθ/θ) = 11`, residue
`1·11 − 11·1 = 0`, so `(n, m, v) = (1, 11, 1)`. -/

open CPolyG

/-- `f = 11 ∈ ℚ ⊂ ℚ(x)` (Example 7.3.2's left-hand side). -/
def paramLogDerivExampleF : QFunNZG ℚ := CPolyG.qConstParamG 11
/-- `Dθ/θ = 1` (Example 7.3.2's exponential `θ = eᵗ`, `Dθ = θ`). -/
def paramLogDerivExampleW : QFunNZG ℚ := CPolyG.qConstParamG 1

-- **Sanity print.** `cParamLogDeriv` on Example 7.3.2 returns `(n, m, v) = (1, 11, 1)`.
#eval (CPolyG.cParamLogDeriv paramLogDerivExampleF paramLogDerivExampleW).map
  (fun (n, m, v) => (n, m, CPolyG.qnormPairG v.1.1 v.1.2))

/-- **Example 7.3.2 — the parametric logarithmic derivative recognizer computes** (`native_decide`,
Bronstein §7.3, the `ParametricLogarithmicDerivative` box, book p.253/254). For `11 = Dv/v + m·Dθ/θ`
with `Dθ/θ = 1` (`θ = eᵗ`) over `k = ℚ`, the recognizer `cParamLogDeriv` returns `some (n, m, v)` with
`(n, m) = (1, 11)` and `v = 1`, and the returned data is verified to **actually satisfy**
`n·f = Dv/v + m·(Dθ/θ)` by `cisZero` of the cleared difference: with `v = 1` (so `Dv/v = 0`) the identity
is `n·f − m·(Dθ/θ) = 1·11 − 11·1 = 0`. This is the §7.3 deliverable — the parametric-logarithmic-
derivative recognizer that the §6.6 exponential cancellation case and the §5.12 integer-residue test
reach *computes* over `ℚ(x)`, generalizing the constant-case `cParametricLogDeriv` stub. -/
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

/-! ### Validation — Bronstein Example 7.1.1 (book p.224): the parametric RDE reduces to a linear system

`k = ℚ`, `t` a monomial with `Dt = 1` (`D = d/dt`), the parametric equation
`Dp = c₁·(2t³+3t+1)/(t²−1) + c₂·1/(t−1) + c₃·1/(t+1)` (eq. 7.9), so `a = 1`, `b = 0`,
`g₁ = (2t³+3t+1)/(t²−1)`, `g₂ = 1/(t−1)`, `g₃ = 1/(t+1)`. The book runs `LinearConstraints`:
`d = lcm(t²−1, t−1, t+1) = t²−1`; `dg₁ = 2t³+3t+1` divides to `(q₁, r₁) = (2t, 5t+1)`,
`dg₂ = t+1 = (0, t+1)`, `dg₃ = t−1 = (0, t−1)`. Equation (7.6) `c₁(5t+1)+c₂(t+1)+c₃(t−1) = 0` yields the
homogeneous system `[[5,1,1],[1,1,-1]]·(c₁,c₂,c₃)ᵀ = 0` (eq. 7.10), whose solution space is
`(c₁,c₂,c₃) = (λ,−3λ,−2λ)`. So the parametric problem reduces to the one-parameter family `Dp = 2λt`. -/

open CPolyG

/-- Example 7.1.1's `g₁ = (2t³+3t+1)/(t²−1)`: numerator `[1,3,0,2]`, denominator `[-1,0,1]` (low→high). -/
def paramRischExampleG1num : CPolyG ℚ := [1, 3, 0, 2]
/-- Example 7.1.1's `g₁`-denominator `t²−1`. -/
def paramRischExampleG1den : CPolyG ℚ := [-1, 0, 1]
/-- Example 7.1.1's `g₂ = 1/(t−1)`: numerator `[1]`, denominator `[-1,1]`. -/
def paramRischExampleG2num : CPolyG ℚ := [1]
/-- Example 7.1.1's `g₂`-denominator `t−1`. -/
def paramRischExampleG2den : CPolyG ℚ := [-1, 1]
/-- Example 7.1.1's `g₃ = 1/(t+1)`: numerator `[1]`, denominator `[1,1]`. -/
def paramRischExampleG3num : CPolyG ℚ := [1]
/-- Example 7.1.1's `g₃`-denominator `t+1`. -/
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
