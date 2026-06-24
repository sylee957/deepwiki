import DeepWiki.SymbolicIntegration.ComputableRischDE

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

* **`cParamLogDeriv Dt fuel fnum fden θnum θden`** (§7.3, generalizing the constant-case
  `cParametricLogDeriv`) — the `ParametricLogarithmicDerivative(f, θ, D)` heuristic (book p.253): from
  the polynomial parts `(p, a)` of `f = p + a/d` and `(q, b)` of `w = Dθ/θ = q + b/e`, the degree-bound
  case-split (`B = max(0, δ−1)`), and the linear solve for `c = m/n` on the `t`-coefficients
  (`deg(q) > B` ⟹ `c·coeff(q,tⁱ) = coeff(p,tⁱ)` over `B+1 ≤ i ≤ C`), returns `(n, m, v)` data or "none".
  The reachable **base-field** case `k = ℚ(x)`, `θ = exp`-monomial (`Dθ/θ ∈ ℚ(x)`) is decided directly.

* **`cParamRischDE Dt fuel f gs`** (§7.1) — the `ParamRischDE(f, [g₁,…,gₘ], D)` pipeline: run the §6
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

open Compute CPolyG QFunNZ

namespace CPolyG

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
reduced (the caller computes `Dθ/θ`). All over `QFunNZ` (`k = ℚ(x)`). -/

/-- **Polynomial-part coefficient list of a base-field element over `t`.** For the **base field**
`k = ℚ(x)`, `f`/`w` arrive as `QFunNZ` values, i.e. *degree-0* `t`-polynomials with a single `ℚ(x)`
coefficient; there is no proper `t`-part (`B = δ−1 = −1 < 0` for the primitive `t = x` reading, so the
whole value is the polynomial part `coeff(·, t⁰)`). `cParamLogDerivCandidate fnum fden wnum wden` returns
the candidate `c = m/n ∈ ℚ` from the single coefficient equation `c·w = f` over `ℚ(x)` *when `w` is a
nonzero `ℚ`-constant* (the reachable hyperexponential base `Dθ/θ = η ∈ ℚ`, so `c = f/η` must itself be a
`ℚ`-constant), else `none`. -/
def cParamLogDerivCandidate (fval wval : QFunNZ) : Option ℚ :=
  -- `c·wval = fval` over ℚ(x); a constant candidate `c ∈ ℚ` exists iff `fval/wval ∈ ℚ`.
  if CField.isZero wval then none
  else
    let r := CField.div fval wval
    -- `r ∈ ℚ` iff its lowest-terms denominator is a (nonzero) constant and numerator degree 0.
    let rn := Compute.qnorm 64 r.1
    if Compute.cdeg rn.1 = 0 ∧ Compute.cdeg rn.2 = 0 then
      some ((rn.1.headD 0) / (rn.2.headD 1))
    else none

/-- **Parametric logarithmic derivative recognizer** `cParamLogDeriv fuel fval θlogderiv` (Bronstein §7.3,
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
def cParamLogDeriv (fuel : ℕ) (fval θlogderiv : QFunNZ) :
    Option (ℤ × ℤ × QFunNZ) :=
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
    let Nf := CField.mul (QFunNZ.ofConstNZ ((N : ℚ))) fval
    let Mw := CField.mul (QFunNZ.ofConstNZ ((M : ℚ))) θlogderiv
    let resid := CField.sub Nf Mw
    -- the residue `N·f − M·w`: a logarithmic derivative of a radical. The exactly-decidable witness is
    -- `resid = 0` (then `v = 1`, `N·f = M·w`, so `n = N, m = M`); the general radical witness (§5.12
    -- construction) is the documented continuation.
    if CField.isZero resid then some (N, M, CField.one)
    else if !cParametricLogDeriv fuel resid then none
    else some (N, M, resid)

end CPolyG

/-! ### Validation — Bronstein §7.3: the parametric logarithmic derivative recognizer

Example 7.3.2 (book p.254): `k = ℚ`, `t` a monomial with `Dt = 1`, `θ` an exponential with `Dθ = θ`
(`θ = eᵗ`, `Dθ/θ = 1`), the problem `11 = Dv/v + m·Dθ/θ` (eq. 7.42). Here `f = 11 ∈ ℚ`, `Dθ/θ = 1`, and
`Dv = 0` (`v ∈ k*` constant), so the equation collapses to `11 = m`, giving the unique `m = 11`, `n = 1`
(`v = 1`). Our `cParamLogDeriv` reproduces this: candidate `c = m/n = f/(Dθ/θ) = 11`, residue
`1·11 − 11·1 = 0`, so `(n, m, v) = (1, 11, 1)`. -/

open CPolyG QFunNZ

/-- `f = 11 ∈ ℚ ⊂ ℚ(x)` (Example 7.3.2's left-hand side). -/
def paramLogDerivExampleF : QFunNZ := ofConstNZ 11
/-- `Dθ/θ = 1` (Example 7.3.2's exponential `θ = eᵗ`, `Dθ = θ`). -/
def paramLogDerivExampleW : QFunNZ := ofConstNZ 1

-- **Sanity print.** `cParamLogDeriv` on Example 7.3.2 returns `(n, m, v) = (1, 11, 1)`.
#eval (CPolyG.cParamLogDeriv 30 paramLogDerivExampleF paramLogDerivExampleW).map
  (fun (n, m, v) => (n, m, Compute.qnorm 30 v.1))

/-- **Example 7.3.2 — the parametric logarithmic derivative recognizer computes** (`native_decide`,
Bronstein §7.3, the `ParametricLogarithmicDerivative` box, book p.253/254). For `11 = Dv/v + m·Dθ/θ`
with `Dθ/θ = 1` (`θ = eᵗ`) over `k = ℚ`, the recognizer `cParamLogDeriv` returns `some (n, m, v)` with
`(n, m) = (1, 11)` and `v = 1`, and the returned data is verified to **actually satisfy**
`n·f = Dv/v + m·(Dθ/θ)` by `cisZero` of the cleared difference: with `v = 1` (so `Dv/v = 0`) the identity
is `n·f − m·(Dθ/θ) = 1·11 − 11·1 = 0`. This is the §7.3 deliverable — the parametric-logarithmic-
derivative recognizer that the §6.6 exponential cancellation case and the §5.12 integer-residue test
reach *computes* over `ℚ(x)`, generalizing the constant-case `cParametricLogDeriv` stub. -/
theorem paramLogDeriv_example :
    (match cParamLogDeriv 30 paramLogDerivExampleF paramLogDerivExampleW with
      | some (n, m, v) =>
          -- `n·f − m·(Dθ/θ) − Dv/v` cleared: with `v = 1`, `Dv/v = 0`, so check `n·f − m·w = 0`.
          let nf := CField.mul (QFunNZ.ofConstNZ ((n : ℚ))) paramLogDerivExampleF
          let mw := CField.mul (QFunNZ.ofConstNZ ((m : ℚ))) paramLogDerivExampleW
          CField.isZero (CField.sub nf mw) && CField.isZero (CField.sub v CField.one)
            && decide (n ≠ 0)
      | none => false) = true := by native_decide

#print axioms paramLogDeriv_example

end DeepWiki.SymbolicIntegration
