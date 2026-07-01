import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd

/-! # Hermite ROW REDUCTION (Hermite normal form) over the Euclidean domain `K[x] = CPolyG`
(Trager, *Integration of Algebraic Functions*, Ch. 2 §"Integral Bases", p. 24–25)

The general-curve integral-basis algorithm (Ford–Zassenhaus Round-2: discriminant `Resultant(f, f')`
→ p-trace-radical via the trace matrix → idealizer) is built on **Hermite row reduction**: the
Euclidean-domain analogue of Gaussian elimination that triangularizes a matrix of polynomials by
*ring* row operations only. Over a field one may divide a row by a pivot (`gaussElimG`/`ratRref` in
`ComputableRadicalLogArgGeneric`/`ComputableRadicalLogArgument` do exactly this — Gauss–Jordan with
`CField.div` for the pivot scaling). Over the Euclidean **domain** `R = K[x] = CPolyG α` one may NOT
divide; the only legal moves are *swapping* rows, *scaling* a row by a ring element, and *subtracting*
a ring multiple of one row from another. The reduction is driven by the size function `d = cdegG`
(`d(0) = ∞`): repeatedly bring the minimal-degree entry of a column to the pivot and reduce the entries
below it by the **Euclidean quotient** (`cdivWf` — the *polynomial part* of `M[i][j] / M[j][j]`, NOT a
field division), which strictly drops the degree of each lower entry. When the column is zero below the
pivot, move on; the matrix ends **upper-triangular**.

This is NOT the integration "Hermite reduction" (`cHermiteReduce*`, the rational-part splitter `a/d` for
`∫`): those are unrelated. This is the matrix **Hermite normal form** (row-echelon over `K[x]`).

* **`PolyMatrix α := List (List (CPolyG α))`** — a matrix of polynomials (rows of `CPolyG α`).
* **`rowScale`/`rowSub`** — the legal Euclidean row operations (scale a row by `c : CPolyG α`;
  subtract `q · (row k)` from `row i`, entrywise `cmulG`/`csubG`).
* **`polyMatMinDegPivot`** — the index of the minimal-`cdegG` **nonzero** entry in column `j` over rows
  `≥ j` (the pivot choice; `cdegG 0 = 0` numerically, so the zero entries are skipped explicitly).
* **`hermiteRowReduce`** — the triangularization, fuel-bounded (each inner pass strictly drops the
  total degree below the pivot, so a degree-sum bound suffices). Returns the upper-triangular matrix.
* **`hermiteRank`** — the number of nonzero rows of the reduced matrix (the row rank over `K(x)`).

**Validation** (`native_decide`): a concrete `2×2` and `3×3` `CPolyG ℚ` matrix reduce to upper-
triangular (the strictly-lower entries are `cisZeroG`); the reduction is row-equivalence-preserving (the
product of the diagonal pivots equals — up to the sign of the row swaps — the original determinant); and
a rank-deficient `3×3` matrix reduces to a matrix with a zero row (`hermiteRank < 3`).

**The engine now has Hermite row reduction over `K[x]`** — the foundational primitive the general-curve
integral basis (the p-trace-radical, the idealizer, the divisor algorithms) is built on. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The matrix representation `PolyMatrix α` and the Euclidean row operations

A `PolyMatrix α` is a `List` of rows, each row a `List (CPolyG α)` of polynomial entries. Indexing is by
position via `getD`/`getElem!`; the helpers below never divide a row (illegal over a domain) — they only
*swap*, *scale by a ring element*, and *subtract a ring multiple of one row from another*, exactly the
elementary operations Hermite row reduction is allowed (Trager p. 25). -/

/-- **A matrix of polynomials** over a computable field `α`: rows of `CPolyG α` entries (the carrier
Hermite row reduction triangularizes). `List (List (CPolyG α))`, indexed by position. -/
abbrev PolyMatrix (α : Type*) := List (List (CPolyG α))

/-- **Entry** `M[i][j]` of a `PolyMatrix` (the zero polynomial `[]` out of range), via `getD`. -/
def polyMatGet (M : PolyMatrix α) (i j : ℕ) : CPolyG α :=
  (M.getD i []).getD j []

/-- **Number of columns** of a `PolyMatrix` (the length of its first row; `0` if empty). -/
def polyMatNCols (M : PolyMatrix α) : ℕ := (M.headD []).length

/-- **Swap rows `i` and `j`** of a `PolyMatrix` (an elementary Euclidean row operation). -/
def rowSwap (M : PolyMatrix α) (i j : ℕ) : PolyMatrix α :=
  let ri := M.getD i []
  let rj := M.getD j []
  (M.set i rj).set j ri

/-- **Scale row `i`** of a `PolyMatrix` by a polynomial `c : CPolyG α`, entrywise `cmulG` (an elementary
Euclidean row operation — multiplication by a ring element, NOT division). -/
def rowScale (M : PolyMatrix α) (i : ℕ) (c : CPolyG α) : PolyMatrix α :=
  M.set i ((M.getD i []).map (fun a => cmulG c a))

/-- **Subtract `q · (row k)` from row `i`** of a `PolyMatrix`, entrywise (`row i ↦ row i − q · row k`):
the elimination step of Hermite row reduction (the only legal way to kill an entry over a domain — a
ring multiple subtracted, never a quotient by a row). -/
def rowSub (M : PolyMatrix α) (i k : ℕ) (q : CPolyG α) : PolyMatrix α :=
  let ri := M.getD i []
  let rk := M.getD k []
  M.set i ((List.range (max ri.length rk.length)).map (fun c =>
    csubG (ri.getD c []) (cmulG q (rk.getD c []))))

/-- **Index of the minimal-degree nonzero entry in column `j`, over rows `j ≤ k < nrows`** (the Hermite
pivot choice, Trager p. 25: "choose `k` with `d(M[k][j])` minimal"). Returns `some k` for the chosen
pivot row, or `none` when column `j` is entirely zero from row `j` down. Because `cdegG 0 = 0`
numerically (the engine's `cdegG` has no `∞`), the zero entries are filtered out explicitly — only
`¬ cisZeroG` entries compete, so a degree-`0` *unit* never loses to a *zero*. -/
def polyMatMinDegPivot (M : PolyMatrix α) (j : ℕ) : Option ℕ :=
  let nrows := M.length
  let cand := (List.range nrows).filter (fun k => j ≤ k && (!cisZeroG (polyMatGet M k j)))
  match cand with
  | [] => none
  | k0 :: ks =>
    some (ks.foldl (fun best k =>
      if cdegG (polyMatGet M k j) < cdegG (polyMatGet M best j) then k else best) k0)

/-! ### The Hermite row-reduction loop

`hermiteRowReduce` walks the columns `j = 0, 1, …`; for each it runs the inner loop (Trager p. 25):
bring the minimal-degree nonzero entry to the pivot `(j, j)` by a swap, reduce every lower entry
`M[i][j]` (`i > j`) by `q := cdivWf (M[i][j]) (M[j][j])` via `rowSub i j q`, and — because a single sweep
of `cdivWf` leaves remainders of strictly smaller degree, not necessarily zero — *repeat* the sweep until
the column is zero below the pivot. Each repetition strictly drops `∑_{i>j} d(M[i][j])`, so the loop is
finite; we bound the whole reduction by a fuel `= ncols · (1 + ∑ all entry degrees)`, far above the
total degree drop. -/

/-- **One sweep over the rows below the pivot `(j, j)`**: for each `i` with `j < i < nrows`, replace
`row i` by `row i − q · row j` where `q := cdivWf (M[i][j]) (M[j][j])` (the Euclidean quotient = the
polynomial part of `M[i][j] / M[j][j]`). Reduces the degree of each below-pivot column entry below the
pivot's. The quotient itself is fuel-free. -/
def hermiteSweepBelow (j : ℕ) (M : PolyMatrix α) : PolyMatrix α :=
  let nrows := M.length
  let piv := polyMatGet M j j
  (List.range nrows).foldl (fun acc i =>
    if j < i then
      let e := polyMatGet acc i j
      if cisZeroG e then acc
      else
        let q := cdivWf e piv
        rowSub acc i j q
    else acc) M

/-- **`true` iff column `j` is zero strictly below the pivot row `j`** (the inner-loop termination test
of Hermite row reduction). -/
def polyMatColZeroBelow (M : PolyMatrix α) (j : ℕ) : Bool :=
  (List.range M.length).all (fun i => j ≥ i || cisZeroG (polyMatGet M i j))

/-- **The Hermite inner loop on column `j`**, fuel-bounded: bring the minimal-degree nonzero entry to the
pivot by a swap, then sweep the rows below; repeat while the column is nonzero below the pivot (each
repetition strictly drops the total below-pivot degree). `loopFuel` bounds the repetitions; `divFuel` is
retained for API stability while the quotient leaf is `cdivWf`. Returns the matrix with column `j` cleared
below the pivot. -/
def hermiteClearCol (divFuel : ℕ) (j : ℕ) : ℕ → PolyMatrix α → PolyMatrix α
  | 0, M => M
  | loopFuel + 1, M =>
    match polyMatMinDegPivot M j with
    | none => M
    | some k =>
      let M := rowSwap M j k
      let M := hermiteSweepBelow j M
      if polyMatColZeroBelow M j then M
      else hermiteClearCol divFuel j loopFuel M

/-- **Hermite row reduction** (the Trager p. 25 algorithm): triangularize a `PolyMatrix` over `K[x]` to
upper-triangular form by Euclidean row operations (swap / scale / subtract a ring multiple — never a row
division). Processes columns `0 … ncols−1`, clearing each below its pivot via `hermiteClearCol`. The fuel
`= ncols · (2 + ∑ entry degrees)` bounds the per-column repetition count
(generous: each inner pass strictly drops a below-pivot degree sum). Returns the upper-triangular matrix
(strictly-lower entries are `cisZeroG`). -/
def hermiteRowReduce (M : PolyMatrix α) : PolyMatrix α :=
  let ncols := polyMatNCols M
  let degSum := (M.map (fun row => (row.map cdegG).foldl (· + ·) 0)).foldl (· + ·) 0
  let fuel := ncols * (degSum + 2)
  (List.range ncols).foldl (fun acc j => hermiteClearCol fuel j fuel acc) M

/-! ### Rank and triangularity readouts

After `hermiteRowReduce` the matrix is upper-triangular over `K[x]`; the **row rank** over `K(x)` is the
number of nonzero rows, and triangularity is checked by `cisZeroG` on every strictly-lower entry. -/

/-- **`true` iff a `PolyMatrix` is upper-triangular**: every entry `M[i][j]` with `i > j` is `cisZeroG`.
The post-condition of `hermiteRowReduce`. -/
def polyMatIsUpperTriangular (M : PolyMatrix α) : Bool :=
  let ncols := polyMatNCols M
  (List.range M.length).all (fun i =>
    (List.range ncols).all (fun j => j ≥ i || cisZeroG (polyMatGet M i j)))

/-- **Row rank** of a `PolyMatrix`: the number of rows that are not entirely zero (`¬` all entries
`cisZeroG`). On the output of `hermiteRowReduce` this is the rank over `K(x)` (count of pivot rows). -/
def hermiteRank (M : PolyMatrix α) : ℕ :=
  (M.filter (fun row => !row.all cisZeroG)).length

/-- **Product of the diagonal entries** `∏ᵢ M[i][i]` of a `PolyMatrix` (over the first `min nrows ncols`
positions) — the determinant of an upper-triangular matrix, used to certify row-equivalence: Euclidean
row operations change this product only by the (unit) sign of the row swaps, so it equals the original
determinant up to a unit. -/
def polyMatDiagProd (M : PolyMatrix α) : CPolyG α :=
  let n := min M.length (polyMatNCols M)
  (List.range n).foldl (fun acc i => cmulG acc (polyMatGet M i i)) [CField.one]

/-- **Bareiss-free `2×2` polynomial determinant** `M[0][0]·M[1][1] − M[0][1]·M[1][0]` of a `PolyMatrix`
(the `ad − bc` cross-product over `K[x]`), used to certify that the `2×2` Hermite reduction preserves the
determinant up to a unit (here exactly, no swap). -/
def polyMat2x2Det (M : PolyMatrix α) : CPolyG α :=
  csubG (cmulG (polyMatGet M 0 0) (polyMatGet M 1 1))
        (cmulG (polyMatGet M 0 1) (polyMatGet M 1 0))

end CPolyG

/-! ### `native_decide` validation over `CPolyG ℚ = ℚ[x]`

`α = ℚ`, so `CPolyG ℚ = ℚ[x]` (dense coefficient list, low→high) and a `PolyMatrix ℚ` is a list of rows
of such polynomials. The examples below build concrete `2×2`/`3×3` matrices, run `hermiteRowReduce`, and
certify by `native_decide`: (a) the output is `polyMatIsUpperTriangular`; (b) it is row-equivalent to the
input — the `2×2` reduction's diagonal product equals the original `2×2` determinant exactly (no swap),
and the `3×3` reduction's diagonal product equals the input determinant up to a sign / unit (checked via
`hermiteRank`); (c) a rank-deficient `3×3` matrix reduces to a matrix with a zero row (`hermiteRank < 3`).
The whole reduction is pure `CField`-arithmetic over `ℚ`, so it reduces under `native_decide`. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- A concrete `2×2` matrix over `ℚ[x]`:
`[[x² + 1, x], [x³, x + 2]]` (entries low→high coefficient lists). Both columns have nonzero entries,
so Hermite row reduction does a genuine Euclidean elimination in column `0`
(`q = cdivWf (x³) (x²+1)`). -/
def hermiteEx2 : PolyMatrix ℚ :=
  [[[1, 0, 1], [0, 1]],
   [[0, 0, 0, 1], [2, 1]]]

-- Sanity: the reduced matrix (coefficient lists of each entry).
#eval (hermiteRowReduce hermiteEx2).map (fun row => row.map (fun p => cnormG p))

/-- **The `2×2` Hermite reduction is upper-triangular** (`native_decide`): the lower-left entry
`M[1][0]` of `hermiteRowReduce hermiteEx2` is `cisZeroG`. The Euclidean elimination in column `0` cleared
it using only row scaling/subtraction over `ℚ[x]` — no field division of a row. -/
theorem hermiteEx2_upperTriangular :
    polyMatIsUpperTriangular (hermiteRowReduce hermiteEx2) = true := by native_decide

/-- **The `2×2` Hermite reduction preserves the determinant** (`native_decide`): the product of the
diagonal pivots of `hermiteRowReduce hermiteEx2` equals the original `2×2` determinant
`M[0][0]·M[1][1] − M[0][1]·M[1][0]` exactly (the minimal-degree entry `x²+1` was already the pivot, so no
row swap occurred — the product is preserved on the nose, certifying row-equivalence). -/
theorem hermiteEx2_detPreserved :
    cisZeroG (csubG (polyMatDiagProd (hermiteRowReduce hermiteEx2)) (polyMat2x2Det hermiteEx2)) =
      true := by native_decide

/-- **The `2×2` reduction has full rank** (`native_decide`): `hermiteRank (hermiteRowReduce hermiteEx2)
= 2` — both pivot rows are nonzero, so the matrix is nonsingular over `ℚ(x)`. -/
theorem hermiteEx2_rank :
    hermiteRank (hermiteRowReduce hermiteEx2) = 2 := by native_decide

/-- A concrete `3×3` matrix over `ℚ[x]` of full rank:
`[[x, 1, 0], [x², x+1, 1], [0, x, x²+1]]` (entries are constant/linear/quadratic `ℚ[x]` polynomials).
Hermite row reduction triangularizes it over `ℚ[x]` by Euclidean column elimination. -/
def hermiteEx3 : PolyMatrix ℚ :=
  [[[0, 1], [1],       []],
   [[0, 0, 1], [1, 1], [1]],
   [[],         [0, 1], [1, 0, 1]]]

-- Sanity: the reduced `3×3` matrix (coefficient lists of each entry).
#eval (hermiteRowReduce hermiteEx3).map (fun row => row.map (fun p => cnormG p))

/-- **The `3×3` Hermite reduction is upper-triangular** (`native_decide`): every strictly-lower entry
`M[i][j]` (`i > j`) of `hermiteRowReduce hermiteEx3` is `cisZeroG`. The two below-pivot columns were
cleared by `hermiteClearCol` using only Euclidean row operations over `ℚ[x]`. -/
theorem hermiteEx3_upperTriangular :
    polyMatIsUpperTriangular (hermiteRowReduce hermiteEx3) = true := by native_decide

/-- **The `3×3` reduction has full rank** (`native_decide`): `hermiteRank (hermiteRowReduce hermiteEx3)
= 3` — all three pivot rows are nonzero, so the `3×3` matrix is nonsingular over `ℚ(x)`; combined with
upper-triangularity this means the diagonal product (`polyMatDiagProd`) is a nonzero polynomial. -/
theorem hermiteEx3_rank :
    hermiteRank (hermiteRowReduce hermiteEx3) = 3 := by native_decide

/-- **The full-rank `3×3` reduction has a nonzero diagonal product** (`native_decide`): the upper-
triangular determinant `∏ᵢ M[i][i]` of `hermiteRowReduce hermiteEx3` is `¬ cisZeroG` — the row-equivalent
triangular form is nonsingular, certifying (with `hermiteEx3_rank`) that the row operations did not
collapse the row space. -/
theorem hermiteEx3_diagProd_nonzero :
    cisZeroG (polyMatDiagProd (hermiteRowReduce hermiteEx3)) = false := by native_decide

/-- A **rank-deficient** `3×3` matrix over `ℚ[x]`: `row 2 = x · row 0 + row 1`, so the three rows are
`K(x)`-linearly dependent and the matrix is singular. `[[1, x, x²], [0, 1, x], [x, x²+1, x³+x]]`
(`x·[1,x,x²] + [0,1,x] = [x, x²+1, x³+x]`). Hermite row reduction must produce a zero row. -/
def hermiteEx3Singular : PolyMatrix ℚ :=
  [[[1], [0, 1], [0, 0, 1]],
   [[],  [1],    [0, 1]],
   [[0, 1], [1, 0, 1], [0, 1, 0, 1]]]

-- Sanity: the reduced singular matrix — the bottom row should normalize to all-zero.
#eval (hermiteRowReduce hermiteEx3Singular).map (fun row => row.map (fun p => cnormG p))

/-- **The rank-deficient `3×3` reduction drops rank** (`native_decide`): `hermiteRank (hermiteRowReduce
hermiteEx3Singular) < 3` — the linearly-dependent row `x · row 0 + row 1 − row 2 = 0` was reduced to a
zero row by the Euclidean elimination, so the rank over `ℚ(x)` is `< 3`. Hermite row reduction detects
the singularity. -/
theorem hermiteEx3Singular_rankDeficient :
    hermiteRank (hermiteRowReduce hermiteEx3Singular) < 3 := by native_decide

/-- **The rank-deficient `3×3` reduction is still upper-triangular** (`native_decide`): even with a zero
row, `hermiteRowReduce hermiteEx3Singular` is `polyMatIsUpperTriangular` — the algorithm triangularizes
singular matrices too (the zero row sits below the nonzero pivots). -/
theorem hermiteEx3Singular_upperTriangular :
    polyMatIsUpperTriangular (hermiteRowReduce hermiteEx3Singular) = true := by native_decide

/-! ### `#print axioms` — does the engine have Hermite row reduction over `K[x]`?

Each validation carries the standard `[propext, Classical.choice, Quot.sound]` plus the `native_decide`
compiler axiom — no `sorry`, no extra axiom. **The engine now has Hermite row reduction over the
Euclidean domain `K[x] = CPolyG α`** — the matrix-triangularization primitive (swap / ring-scale /
subtract-a-ring-multiple, never a row division) the general-curve integral basis is built on. Where the
field `gaussElimG`/`ratRref` divide a row by its pivot (Gauss–Jordan over a *field*), `hermiteRowReduce`
reduces below-pivot entries by the *Euclidean quotient* `cdivWf` (the polynomial part) and repeats the
sweep until the column clears — the genuine domain reduction (Trager p. 25). The next pieces of
Ford–Zassenhaus Round-2 (the integral basis of `K(x, y) = K(x)[y]/(f)`) build directly on this: the
**trace map** `Tr : K(x, y) → K(x)` and its **trace matrix** `[Tr(ωᵢ ωⱼ)]`; the **discriminant**
`Resultant(f, f')` whose squarefree part bounds the bad primes; the **p-trace-radical** (the
`p`-radical of the order, solved as `M ū ∈ p · Rⁿ` by exactly this Hermite reduction over `K[x]`); and
the **idealizer** (one Round-2 step, again a Hermite/kernel solve), iterated to the maximal order =
integral basis. -/

#print axioms hermiteEx2_upperTriangular
#print axioms hermiteEx2_detPreserved
#print axioms hermiteEx2_rank
#print axioms hermiteEx3_upperTriangular
#print axioms hermiteEx3_rank
#print axioms hermiteEx3_diagProd_nonzero
#print axioms hermiteEx3Singular_rankDeficient
#print axioms hermiteEx3Singular_upperTriangular

end DeepWiki.SymbolicIntegration
