import DeepWiki.SymbolicIntegration.ComputableRadicalExtension
import DeepWiki.SymbolicIntegration.ComputableHermiteNormalForm

/-! # Fraction-free linear algebra ENGINE — the pure Bareiss defs over `ℚ[x]` and `ℚ(x)`
(Bareiss, *Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination*, 1968;
the polynomial form, e.g. Geddes–Czapor–Labahn §9.3)

The **pure** fraction-free linear-algebra primitives, split UPSTREAM of the general algebraic-curve
machinery so the curve call sites (`ComputableAlgFunctionField.discriminant`,
`ComputableRound2IntegralBasis.idealizerBasis`) can call them without forming an import cycle. This
module imports only the polynomial/field-tower floor (`GenericPolyEngine` ops + `QFunNZG ≅ ℚ(x)` and its
`qxOfNum`); it references **no** `fieldDet`/`traceMatrix`/`matInvG`. The agreement lemmas
`bareissDet = fieldDet`, `qfDet = fieldDet`, `qfInv = matInvG` and the swell benchmarks live DOWNSTREAM in
`ComputableBareiss`/`ComputableBareissQF` (which import this engine plus the curve machinery).

* **`bareissDet`** — the fraction-free determinant over `ℚ[x] = CPolyG α` (`cmulG`/`csubG`/`cdivG`, exact:
  every Bareiss division is exact by Sylvester's identity, so entries stay flat — no swell).
* **`bareissAdjugate` / `bareissSolve`** — the adjugate `adj M` and the Cramer solve `(det, det·x)`, the
  fraction-free inverse representation `M⁻¹ = adj M / det M` (the `(det, adjugate)` pair).
* **`qfDet` / `qfAdjugate` / `qfInv` / `qfSolve`** — the `ℚ(x) = QFunNZG ℚ` wrappers: CLEAR each row /
  the matrix to a common denominator into `ℚ[x]` (`qfClearMatrix`), run the fraction-free Bareiss, read the
  result back into `ℚ(x)` — never an intermediate `ℚ(x)` fraction, so no denominator pile-up.

The single Bareiss step recurrence is, with `M⁽⁰⁾ = M`, `p₋₁ = 1`, pivot at `[k][k]`, and for `i, j > k`:

  `M⁽ᵏ⁺¹⁾[i][j] = (M⁽ᵏ⁾[k][k]·M⁽ᵏ⁾[i][j] − M⁽ᵏ⁾[i][k]·M⁽ᵏ⁾[k][j]) / pₖ₋₁`,   `pₖ₋₁ = M⁽ᵏ⁾[k-1][k-1]`.

Every division is **exact** (the numerator is a `2×2` connecting minor, divisible by the previous pivot),
so entries stay in `ℚ[x]` with **bounded degree**; `det M = M⁽ⁿ⁾[n-1][n-1]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Matrix entry access and the Bareiss single-step over `ℚ[x]`

A polynomial matrix is `List (List (CPolyG α))` (rows of `CPolyG α = α[x]` entries). `getEntry M i j`
reads `M[i][j]` (the zero polynomial `[]` past the end). The Bareiss step `bareissStep prevPiv k M`
applies, to every entry `[i][j]` with `i, j > k` (`k` = current pivot index), the cross-multiply
`M[k][k]·M[i][j] − M[i][k]·M[k][j]` divided **exactly** by the previous pivot `prevPiv`. Entries on or
above the pivot row/column are carried unchanged (the upper-triangular part already computed). -/

/-- **Read the polynomial entry `M[i][j]`** of a `ℚ[x]`-matrix (rows of `CPolyG α`); the zero polynomial
`[]` past the end (`getEntry M i j` never panics). -/
def getEntry (M : List (List (CPolyG α))) (i j : ℕ) : CPolyG α :=
  (M.getD i []).getD j []

/-- **One Bareiss fraction-free elimination step** with pivot index `k` and previous pivot `prevPiv`:
each entry `[i][j]` with `i > k` and `j > k` becomes
`(M[k][k]·M[i][j] − M[i][k]·M[k][j]) / prevPiv` (the cross-minor divided **exactly** by the previous
pivot — Bareiss's identity guarantees divisibility, so `cdivG` returns the exact quotient with no
remainder). Entries with `i ≤ k` or `j ≤ k` are left unchanged. `divFuel` bounds the exact division
(`len numerator + 1` suffices). -/
def bareissStep (divFuel : ℕ) (prevPiv : CPolyG α) (k : ℕ) (M : List (List (CPolyG α))) :
    List (List (CPolyG α)) :=
  let mkk := getEntry M k k
  (List.range M.length).map (fun i =>
    (List.range (M.getD i []).length).map (fun j =>
      if k < i ∧ k < j then
        let num := csubG (cmulG mkk (getEntry M i j)) (cmulG (getEntry M i k) (getEntry M k j))
        cdivG divFuel num prevPiv
      else getEntry M i j))

/-- **Bareiss elimination driver**: run `bareissStep` for pivot indices `k = 0, 1, …` carrying the
previous pivot `prevPiv` (initially `[1]`, then `M[k][k]` after step `k`). `fuel` is the **matrix size**
(`ℕ`-structural recursion, one step per pivot). Returns the fully reduced (upper-triangular-in-the-
fraction-free-sense) matrix whose `[n-1][n-1]` entry is `det M`. `divFuel` is passed to each step's exact
division. -/
def bareissDrive (divFuel : ℕ) : ℕ → CPolyG α → ℕ → List (List (CPolyG α)) → List (List (CPolyG α))
  | 0, _, _, M => M
  | fuel + 1, prevPiv, k, M =>
    let M' := bareissStep divFuel prevPiv k M
    bareissDrive divFuel fuel (getEntry M' k k) (k + 1) M'

/-- **The Bareiss fraction-free determinant over `ℚ[x]`** `bareissDet M`: run `bareissDrive` for `n =
M.length` pivots starting from `prevPiv = [1]`, then read the final pivot `M⁽ⁿ⁾[n-1][n-1]`. Every
intermediate entry is an **exact** polynomial (no `ℚ(x)` fraction is ever formed), so the degrees stay
bounded — the swell-free determinant. Equals `fieldDet (fromQ M)` over `ℚ(x)` (validated downstream). The
empty matrix has determinant `1`. -/
def bareissDet (M : List (List (CPolyG α))) : CPolyG α :=
  let n := M.length
  if n = 0 then [CField.one]
  else
    -- a division-fuel bound large enough for every cross-minor numerator over the run
    let divFuel := (M.foldl (fun acc row => acc + row.foldl (fun a p => a + p.length + 1) 0) 0) + n + 2
    let M' := bareissDrive divFuel n [CField.one] 0 M
    getEntry M' (n - 1) (n - 1)

/-! ### Fraction-free solve and adjugate (the inverse representation `(det, adjugate)`)

Over `ℚ[x]` the inverse `M⁻¹ = adj(M)/det(M)` is kept as the **pair** `(det M, adj M)` — both
polynomial, no `ℚ(x)` fraction. `bareissAdjugate` builds `adj M` cofactor-by-cofactor through the
**fraction-free** `bareissDet` on each minor (the `(j, i)` cofactor is `(−1)^{i+j} det(minor M i j)`,
transposed). `bareissSolve M b` returns `(det M, det M · x)` where `x = M⁻¹ b`: the polynomial solution
of `M·(det·x) = det·b`, by Cramer (`adj M · b`). Both stay in `ℚ[x]`. -/

/-- **Delete row `i` and column `j`** from a `ℚ[x]`-matrix (the `(i, j)` minor), for the cofactor
expansion of the adjugate. -/
def minorMat (M : List (List (CPolyG α))) (i j : ℕ) : List (List (CPolyG α)) :=
  (M.eraseIdx i).map (fun row => row.eraseIdx j)

/-- **The adjugate (classical adjoint) of a `ℚ[x]`-matrix** `bareissAdjugate M`, fraction-free: the
**transpose** of the cofactor matrix, entry `(i, j) = (−1)^{i+j}·det(minor M j i)` computed by the
fraction-free `bareissDet`. Satisfies `M · adj M = (det M)·I = adj M · M`, so `M⁻¹ = adj M / det M` is
the fraction-free inverse representation `(det M, adj M)` — never a `ℚ(x)` matrix. -/
def bareissAdjugate (M : List (List (CPolyG α))) : List (List (CPolyG α)) :=
  let n := M.length
  (List.range n).map (fun i =>
    (List.range n).map (fun j =>
      let c := bareissDet (minorMat M j i)
      if (i + j) % 2 = 0 then c else cnegG c))

/-- **Fraction-free linear solve** `bareissSolve M b = (det M, det M · x)` where `x = M⁻¹·b`: by Cramer,
`det M · x = adj M · b`, a polynomial vector (`adj M` applied to the column `b`), paired with `det M`.
The solution of `M·(det M·x) = det M·b` over `ℚ[x]` — no fraction is formed; recover `x` as
`(det M · x)/det M` only if a genuine `ℚ(x)` value is wanted. -/
def bareissSolve (M : List (List (CPolyG α))) (b : List (CPolyG α)) : CPolyG α × List (CPolyG α) :=
  let n := M.length
  let adj := bareissAdjugate M
  let sol := (List.range n).map (fun i =>
    (List.range n).foldl (fun acc j =>
      caddG acc (cmulG (getEntry adj i j) (b.getD j []))) [])
  (bareissDet M, sol)

/-! ### Denominator-combining helpers over `ℚ[x]` (`qfLcm`/`qfRowDen`/`qfMatDen`)

To clear a `ℚ(x)`-matrix into `ℚ[x]` we need a common multiple of the entry denominators. The **lcm**
`lcm(a, b) = a·b / gcd(a, b)` keeps the cleared degree minimal (a coarse product would over-inflate `D`,
re-introducing swell); `gcd` is the Euclidean `cgcdExtG` over `ℚ[x]` (monic). `qfRowDen` folds the lcm
over a row's denominators, `qfMatDen` over the whole matrix — the common denominator `D` to clear by. -/

/-- **The lcm of two `CPolyG` polynomials over a field** `qfLcm fuel a b = a·b / gcd(a, b)` (monic, gcd via
the `[CField α]`-only Euclidean `cgcdExtG`), the minimal common multiple — used to combine entry
denominators when clearing a `ℚ(x)`-row to `ℚ[x]`. The `0` polynomial on either side returns the other
(`lcm(a, 0) = a`); `lcm(1, b) = b`. Fuel bounds the gcd and the exact division. Pure engine ops (no
`CFracGcd`/`CFieldSpec`), so it reduces under `native_decide`. -/
def qfLcm (fuel : ℕ) (a b : CPolyG α) : CPolyG α :=
  if cisZeroG a then b
  else if cisZeroG b then a
  else
    let g := (cgcdExtG fuel a b).1
    cmonicG (cdivG fuel (cmulG a b) g)

/-- **The common denominator of a `ℚ(x)`-row** `qfRowDen fuel row = lcm of the entry denominators`
(`z.1.2` over the row, normalized monic, `cgcdExtG`-lcm-folded). Scaling the row by this `D ∈ ℚ[x]` lands
every entry in `ℚ[x]` (its denominator divides `D`). Starts from `[1]` (the empty row clears trivially). -/
def qfRowDen (fuel : ℕ) (row : List (QFunNZG ℚ)) : CPolyG ℚ :=
  row.foldl (fun acc z => qfLcm fuel acc (cmonicG (z.1.2 : CPolyG ℚ))) [CField.one]

/-- **The common denominator of a whole `ℚ(x)`-matrix** `qfMatDen fuel M = lcm of every entry denominator`
(the lcm over all rows of `qfRowDen`). The single `D ∈ ℚ[x]` to scale the **whole** matrix by so that
`D·M ∈ ℚ[x]ⁿˣⁿ`; then `det(D·M) = Dⁿ·det M` and `(D·M)⁻¹` reads back the fraction-free inverse. -/
def qfMatDen (fuel : ℕ) (M : List (List (QFunNZG ℚ))) : CPolyG ℚ :=
  M.foldl (fun acc row => qfLcm fuel acc (qfRowDen fuel row)) [CField.one]

/-! ### Clearing a `ℚ(x)`-row / matrix into `ℚ[x]` (`qfClearRow`/`qfClearMatrix`)

`qfClearRow` scales a `ℚ(x)`-row by the lcm `D` of its denominators and reads each `D·zᵢ` numerator (a
`ℚ[x]` polynomial since `denᵢ | D`), returning the cleared `ℚ[x]`-row **and** the factor `D` (the row's
contribution to the determinant scale). `qfClearMatrix` clears the **whole** matrix by a *single* common
denominator `D = qfMatDen M` (so the scale is the scalar `D`, not a diagonal), returning the
`ℚ[x]`-matrix `D·M` and `D`; then `det(D·M) = Dⁿ·det M` (`qfDet` divides back by `Dⁿ`). -/

/-- **Clear a single `ℚ(x)` entry by a common denominator `D`** `qfClearEntry fuel D z = num(z)·(D/den(z))`,
the `ℚ[x]` polynomial `D·z` — **exact** because `den(z) | D` (`D` is a common multiple), so `D/den(z) ∈ ℚ[x]`
and `num(z)·(D/den(z)) = D·z`. (NOT `(qxOfNum D · z).1.1`, which is `D·num(z)` — it ignores that `z`'s
denominator survives in the *unreduced* product's denominator.) The per-entry clearing primitive. -/
def qfClearEntry (fuel : ℕ) (D : CPolyG ℚ) (z : QFunNZG ℚ) : CPolyG ℚ :=
  cmulG (z.1.1 : CPolyG ℚ) (cdivG fuel D (z.1.2 : CPolyG ℚ))

/-- **Clear a single `ℚ(x)`-row to `ℚ[x]`** `qfClearRow fuel row = ([D·zᵢ], D)` where `D = qfRowDen row` is
the lcm of the row's denominators. Each `D·zᵢ = num(zᵢ)·(D/den(zᵢ))` is in `ℚ[x]` (`den(zᵢ) | D`,
`qfClearEntry`). Returns the cleared `ℚ[x]`-row paired with the clearing factor `D` (the row's
determinant-scale contribution). -/
def qfClearRow (fuel : ℕ) (row : List (QFunNZG ℚ)) : List (CPolyG ℚ) × CPolyG ℚ :=
  let D := qfRowDen fuel row
  (row.map (qfClearEntry fuel D), D)

/-- **Clear a whole `ℚ(x)`-matrix to `ℚ[x]` by a single common denominator** `qfClearMatrix fuel M =
(D·M, D)` where `D = qfMatDen M` is the lcm of **all** entry denominators. Every entry `D·M[i][j] =
num·(D/den) ∈ ℚ[x]` (`qfClearEntry`, exact since each denominator divides `D`), so the result is a
`ℚ[x]`-matrix; the scalar factor `D` tracks the determinant scale `det(D·M) = Dⁿ·det M`. (A single scalar
`D` — not a per-row diagonal — so the inverse reads back as `M⁻¹ = D·adj(D·M)/det(D·M)`.) -/
def qfClearMatrix (fuel : ℕ) (M : List (List (QFunNZG ℚ))) : List (List (CPolyG ℚ)) × CPolyG ℚ :=
  let D := qfMatDen fuel M
  (M.map (fun row => row.map (qfClearEntry fuel D)), D)

/-! ### The fraction-free determinant / adjugate / inverse / solve over `ℚ(x)` (`qfDet`/`qfAdjugate`/…)

With the clearing in hand, the `ℚ(x)` linear algebra routes through Bareiss over `ℚ[x]`:

* **`qfDet M`**: clear `M` to `(M', D)` (`M' = D·M ∈ ℚ[x]`), run `bareissDet M'`, and divide back by `Dⁿ`
  (`det M = det(D·M)/Dⁿ`) as a `ℚ(x)` value `bareissDet M' / Dⁿ` — never an intermediate fraction.
* **`qfAdjugate M`**: `bareissAdjugate M'` over `ℚ[x]`. With `M' = D·M`, `adj(M') = Dⁿ⁻¹·adj(M)`, so the
  `ℚ(x)`-adjugate of `M` is `adj(M') / Dⁿ⁻¹`; we return the **`ℚ[x]`** adjugate `adj(M')` paired with `D`.
* **`qfInv M = (det, adjugate)`** as the fraction-free inverse representation: `M⁻¹ = D·adj(M')/det(M')`
  (the `(det(M'), D·adj(M'))` pair, both flat `ℚ[x]`). Each entry `(M⁻¹)[i][j] = D·adj(M')[i][j]/det(M')`.
* **`qfSolve M b`**: clear `M` and the rhs `b` by `D` and run `bareissSolve` over `ℚ[x]`. -/

/-- **The fraction-free determinant of a `ℚ(x)`-matrix** `qfDet fuel M`: clear `M` to the `ℚ[x]`-matrix
`M' = D·M` (`D = qfMatDen M`), run the fraction-free `bareissDet M'` over `ℚ[x]`, and divide back by `Dⁿ`
(`det M = det(D·M)/Dⁿ`), returning the `ℚ(x)` value `qxOfNum(bareissDet M') / qxOfNum(Dⁿ)`. **No
intermediate `ℚ(x)` fraction is ever formed** — the determinant is a single flat `ℚ[x]` polynomial over the
single denominator `Dⁿ`. Equals `fieldDet M` (validated downstream). -/
def qfDet (fuel : ℕ) (M : List (List (QFunNZG ℚ))) : QFunNZG ℚ :=
  let n := M.length
  let (M', D) := qfClearMatrix fuel M
  let detPoly := bareissDet M'
  let Dn := cpowG D n
  CField.mul (qxOfNum detPoly) (CField.inv (qxOfNum Dn))

/-- **The fraction-free adjugate `(adj(D·M), D)` of a `ℚ(x)`-matrix** `qfAdjugate fuel M`: clear `M` to
`M' = D·M ∈ ℚ[x]`, return the **`ℚ[x]`** adjugate `bareissAdjugate M'` paired with the common denominator
`D`. The genuine `ℚ(x)`-adjugate is `adj(M') / Dⁿ⁻¹` (since `adj(D·M) = Dⁿ⁻¹·adj M`); keeping the flat
`ℚ[x]` adjugate avoids fractions. Consumed by `qfInv` (which reads `M⁻¹ = D·adj(M')/det(M')`). -/
def qfAdjugate (fuel : ℕ) (M : List (List (QFunNZG ℚ))) : List (List (CPolyG ℚ)) × CPolyG ℚ :=
  let (M', D) := qfClearMatrix fuel M
  (bareissAdjugate M', D)

/-- **The fraction-free inverse representation of a `ℚ(x)`-matrix** `qfInv fuel M = (det(M'), D·adj(M'))`
with `M' = D·M ∈ ℚ[x]`: the pair of **flat `ℚ[x]`** polynomials `(det(D·M), D·adj(D·M))` so that
`M⁻¹[i][j] = (D·adj(M'))[i][j] / det(M')` — a single shared `ℚ[x]` denominator `det(M')`, no per-entry
fraction. (Derivation: `M = D⁻¹M'`, so `M⁻¹ = M'⁻¹·D = (adj M'/det M')·D`.) **The fraction-free inverse**:
where `matInvG` over `ℚ(x)` swells each entry to total degree `~40`, this is one bounded adjugate matrix
over one determinant. Returns `(detM', adjM'·D)` where `adjM'·D` scales every entry of `adj(M')` by the
`ℚ[x]` polynomial `D`. -/
def qfInv (fuel : ℕ) (M : List (List (QFunNZG ℚ))) : CPolyG ℚ × List (List (CPolyG ℚ)) :=
  let (M', D) := qfClearMatrix fuel M
  let detPoly := bareissDet M'
  let adjPoly := bareissAdjugate M'
  (detPoly, adjPoly.map (fun row => row.map (fun e => cmulG D e)))

/-- **A single `ℚ(x)` entry of the fraction-free inverse** `qfInvEntry fuel M i j = (D·adj(M'))[i][j] /
det(M') : QFunNZG ℚ` — read the `(i, j)` entry of `qfInv` back into `ℚ(x)` (numerator the flat `ℚ[x]`
polynomial `D·adj(M')[i][j]`, denominator `det(M')`). Used to compare `qfInv` against `matInvG` entrywise. -/
def qfInvEntry (fuel : ℕ) (M : List (List (QFunNZG ℚ))) (i j : ℕ) : QFunNZG ℚ :=
  let dn := qfInv fuel M
  CField.mul (qxOfNum (getEntry dn.2 i j)) (CField.inv (qxOfNum dn.1))

/-- **The fraction-free Cramer solve of `M·x = b` over `ℚ(x)`** `qfSolve fuel M b`: clear `M` to `M' = D·M`
and the rhs to `D·b`, both in `ℚ[x]`, run `bareissSolve M' (D·b)` (returns `(det M', det M'·x)` over
`ℚ[x]`). Since `M·x = b ⟺ (D·M)·x = D·b`, the polynomial solution `det(M')·x` and `det(M')` give
`x = (det M'·x)/det M'` over `ℚ(x)` with one shared denominator — no per-component fraction. -/
def qfSolve (fuel : ℕ) (M : List (List (QFunNZG ℚ))) (b : List (QFunNZG ℚ)) :
    CPolyG ℚ × List (CPolyG ℚ) :=
  let (M', D) := qfClearMatrix fuel M
  let b' := b.map (qfClearEntry fuel D)
  bareissSolve M' b'

end CPolyG

end DeepWiki.SymbolicIntegration
