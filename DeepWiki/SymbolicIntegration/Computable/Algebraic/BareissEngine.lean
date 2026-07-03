import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Computable.Algebraic.HermiteNormalForm
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd

/-! # Fraction-free linear algebra engine — the Bareiss defs over `ℚ[x]` and `ℚ(x)`

The fraction-free determinant `bareissDet`, adjugate `bareissAdjugate`, and Cramer solve `bareissSolve`
over `ℚ[x]`, plus the `ℚ(x)` wrappers `qfDet`/`qfAdjugate`/`qfInv`/`qfSolve` that clear to a common
denominator and run Bareiss. Every division is exact, so entries stay in `ℚ[x]` with bounded degree. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Matrix entry access and the Bareiss single-step over `ℚ[x]` -/

/-- Read the polynomial entry `M[i][j]` of a `ℚ[x]`-matrix, the zero polynomial `[]` past the end. -/
def getEntry (M : List (List (CPolyG α))) (i j : ℕ) : CPolyG α :=
  (M.getD i []).getD j []

/-- One Bareiss fraction-free elimination step with pivot index `k` and previous pivot `prevPiv`: each
entry `[i][j]` with `i, j > k` becomes `(M[k][k]·M[i][j] − M[i][k]·M[k][j]) / prevPiv` (an exact
division); other entries are unchanged. -/
def bareissStep (prevPiv : CPolyG α) (k : ℕ) (M : List (List (CPolyG α))) :
    List (List (CPolyG α)) :=
  let mkk := getEntry M k k
  (List.range M.length).map (fun i =>
    (List.range (M.getD i []).length).map (fun j =>
      if k < i ∧ k < j then
        let num := csubG (cmulG mkk (getEntry M i j)) (cmulG (getEntry M i k) (getEntry M k j))
        cdivWf num prevPiv
      else getEntry M i j))

/-- Bareiss elimination driver: run `bareissStep` for pivot indices `k = 0, 1, …` carrying the previous
pivot, one step per pivot; returns the reduced matrix whose `[n-1][n-1]` entry is `det M`. -/
def bareissDrive : ℕ → CPolyG α → ℕ → List (List (CPolyG α)) → List (List (CPolyG α))
  | 0, _, _, M => M
  | fuel + 1, prevPiv, k, M =>
    let M' := bareissStep prevPiv k M
    bareissDrive fuel (getEntry M' k k) (k + 1) M'

/-- The Bareiss fraction-free determinant over `ℚ[x]` `bareissDet M`: run `bareissDrive` for `n =
M.length` pivots and read the final pivot `M⁽ⁿ⁾[n-1][n-1]`; the empty matrix has determinant `1`. -/
def bareissDet (M : List (List (CPolyG α))) : CPolyG α :=
  let n := M.length
  if n = 0 then [CField.one]
  else
    let M' := bareissDrive n [CField.one] 0 M
    getEntry M' (n - 1) (n - 1)

/-! ### Fraction-free solve and adjugate (the inverse representation `(det, adjugate)`) -/

/-- Delete row `i` and column `j` from a `ℚ[x]`-matrix (the `(i, j)` minor). -/
def minorMat (M : List (List (CPolyG α))) (i j : ℕ) : List (List (CPolyG α)) :=
  (M.eraseIdx i).map (fun row => row.eraseIdx j)

/-- The adjugate of a `ℚ[x]`-matrix `bareissAdjugate M`, fraction-free: the transpose of the cofactor
matrix, entry `(i, j) = (−1)^{i+j}·det(minor M j i)`; satisfies `M · adj M = (det M)·I`. -/
def bareissAdjugate (M : List (List (CPolyG α))) : List (List (CPolyG α)) :=
  let n := M.length
  (List.range n).map (fun i =>
    (List.range n).map (fun j =>
      let c := bareissDet (minorMat M j i)
      if (i + j) % 2 = 0 then c else cnegG c))

/-- Fraction-free linear solve `bareissSolve M b = (det M, det M · x)` where `x = M⁻¹·b`: by Cramer
`det M · x = adj M · b`, the polynomial solution of `M·(det M·x) = det M·b` over `ℚ[x]`. -/
def bareissSolve (M : List (List (CPolyG α))) (b : List (CPolyG α)) : CPolyG α × List (CPolyG α) :=
  let n := M.length
  let adj := bareissAdjugate M
  let sol := (List.range n).map (fun i =>
    (List.range n).foldl (fun acc j =>
      caddG acc (cmulG (getEntry adj i j) (b.getD j []))) [])
  (bareissDet M, sol)

/-! ### Denominator-combining helpers over `ℚ[x]` (`qfLcm`/`qfRowDen`/`qfMatDen`) -/

/-- The monic lcm of two `CPolyG` polynomials over a field `qfLcm a b = a·b / gcd(a, b)` (gcd via
`cgcdWf`); the `0` polynomial on either side returns the other. -/
def qfLcm (a b : CPolyG α) : CPolyG α :=
  if cisZeroG a then b
  else if cisZeroG b then a
  else
    let g := (cgcdWf a b).1
    cmonicG (cdivWf (cmulG a b) g)

/-- The common denominator of a `ℚ(x)`-row `qfRowDen row`, the monic lcm of the entry denominators;
scaling the row by this `D ∈ ℚ[x]` lands every entry in `ℚ[x]`. -/
def qfRowDen (row : List (QFunNZG ℚ)) : CPolyG ℚ :=
  row.foldl (fun acc z => qfLcm acc (cmonicG (z.1.2 : CPolyG ℚ))) [CField.one]

/-- The common denominator of a whole `ℚ(x)`-matrix `qfMatDen M`, the lcm over all rows of `qfRowDen`;
the single `D ∈ ℚ[x]` with `D·M ∈ ℚ[x]ⁿˣⁿ` and `det(D·M) = Dⁿ·det M`. -/
def qfMatDen (M : List (List (QFunNZG ℚ))) : CPolyG ℚ :=
  M.foldl (fun acc row => qfLcm acc (qfRowDen row)) [CField.one]

/-! ### Clearing a `ℚ(x)`-row / matrix into `ℚ[x]` (`qfClearRow`/`qfClearMatrix`) -/

/-- Clear a single `ℚ(x)` entry by a common denominator `D` `qfClearEntry D z = num(z)·(D/den(z))`, the
`ℚ[x]` polynomial `D·z` (exact since `den(z) | D`). -/
def qfClearEntry (D : CPolyG ℚ) (z : QFunNZG ℚ) : CPolyG ℚ :=
  cmulG (z.1.1 : CPolyG ℚ) (cdivWf D (z.1.2 : CPolyG ℚ))

/-- Clear a single `ℚ(x)`-row to `ℚ[x]` `qfClearRow row = ([D·zᵢ], D)` where `D = qfRowDen row`;
returns the cleared `ℚ[x]`-row paired with the clearing factor `D`. -/
def qfClearRow (row : List (QFunNZG ℚ)) : List (CPolyG ℚ) × CPolyG ℚ :=
  let D := qfRowDen row
  (row.map (qfClearEntry D), D)

/-- Clear a whole `ℚ(x)`-matrix to `ℚ[x]` by a single common denominator `qfClearMatrix M = (D·M, D)`
where `D = qfMatDen M`; the scalar factor `D` tracks the determinant scale `det(D·M) = Dⁿ·det M`. -/
def qfClearMatrix (M : List (List (QFunNZG ℚ))) : List (List (CPolyG ℚ)) × CPolyG ℚ :=
  let D := qfMatDen M
  (M.map (fun row => row.map (qfClearEntry D)), D)

/-! ### The fraction-free determinant / adjugate / inverse / solve over `ℚ(x)` (`qfDet`/`qfAdjugate`/…) -/

/-- The fraction-free determinant of a `ℚ(x)`-matrix `qfDet M`: clear `M` to `M' = D·M ∈ ℚ[x]`, run
`bareissDet M'`, and divide back by `Dⁿ`, returning `qxOfNum(bareissDet M') / qxOfNum(Dⁿ)`. -/
def qfDet (M : List (List (QFunNZG ℚ))) : QFunNZG ℚ :=
  let n := M.length
  let (M', D) := qfClearMatrix M
  let detPoly := bareissDet M'
  let Dn := cpowG D n
  CField.mul (qxOfNum detPoly) (CField.inv (qxOfNum Dn))

/-- The fraction-free adjugate `(adj(D·M), D)` of a `ℚ(x)`-matrix `qfAdjugate M`: clear `M` to
`M' = D·M ∈ ℚ[x]` and return the `ℚ[x]` adjugate `bareissAdjugate M'` paired with `D`; the genuine
`ℚ(x)`-adjugate is `adj(M') / Dⁿ⁻¹`. -/
def qfAdjugate (M : List (List (QFunNZG ℚ))) : List (List (CPolyG ℚ)) × CPolyG ℚ :=
  let (M', D) := qfClearMatrix M
  (bareissAdjugate M', D)

/-- The fraction-free inverse representation of a `ℚ(x)`-matrix `qfInv M = (det(M'), D·adj(M'))` with
`M' = D·M ∈ ℚ[x]`: a pair of flat `ℚ[x]` polynomials with `M⁻¹[i][j] = (D·adj(M'))[i][j] / det(M')`,
one shared denominator `det(M')`. -/
def qfInv (M : List (List (QFunNZG ℚ))) : CPolyG ℚ × List (List (CPolyG ℚ)) :=
  let (M', D) := qfClearMatrix M
  let detPoly := bareissDet M'
  let adjPoly := bareissAdjugate M'
  (detPoly, adjPoly.map (fun row => row.map (fun e => cmulG D e)))

/-- A single `ℚ(x)` entry of the fraction-free inverse `qfInvEntry M i j = (D·adj(M'))[i][j] /
det(M') : QFunNZG ℚ`, reading the `(i, j)` entry of `qfInv` back into `ℚ(x)`. -/
def qfInvEntry (M : List (List (QFunNZG ℚ))) (i j : ℕ) : QFunNZG ℚ :=
  let dn := qfInv M
  CField.mul (qxOfNum (getEntry dn.2 i j)) (CField.inv (qxOfNum dn.1))

/-- The fraction-free Cramer solve of `M·x = b` over `ℚ(x)` `qfSolve M b`: clear `M` to `M' = D·M` and
the rhs to `D·b`, then run `bareissSolve M' (D·b)`, giving `x = (det M'·x)/det M'` with one shared
denominator. -/
def qfSolve (M : List (List (QFunNZG ℚ))) (b : List (QFunNZG ℚ)) :
    CPolyG ℚ × List (CPolyG ℚ) :=
  let (M', D) := qfClearMatrix M
  let b' := b.map (qfClearEntry D)
  bareissSolve M' b'

end CPolyG

end DeepWiki.SymbolicIntegration
