import DeepWiki.SymbolicIntegration.Engine.Algebraic.BareissEngine.Polynomial

/-! # Fraction-free rational-function Bareiss wrappers

The `ℚ(x)` wrappers `qfDet`/`qfAdjugate`/`qfInv`/`qfSolve` clear a matrix to a common denominator
and run the polynomial Bareiss engine. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### Denominator-combining helpers over `ℚ[x]` (`qfLcm`/`qfRowDen`/`qfMatDen`) -/

/-- The monic lcm of two `DensePoly` polynomials over a field `qfLcm a b = a·b / gcd(a, b)` (gcd via
`cgcdWf`); the `0` polynomial on either side returns the other. -/
def qfLcm (a b : DensePoly α) : DensePoly α :=
  if cisZero a then b
  else if cisZero b then a
  else
    let g := (cgcdWf a b).1
    cmonic (cdivWf (cmul a b) g)

/-- The common denominator of a `ℚ(x)`-row `qfRowDen row`, the monic lcm of the entry denominators;
scaling the row by this `D ∈ ℚ[x]` lands every entry in `ℚ[x]`. -/
def qfRowDen (row : List (DenseFrac ℚ)) : DensePoly ℚ :=
  row.foldl (fun acc z => qfLcm acc (cmonic z.den)) [CCommRing.one]

/-- The common denominator of a whole `ℚ(x)`-matrix `qfMatDen M`, the lcm over all rows of `qfRowDen`;
the single `D ∈ ℚ[x]` with `D·M ∈ ℚ[x]ⁿˣⁿ` and `det(D·M) = Dⁿ·det M`. -/
def qfMatDen (M : List (List (DenseFrac ℚ))) : DensePoly ℚ :=
  M.foldl (fun acc row => qfLcm acc (qfRowDen row)) [CCommRing.one]

/-! ### Clearing a `ℚ(x)`-row / matrix into `ℚ[x]` (`qfClearRow`/`qfClearMatrix`) -/

/-- Clear a single `ℚ(x)` entry by a common denominator `D` `qfClearEntry D z = num(z)·(D/den(z))`, the
`ℚ[x]` polynomial `D·z` (exact since `den(z) | D`). -/
def qfClearEntry (D : DensePoly ℚ) (z : DenseFrac ℚ) : DensePoly ℚ :=
  cmul z.num (cdivWf D z.den)

/-- Clear a single `ℚ(x)`-row to `ℚ[x]` `qfClearRow row = ([D·zᵢ], D)` where `D = qfRowDen row`;
returns the cleared `ℚ[x]`-row paired with the clearing factor `D`. -/
def qfClearRow (row : List (DenseFrac ℚ)) : List (DensePoly ℚ) × DensePoly ℚ :=
  let D := qfRowDen row
  (row.map (qfClearEntry D), D)

/-- Clear a whole `ℚ(x)`-matrix to `ℚ[x]` by a single common denominator `qfClearMatrix M = (D·M, D)`
where `D = qfMatDen M`; the scalar factor `D` tracks the determinant scale `det(D·M) = Dⁿ·det M`. -/
def qfClearMatrix (M : List (List (DenseFrac ℚ))) : List (List (DensePoly ℚ)) × DensePoly ℚ :=
  let D := qfMatDen M
  (M.map (fun row => row.map (qfClearEntry D)), D)

/-! ### The fraction-free determinant / adjugate / inverse / solve over `ℚ(x)` (`qfDet`/`qfAdjugate`/…) -/

/-- The fraction-free determinant of a `ℚ(x)`-matrix `qfDet M`: clear `M` to `M' = D·M ∈ ℚ[x]`, run
`bareissDet M'`, and divide back by `Dⁿ`, returning `CFrac.ofPoly(bareissDet M') / CFrac.ofPoly(Dⁿ)`. -/
def qfDet (M : List (List (DenseFrac ℚ))) : DenseFrac ℚ :=
  let n := M.length
  let (M', D) := qfClearMatrix M
  let detPoly := bareissDet M'
  let Dn := cpow D n
  CCommRing.mul (CFrac.ofPoly detPoly) (CField.inv (CFrac.ofPoly Dn))

/-- The fraction-free adjugate `(adj(D·M), D)` of a `ℚ(x)`-matrix `qfAdjugate M`: clear `M` to
`M' = D·M ∈ ℚ[x]` and return the `ℚ[x]` adjugate `bareissAdjugate M'` paired with `D`; the genuine
`ℚ(x)`-adjugate is `adj(M') / Dⁿ⁻¹`. -/
def qfAdjugate (M : List (List (DenseFrac ℚ))) : List (List (DensePoly ℚ)) × DensePoly ℚ :=
  let (M', D) := qfClearMatrix M
  (bareissAdjugate M', D)

/-- The fraction-free inverse representation of a `ℚ(x)`-matrix `qfInv M = (det(M'), D·adj(M'))` with
`M' = D·M ∈ ℚ[x]`: a pair of flat `ℚ[x]` polynomials with `M⁻¹[i][j] = (D·adj(M'))[i][j] / det(M')`,
one shared denominator `det(M')`. -/
def qfInv (M : List (List (DenseFrac ℚ))) : DensePoly ℚ × List (List (DensePoly ℚ)) :=
  let (M', D) := qfClearMatrix M
  let detPoly := bareissDet M'
  let adjPoly := bareissAdjugate M'
  (detPoly, adjPoly.map (fun row => row.map (fun e => cmul D e)))

/-- A single `ℚ(x)` entry of the fraction-free inverse `qfInvEntry M i j = (D·adj(M'))[i][j] /
det(M') : DenseFrac ℚ`, reading the `(i, j)` entry of `qfInv` back into `ℚ(x)`. -/
def qfInvEntry (M : List (List (DenseFrac ℚ))) (i j : ℕ) : DenseFrac ℚ :=
  let dn := qfInv M
  CCommRing.mul (CFrac.ofPoly (polyMatGet dn.2 i j)) (CField.inv (CFrac.ofPoly dn.1))

/-- The fraction-free Cramer solve of `M·x = b` over `ℚ(x)` `qfSolve M b`: clear `M` to `M' = D·M` and
the rhs to `D·b`, then run `bareissSolve M' (D·b)`, giving `x = (det M'·x)/det M'` with one shared
denominator. -/
def qfSolve (M : List (List (DenseFrac ℚ))) (b : List (DenseFrac ℚ)) :
    DensePoly ℚ × List (DensePoly ℚ) :=
  let (M', D) := qfClearMatrix M
  let b' := b.map (qfClearEntry D)
  bareissSolve M' b'

end DensePoly

end DeepWiki.SymbolicIntegration
