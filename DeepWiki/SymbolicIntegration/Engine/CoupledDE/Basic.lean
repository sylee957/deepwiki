import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.ComputableAlgebra.PolyEngine

/-! # The base coupled differential system

The real form `(Dy₁; Dy₂) + [[f₁, a·f₂], [f₂, f₁]]·(y₁; y₂) = (g₁; g₂)` of `Dy + f·y = g` over `K(√a)`.
`cCoupledDESystem` solves the base system over `k = ℚ(x)` by a degree-bounded ansatz reduced to a
single ℚ-linear solve; cleared-check bridges lift passing self-checks to `ℚ[X]` identities. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

namespace DensePoly

/-! ### The base coupled differential system over ℚ(x) (`cCoupledDESystem`)

Solve `(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]](y₁; y₂) = (z₁; z₂)` over `k = ℚ(x)`, `D = d/dx`, for
polynomial data, via a degree-`d` ansatz whose residual coefficients form one ℚ-linear solve. -/

/-- `mulMatrixQ m d nrows`: the `nrows × (d+1)` ℚ-matrix of multiplication by a polynomial in any
`CPoly` representation on the degree-`d` ansatz; entry `(r,i) = coeff(m, r−i)`. -/
def mulMatrixQ {P : Type → Type} [CPoly P] (m : P ℚ) (d nrows : ℕ) : List (List ℚ) :=
  (List.range nrows).map (fun r =>
    (List.range (d + 1)).map (fun i =>
      if r ≥ i then CPoly.coeff m (r - i) else 0))

/-- `derivMatrixQ d nrows`: the `nrows × (d+1)` ℚ-matrix of `D = d/dx` on the degree-`d` ansatz;
entry `(r,i) = i` when `i = r+1`, else `0`. -/
def derivMatrixQ (d nrows : ℕ) : List (List ℚ) :=
  (List.range nrows).map (fun r =>
    (List.range (d + 1)).map (fun i => if (i : ℕ) = r + 1 then ((i : ℚ)) else (0 : ℚ)))

/-- `matAddQ A B`: entrywise sum of two equally-shaped ℚ-matrices. -/
def matAddQ (A B : List (List ℚ)) : List (List ℚ) :=
  List.zipWith (fun ra rb => List.zipWith (· + ·) ra rb) A B

/-- `hcatQ A B`: horizontal block-concatenation of two ℚ-matrices (append each row of `B` to the
corresponding row of `A`). -/
def hcatQ (A B : List (List ℚ)) : List (List ℚ) :=
  List.zipWith (· ++ ·) A B

/-- A `mulMatrixQ` row within range is exactly `d + 1` entries wide. -/
theorem mulMatrixQ_row_len {P : Type → Type} [CPoly P] (b : P ℚ) (d nrows r : ℕ)
    (hr : r < nrows) :
    ((mulMatrixQ b d nrows).getD r []).length = d + 1 := by
  rw [mulMatrixQ, getD_lt_gen _ r [] (by rw [List.length_map, List.length_range]; exact hr),
    List.getElem_map]
  simp

/-- A `derivMatrixQ` row within range is exactly `d + 1` entries wide. -/
theorem derivMatrixQ_row_len (d nrows r : ℕ) (hr : r < nrows) :
    ((derivMatrixQ d nrows).getD r []).length = d + 1 := by
  rw [derivMatrixQ, getD_lt_gen _ r [] (by rw [List.length_map, List.length_range]; exact hr),
    List.getElem_map]
  simp

/-- `getD` row of `matAddQ A B` within both inputs is the rowwise `zipWith (+)`. -/
theorem matAddQ_getD_row (A B : List (List ℚ)) (r : ℕ) (hA : r < A.length) (hB : r < B.length) :
    (matAddQ A B).getD r [] = List.zipWith (· + ·) (A.getD r []) (B.getD r []) := by
  rw [matAddQ, getD_lt_gen _ r [] (by rw [List.length_zipWith]; omega), List.getElem_zipWith,
    getD_lt_gen A r [] hA, getD_lt_gen B r [] hB]

/-- `getD` row of `hcatQ A B` within both inputs is the append of the two rows. -/
theorem hcatQ_getD_row (A B : List (List ℚ)) (r : ℕ) (hA : r < A.length) (hB : r < B.length) :
    (hcatQ A B).getD r [] = A.getD r [] ++ B.getD r [] := by
  rw [hcatQ, getD_lt_gen _ r [] (by rw [List.length_zipWith]; omega), List.getElem_zipWith,
    getD_lt_gen A r [] hA, getD_lt_gen B r [] hB]

/-- `mulMatrixQ b d nrows` has exactly `nrows` rows. -/
theorem mulMatrixQ_len {P : Type → Type} [CPoly P] (b : P ℚ) (d nrows : ℕ) :
    (mulMatrixQ b d nrows).length = nrows := by
  rw [mulMatrixQ, List.length_map, List.length_range]

/-- `derivMatrixQ d nrows` has exactly `nrows` rows. -/
theorem derivMatrixQ_len (d nrows : ℕ) : (derivMatrixQ d nrows).length = nrows := by
  rw [derivMatrixQ, List.length_map, List.length_range]

/-- `matAddQ A B` has one row for each aligned pair of input rows. -/
theorem matAddQ_len (A B : List (List ℚ)) : (matAddQ A B).length = min A.length B.length := by
  rw [matAddQ, List.length_zipWith]

/-- Assemble and solve the coupled system using explicit degree, scaling, and normalization operations. -/
def cCoupledDESystemWith {P : Type → Type} [CPoly P] [CLinearSolve ℚ]
    (polyDeg : P ℚ → ℕ) (polyScale : ℚ → P ℚ → P ℚ) (polyNorm : P ℚ → P ℚ)
    (a : ℚ) (b1 b2 z1 z2 : P ℚ) (d : ℕ) :
    Option (P ℚ × P ℚ) :=
  -- choose enough rows: any residual coefficient lives below this degree.
  let degs : List ℕ := [polyDeg b1 + d, polyDeg b2 + d, polyDeg z1, polyDeg z2, d]
  let nrows : ℕ := (degs.foldl max 0) + 2
  -- the four polynomial-multiplication / derivation coefficient blocks, each `nrows × (d+1)`.
  let Dblk := derivMatrixQ d nrows
  let B1 := mulMatrixQ b1 d nrows
  let B2 := mulMatrixQ b2 d nrows
  let aB2 := mulMatrixQ (polyScale a b2) d nrows
  -- row 1: `(D + b₁)·u + (a·b₂)·v`; row 2: `b₂·u + (D + b₁)·v`.
  let row1u := matAddQ Dblk B1
  let row1v := aB2
  let row2u := B2
  let row2v := matAddQ Dblk B1
  let M : List (List ℚ) := hcatQ row1u row1v ++ hcatQ row2u row2v
  -- right-hand side: the `z₁` then `z₂` coefficients (length `nrows` each).
  let rhs : List ℚ := CPoly.coeffs z1 nrows ++ CPoly.coeffs z2 nrows
  match CLinearSolve.solveUnique M rhs (2 * (d + 1)) with
  | none => none
  | some sol =>
    let y1 : P ℚ := CPoly.ofFn (d + 1) (fun i => sol.getD i 0)
    let y2 : P ℚ := CPoly.ofFn (d + 1) (fun i => sol.getD ((d + 1) + i) 0)
    some (polyNorm y1, polyNorm y2)

/-- `cCoupledDESystem a b1 b2 z1 z2 d` (`D = d/dx`): in any `CPolyEngine` representation, solve
`(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]]·(y₁; y₂) = (z₁; z₂)` for degree-`≤ d` polynomials via one
abstract unique linear solve (`CLinearSolve.solveUnique`). Returns `some (y₁, y₂)` or `none`. -/
def cCoupledDESystem {P : Type → Type} [CPoly P] [CPolyEngine P] [CLinearSolve ℚ]
    (a : ℚ) (b1 b2 z1 z2 : P ℚ) (d : ℕ) : Option (P ℚ × P ℚ) :=
  cCoupledDESystemWith CPolyEngine.cdeg CPolyEngine.scale CPolyEngine.cnorm
    a b1 b2 z1 z2 d

/-- The generic coupled solver specializes definitionally to the original dense-list computation. -/
theorem cCoupledDESystem_dense_eq [CLinearSolve ℚ]
    (a : ℚ) (b1 b2 z1 z2 : DensePoly ℚ) (d : ℕ) :
    cCoupledDESystem a b1 b2 z1 z2 d =
      cCoupledDESystemWith cdeg cscale cnorm a b1 b2 z1 z2 d := rfl

example :
    cCoupledDESystem (-1)
        (CPoly.SparsePoly.ofList [] : CPoly.SparsePoly ℚ)
        (CPoly.SparsePoly.ofList [(0, -2), (1, 4)])
        (CPoly.SparsePoly.ofList [(0, 2), (2, -8)])
        (CPoly.SparsePoly.ofList [(0, 4), (1, -4)]) 1
      = some (CPoly.SparsePoly.ofList [(0, -1)],
          CPoly.SparsePoly.ofList [(0, 1), (1, 2)]) := by
  native_decide

end DensePoly

open DensePoly

/-- `xQ = x ∈ ℚ[x]` as a `DensePoly ℚ` (low→high `[0, 1]`). -/
def xQ : DensePoly ℚ := [0, 1]

/-- Worked base coupled-system datum `coupledExB2 = 4x−2` (`b₁ = 0`, `z₁ = 2−8x²`, `z₂ = 4−4x`,
`a = −1`; solution `(s₁, s₂) = (−1, 2x+1)`). -/
def coupledExB2 : DensePoly ℚ := [-2, 4]          -- 4x − 2
/-- Worked base system `coupledExZ1 = 2 − 8x²` (low→high). -/
def coupledExZ1 : DensePoly ℚ := [2, 0, -8]       -- 2 − 8x²
/-- Worked base system `coupledExZ2 = 4 − 4x` (low→high). -/
def coupledExZ2 : DensePoly ℚ := [4, -4]          -- 4 − 4x

/-- `coupledClearedCheck a b1 b2 z1 z2 y1 y2`: in any `CPolyEngine` representation, test whether
`(y₁, y₂)` solves the base coupled system by checking both cleared residuals for zero. -/
def coupledClearedCheck {P : Type → Type} [CPoly P] [CPolyEngine P]
    (a : ℚ) (b1 b2 z1 z2 y1 y2 : P ℚ) : Bool :=
  let r1 := CPolyEngine.sub
    (CPolyEngine.add
      (CPolyEngine.add (CPolyEngine.deriv y1) (CPolyEngine.mul b1 y1))
      (CPolyEngine.scale a (CPolyEngine.mul b2 y2))) z1
  let r2 := CPolyEngine.sub
    (CPolyEngine.add
      (CPolyEngine.add (CPolyEngine.deriv y2) (CPolyEngine.mul b2 y1))
      (CPolyEngine.mul b1 y2)) z2
  CPolyEngine.cisZero r1 && CPolyEngine.cisZero r2

/-- The generic cleared check specializes definitionally to the original dense-list computation. -/
theorem coupledClearedCheck_dense_eq (a : ℚ) (b1 b2 z1 z2 y1 y2 : DensePoly ℚ) :
    coupledClearedCheck a b1 b2 z1 z2 y1 y2 =
      let r1 := csub (cadd (cadd (cderiv y1) (cmul b1 y1)) (cscale a (cmul b2 y2))) z1
      let r2 := csub (cadd (cadd (cderiv y2) (cmul b2 y1)) (cmul b1 y2)) z2
      cisZero r1 && cisZero r2 := rfl

example :
    coupledClearedCheck (-1)
      (CPoly.SparsePoly.ofList [] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(0, -2), (1, 4)])
      (CPoly.SparsePoly.ofList [(0, 2), (2, -8)])
      (CPoly.SparsePoly.ofList [(0, 4), (1, -4)])
      (CPoly.SparsePoly.ofList [(0, -1)])
      (CPoly.SparsePoly.ofList [(0, 1), (1, 2)]) = true := by
  native_decide

/-! ### Base coupled-system soundness from the cleared check

The bridge `coupledClearedCheck = true ⟹ the two field identities over ℚ[X]`
(`coupledClearedCheck_sound`) uses only `LawfulCPolyEngine` denotation laws. The check is dischargeable
through the lawful abstract linear-solver soundness law, so the `*_of_check` lemmas here are the
self-certifying intermediate. -/

/-- A passing generic `coupledClearedCheck` gives the two base-system identities under `CPoly.toPoly`. -/
theorem coupledClearedCheck_sound {P : Type → Type} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{0,0} P] (a : ℚ) (b1 b2 z1 z2 y1 y2 : P ℚ)
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (CPoly.toPoly y1) + CPoly.toPoly b1 * CPoly.toPoly y1
        + Polynomial.C a * (CPoly.toPoly b2 * CPoly.toPoly y2) = CPoly.toPoly z1 ∧
      Polynomial.derivative (CPoly.toPoly y2) + CPoly.toPoly b2 * CPoly.toPoly y1
        + CPoly.toPoly b1 * CPoly.toPoly y2 = CPoly.toPoly z2 := by
  rw [coupledClearedCheck, Bool.and_eq_true] at hcheck
  obtain ⟨h1, h2⟩ := hcheck
  rw [LawfulCPolyEngine.cisZero_iff] at h1 h2
  simp only [CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_add,
    LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_scale,
    LawfulCPolyEngine.toPoly_deriv, toR_eq_toK, CFieldSpec.toK_rat] at h1 h2
  refine ⟨?_, ?_⟩
  · linear_combination h1
  · linear_combination h2

/-- `cCoupledDESystem_sound_of_check`: if `cCoupledDESystem a b1 b2 z1 z2 d = some (y1, y2)` and the
returned pair passes `coupledClearedCheck`, then `(y₁, y₂)` solves the base coupled system at the `ℚ[X]`
level (composition with `coupledClearedCheck_sound`). -/
theorem cCoupledDESystem_sound_of_check [CLinearSolve ℚ]
    (a : ℚ) (b1 b2 z1 z2 : DensePoly ℚ) (d : ℕ)
    (y1 y2 : DensePoly ℚ)
    (_hsome : cCoupledDESystem a b1 b2 z1 z2 d = some (y1, y2))
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (toPoly y1) + toPoly b1 * toPoly y1
        + Polynomial.C a * (toPoly b2 * toPoly y2) = toPoly z1 ∧
      Polynomial.derivative (toPoly y2) + toPoly b2 * toPoly y1
        + toPoly b1 * toPoly y2 = toPoly z2 :=
  by
    simpa only [toPoly_list_eq] using
      (coupledClearedCheck_sound (P := DensePoly) a b1 b2 z1 z2 y1 y2 hcheck)

-- **Sanity print.** The worked base solve returns `(−1, 2x+1)`.
#eval (cCoupledDESystem (-1) ([] : DensePoly ℚ) coupledExB2 coupledExZ1 coupledExZ2 1).map
  (fun p => ((p.1 : List ℚ), (p.2 : List ℚ)))

/-- `coupledDESystem_example`: the base coupled system (`a = −1`)
`(Dy₁; Dy₂) + [[0, −(4x−2)], [4x−2, 0]]·(y₁; y₂) = (2−8x²; 4−4x)` solves to `(s₁, s₂) = (−1, 2x+1)`,
verified by `coupledClearedCheck`. -/
theorem coupledDESystem_example :
    (match cCoupledDESystem (-1) ([] : DensePoly ℚ) coupledExB2 coupledExZ1 coupledExZ2 1 with
      | some (y1, y2) =>
          coupledClearedCheck (-1) [] coupledExB2 coupledExZ1 coupledExZ2 y1 y2
      | none => false) = true := by native_decide

#print axioms coupledDESystem_example
/-! ### Axiom audit of the base soundness signature -/

#print axioms coupledClearedCheck_sound

end DeepWiki.SymbolicIntegration
