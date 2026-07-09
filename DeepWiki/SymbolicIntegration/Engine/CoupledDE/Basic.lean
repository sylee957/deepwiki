import DeepWiki.SymbolicIntegration.Engine.Parametric

/-! # The base coupled differential system

The real form `(Dy₁; Dy₂) + [[f₁, a·f₂], [f₂, f₁]]·(y₁; y₂) = (g₁; g₂)` of `Dy + f·y = g` over `K(√a)`.
`cCoupledDESystem` solves the base system over `k = ℚ(x)` by a degree-bounded ansatz reduced to a
single ℚ-linear solve; cleared-check bridges lift passing self-checks to `ℚ[X]` identities. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

namespace CPoly

/-! ### The base coupled differential system over ℚ(x) (`cCoupledDESystem`)

Solve `(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]](y₁; y₂) = (z₁; z₂)` over `k = ℚ(x)`, `D = d/dx`, for
polynomial data, via a degree-`d` ansatz whose residual coefficients form one ℚ-linear solve. -/

/-- `padCoeffsQ p n`: low→high ℚ-coefficient list of `p`, truncated/zero-extended to `n` entries. -/
def padCoeffsQ (p : CPoly ℚ) (n : ℕ) : List ℚ :=
  (List.range n).map (fun i => (p : List ℚ).getD i 0)

/-- `mulMatrixQ m d nrows`: the `nrows × (d+1)` ℚ-matrix of multiplication by `m` on the degree-`d`
ansatz; entry `(r,i) = coeff(m, r−i)`. -/
def mulMatrixQ (m : CPoly ℚ) (d nrows : ℕ) : List (List ℚ) :=
  (List.range nrows).map (fun r =>
    (List.range (d + 1)).map (fun i =>
      if r ≥ i then (m : List ℚ).getD (r - i) 0 else 0))

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
theorem mulMatrixQ_row_len (b : CPoly ℚ) (d nrows r : ℕ) (hr : r < nrows) :
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
theorem mulMatrixQ_len (b : CPoly ℚ) (d nrows : ℕ) : (mulMatrixQ b d nrows).length = nrows := by
  rw [mulMatrixQ, List.length_map, List.length_range]

/-- `derivMatrixQ d nrows` has exactly `nrows` rows. -/
theorem derivMatrixQ_len (d nrows : ℕ) : (derivMatrixQ d nrows).length = nrows := by
  rw [derivMatrixQ, List.length_map, List.length_range]

/-- `matAddQ A B` has one row for each aligned pair of input rows. -/
theorem matAddQ_len (A B : List (List ℚ)) : (matAddQ A B).length = min A.length B.length := by
  rw [matAddQ, List.length_zipWith]

/-- `cCoupledDESystem a b1 b2 z1 z2 d` (`D = d/dx`): solve `(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]]·(y₁; y₂)
= (z₁; z₂)` for `y₁, y₂ ∈ ℚ[x]` of degree `≤ d`, via the ansatz residuals as one ℚ-linear solve
(`cConstSolveUniqueQ`). Returns `some (y₁, y₂)` or `none`. -/
def cCoupledDESystem (a : ℚ) (b1 b2 z1 z2 : CPoly ℚ) (d : ℕ) :
    Option (CPoly ℚ × CPoly ℚ) :=
  -- choose enough rows: any residual coefficient lives below this degree.
  let degs : List ℕ := [cdeg b1 + d, cdeg b2 + d, cdeg z1, cdeg z2, d]
  let nrows : ℕ := (degs.foldl max 0) + 2
  -- the four polynomial-multiplication / derivation coefficient blocks, each `nrows × (d+1)`.
  let Dblk := derivMatrixQ d nrows
  let B1 := mulMatrixQ b1 d nrows
  let B2 := mulMatrixQ b2 d nrows
  let aB2 := mulMatrixQ (cscale a b2) d nrows
  -- row 1: `(D + b₁)·u + (a·b₂)·v`; row 2: `b₂·u + (D + b₁)·v`.
  let row1u := matAddQ Dblk B1
  let row1v := aB2
  let row2u := B2
  let row2v := matAddQ Dblk B1
  let M : List (List ℚ) := hcatQ row1u row1v ++ hcatQ row2u row2v
  -- right-hand side: the `z₁` then `z₂` coefficients (length `nrows` each).
  let rhs : List ℚ := padCoeffsQ z1 nrows ++ padCoeffsQ z2 nrows
  match cConstSolveUniqueQ M rhs (2 * (d + 1)) with
  | none => none
  | some sol =>
    let y1 : CPoly ℚ := (List.range (d + 1)).map (fun i => sol.getD i 0)
    let y2 : CPoly ℚ := (List.range (d + 1)).map (fun i => sol.getD ((d + 1) + i) 0)
    some (cnorm y1, cnorm y2)

end CPoly

open CPoly

/-- `xQ = x ∈ ℚ[x]` as a `CPoly ℚ` (low→high `[0, 1]`). -/
def xQ : CPoly ℚ := [0, 1]

/-- Worked base coupled-system datum `coupledExB2 = 4x−2` (`b₁ = 0`, `z₁ = 2−8x²`, `z₂ = 4−4x`,
`a = −1`; solution `(s₁, s₂) = (−1, 2x+1)`). -/
def coupledExB2 : CPoly ℚ := [-2, 4]          -- 4x − 2
/-- Worked base system `coupledExZ1 = 2 − 8x²` (low→high). -/
def coupledExZ1 : CPoly ℚ := [2, 0, -8]       -- 2 − 8x²
/-- Worked base system `coupledExZ2 = 4 − 4x` (low→high). -/
def coupledExZ2 : CPoly ℚ := [4, -4]          -- 4 − 4x

/-- `coupledClearedCheck a b1 b2 z1 z2 y1 y2`: `true` iff `(y₁, y₂)` solves the base coupled system over
ℚ(x), i.e. both cleared residuals `Dyᵢ + … − zᵢ` are `cisZero`. -/
def coupledClearedCheck (a : ℚ) (b1 b2 z1 z2 y1 y2 : CPoly ℚ) : Bool :=
  let r1 := csub (cadd (cadd (cderivQ y1) (cmul b1 y1)) (cscale a (cmul b2 y2))) z1
  let r2 := csub (cadd (cadd (cderivQ y2) (cmul b2 y1)) (cmul b1 y2)) z2
  cisZero r1 && cisZero r2

/-! ### Base coupled-system soundness from the cleared check

The bridge `coupledClearedCheck = true ⟹ the two field identities over ℚ[X]`
(`coupledClearedCheck_sound`), via `cisZeroG_iff` and the `toPoly` ring/derivation homs. The check is
dischargeable through `cConstSolveUniqueQ_sound`, so the `*_of_check` lemmas here are the
self-certifying intermediate. -/

/-- `coupledClearedCheck_sound`: if `coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true` then `(y₁, y₂)`
solves the base coupled system at the `ℚ[X]` level — `D(y₁) + b₁·y₁ + C a·(b₂·y₂) = z₁` and
`D(y₂) + b₂·y₁ + b₁·y₂ = z₂` (`D = Polynomial.derivative`). -/
theorem coupledClearedCheck_sound (a : ℚ) (b1 b2 z1 z2 y1 y2 : CPoly ℚ)
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (toPoly y1) + toPoly b1 * toPoly y1
        + Polynomial.C a * (toPoly b2 * toPoly y2) = toPoly z1 ∧
      Polynomial.derivative (toPoly y2) + toPoly b2 * toPoly y1
        + toPoly b1 * toPoly y2 = toPoly z2 := by
  rw [coupledClearedCheck, Bool.and_eq_true] at hcheck
  obtain ⟨h1, h2⟩ := hcheck
  rw [cisZeroG_iff] at h1 h2
  refine ⟨?_, ?_⟩
  · have := h1
    simp only [denote, CFieldSpec.toK, id_eq, sub_eq_zero] at this
    linear_combination this
  · have := h2
    simp only [denote, sub_eq_zero] at this
    linear_combination this

/-- `cCoupledDESystem_sound_of_check`: if `cCoupledDESystem a b1 b2 z1 z2 d = some (y1, y2)` and the
returned pair passes `coupledClearedCheck`, then `(y₁, y₂)` solves the base coupled system at the `ℚ[X]`
level (composition with `coupledClearedCheck_sound`). -/
theorem cCoupledDESystem_sound_of_check (a : ℚ) (b1 b2 z1 z2 : CPoly ℚ) (d : ℕ)
    (y1 y2 : CPoly ℚ)
    (_hsome : cCoupledDESystem a b1 b2 z1 z2 d = some (y1, y2))
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (toPoly y1) + toPoly b1 * toPoly y1
        + Polynomial.C a * (toPoly b2 * toPoly y2) = toPoly z1 ∧
      Polynomial.derivative (toPoly y2) + toPoly b2 * toPoly y1
        + toPoly b1 * toPoly y2 = toPoly z2 :=
  coupledClearedCheck_sound a b1 b2 z1 z2 y1 y2 hcheck

-- **Sanity print.** The worked base solve returns `(−1, 2x+1)`.
#eval (cCoupledDESystem (-1) ([] : CPoly ℚ) coupledExB2 coupledExZ1 coupledExZ2 1).map
  (fun p => ((p.1 : List ℚ), (p.2 : List ℚ)))

/-- `coupledDESystem_example`: the base coupled system (`a = −1`)
`(Dy₁; Dy₂) + [[0, −(4x−2)], [4x−2, 0]]·(y₁; y₂) = (2−8x²; 4−4x)` solves to `(s₁, s₂) = (−1, 2x+1)`,
verified by `coupledClearedCheck`. -/
theorem coupledDESystem_example :
    (match cCoupledDESystem (-1) ([] : CPoly ℚ) coupledExB2 coupledExZ1 coupledExZ2 1 with
      | some (y1, y2) =>
          coupledClearedCheck (-1) [] coupledExB2 coupledExZ1 coupledExZ2 y1 y2
      | none => false) = true := by native_decide

#print axioms coupledDESystem_example
/-! ### Restatement of the base soundness signature -/

-- ★ Base coupled-system soundness, `native_decide`-free: a self-certifying `cCoupledDESystem` solve gives
-- the two `ℚ[X]` row identities `D(y₁) + b₁y₁ + a·b₂y₂ = z₁`, `D(y₂) + b₂y₁ + b₁y₂ = z₂`.
example (a : ℚ) (b1 b2 z1 z2 y1 y2 : CPoly ℚ) (d : ℕ)
    (hsome : cCoupledDESystem a b1 b2 z1 z2 d = some (y1, y2))
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (toPoly y1) + toPoly b1 * toPoly y1
        + Polynomial.C a * (toPoly b2 * toPoly y2) = toPoly z1 ∧
      Polynomial.derivative (toPoly y2) + toPoly b2 * toPoly y1
        + toPoly b1 * toPoly y2 = toPoly z2 :=
  cCoupledDESystem_sound_of_check a b1 b2 z1 z2 d y1 y2 hsome hcheck

#print axioms coupledClearedCheck_sound

end DeepWiki.SymbolicIntegration
