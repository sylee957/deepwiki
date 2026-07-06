import DeepWiki.SymbolicIntegration.Computable.Parametric

/-! # The coupled differential system and the tangent RDE cancellation

The real form `(Dy₁; Dy₂) + [[f₁, a·f₂], [f₂, f₁]]·(y₁; y₂) = (g₁; g₂)` of `Dy + f·y = g` over `K(√a)`.
`cCoupledDESystem` solves the base system over `k = ℚ(x)` by a degree-bounded ansatz reduced to one
ℚ-linear solve; `cCoupledDECancelTan` is the hypertangent cancellation (`t = tan(x)`, `Dt = t²+1`),
solving degree-by-degree. Cleared-check bridges lift passing self-checks to `ℚ[X]` / `ℚ[x][t]` identities. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

namespace CPolyG

/-! ### The base coupled differential system over ℚ(x) (`cCoupledDESystem`)

Solve `(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]](y₁; y₂) = (z₁; z₂)` over `k = ℚ(x)`, `D = d/dx`, for
polynomial data, via a degree-`d` ansatz whose residual coefficients form one ℚ-linear solve. -/

/-- `padCoeffsQ p n`: low→high ℚ-coefficient list of `p`, truncated/zero-extended to `n` entries. -/
def padCoeffsQ (p : CPolyG ℚ) (n : ℕ) : List ℚ :=
  (List.range n).map (fun i => (p : List ℚ).getD i 0)

/-- `mulMatrixQ m d nrows`: the `nrows × (d+1)` ℚ-matrix of multiplication by `m` on the degree-`d`
ansatz; entry `(r,i) = coeff(m, r−i)`. -/
def mulMatrixQ (m : CPolyG ℚ) (d nrows : ℕ) : List (List ℚ) :=
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
theorem mulMatrixQ_row_len (b : CPolyG ℚ) (d nrows r : ℕ) (hr : r < nrows) :
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
theorem mulMatrixQ_len (b : CPolyG ℚ) (d nrows : ℕ) : (mulMatrixQ b d nrows).length = nrows := by
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
def cCoupledDESystem (a : ℚ) (b1 b2 z1 z2 : CPolyG ℚ) (d : ℕ) :
    Option (CPolyG ℚ × CPolyG ℚ) :=
  -- choose enough rows: any residual coefficient lives below this degree.
  let degs : List ℕ := [cdegG b1 + d, cdegG b2 + d, cdegG z1, cdegG z2, d]
  let nrows : ℕ := (degs.foldl max 0) + 2
  -- the four polynomial-multiplication / derivation coefficient blocks, each `nrows × (d+1)`.
  let Dblk := derivMatrixQ d nrows
  let B1 := mulMatrixQ b1 d nrows
  let B2 := mulMatrixQ b2 d nrows
  let aB2 := mulMatrixQ (cscaleG a b2) d nrows
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
    let y1 : CPolyG ℚ := (List.range (d + 1)).map (fun i => sol.getD i 0)
    let y2 : CPolyG ℚ := (List.range (d + 1)).map (fun i => sol.getD ((d + 1) + i) 0)
    some (cnormG y1, cnormG y2)

/-! ### The tangent RDE cancellation `cCoupledDECancelTan`

`t = tan(x)`, `Dt = t²+1`, `η = 1`. The cancellation case of `Dq + b·q = c` solves the `t`-polynomial
coupled system (`a = −1`) for `q₁, q₂ ∈ k[t]` degree-by-degree from the top: each level a base
`cCoupledDESystem` solve, then a `c₁, c₂` reduction dropping the degree. Coefficients in `k = ℚ(x)`. -/

/-- `tanDeriv p`: tangent monomial derivation `D = ∂/∂x + (t²+1)·∂/∂t` on a `t`-polynomial over
`ℚ[x]` (`Dt = t²+1`). -/
def tanDeriv (p : List (CPolyG ℚ)) : List (CPolyG ℚ) :=
  -- κ_D: coefficientwise d/dx
  let kappa : List (CPolyG ℚ) := p.map cderivQ
  -- (t²+1)·dp/dt : shift the formal t-derivative by t² and by t⁰.
  let dpdt : List (CPolyG ℚ) := (p.drop 1).zipIdx.map (fun (c, i) => cscaleG ((i : ℚ) + 1) c)
  -- multiply dpdt by (t²+1): result_k = dpdt_{k-2} + dpdt_k
  let mulDt : List (CPolyG ℚ) :=
    (List.range (dpdt.length + 2)).map (fun k =>
      let lo : CPolyG ℚ := if k ≥ 2 then dpdt.getD (k - 2) [] else []
      let hi : CPolyG ℚ := dpdt.getD k []
      caddG lo hi)
  -- add κ_D and (t²+1)dp/dt coefficientwise (over the t-degree).
  let n := max kappa.length mulDt.length
  (List.range n).map (fun k => caddG (kappa.getD k []) (mulDt.getD k []))

/-- `tcoeff p m`: the `tᵐ`-coefficient (in `ℚ(x)`) of a `t`-polynomial, `[]` (zero) past the end. -/
def tcoeff (p : List (CPolyG ℚ)) (m : ℕ) : CPolyG ℚ := p.getD m []

/-- `tdeg p`: the `t`-degree (highest index with a nonzero coefficient), `0` for the zero polynomial. -/
def tdeg (p : List (CPolyG ℚ)) : ℕ :=
  ((p.zipIdx.filter (fun (c, _) => ¬ cisZeroG c)).map (fun (_, i) => i)).foldl max 0

/-- `t`-polynomial zero test `tisZero p`: every `ℚ(x)`-coefficient is zero. -/
def tisZero (p : List (CPolyG ℚ)) : Bool := p.all cisZeroG

/-- `tshiftScale s m = s·tᵐ`: the single-term `t`-polynomial `[0,…,0,s]` with `m` leading zeros. -/
def tshiftScale (s : CPolyG ℚ) (m : ℕ) : List (CPolyG ℚ) :=
  (List.replicate m ([] : CPolyG ℚ)) ++ [s]

/-- `tsub p q`: coefficientwise subtraction `pₖ − qₖ` of `t`-polynomials over `ℚ(x)`. -/
def tsub (p q : List (CPolyG ℚ)) : List (CPolyG ℚ) :=
  let n := max p.length q.length
  (List.range n).map (fun k => csubG (p.getD k []) (q.getD k []))

/-- `tadd p q`: coefficientwise addition `pₖ + qₖ` of `t`-polynomials over `ℚ(x)`. -/
def tadd (p q : List (CPolyG ℚ)) : List (CPolyG ℚ) :=
  let n := max p.length q.length
  (List.range n).map (fun k => caddG (p.getD k []) (q.getD k []))

/-- `cscaleListQ s p`: scale every `ℚ[x]`-coefficient of the `t`-polynomial `p` by `s ∈ ℚ`. -/
def cscaleListQ (s : ℚ) (p : List (CPolyG ℚ)) : List (CPolyG ℚ) := p.map (cscaleG s)

/-! #### Projection mod `t²+1` and division by `t − √−1` over `k(√−1)[t]`

A `k(√−1)`-element is a pair `(re, im)` of `CPolyG ℚ` (`re + im·√−1`, `√−1² = −1`); a `k(√−1)[t]`-poly
is a `t`-list of such pairs. The box needs evaluation at `t = √−1` (reduce mod `t²+1`) and exact
division by `t − √−1`. -/

/-- `evalAtI p = (re, im)`: evaluate a `k[t]`-polynomial at `t = √−1`, `p(√−1) = re + im·√−1`
(Horner mod `t²+1`). -/
def evalAtI (p : List (CPolyG ℚ)) : CPolyG ℚ × CPolyG ℚ :=
  p.foldr (fun (a : CPolyG ℚ) (acc : CPolyG ℚ × CPolyG ℚ) =>
    -- acc = (u, v) standing for u + v√−1; new = a + √−1·acc = a + (u + v√−1)√−1 = (a − v) + u√−1.
    (caddG a (cscaleG (-1) acc.2), acc.1)) ([], [])

/-- `cmulI (a,b) (c,d) = (ac − bd, ad + bc)`: `k(√−1)`-multiplication on pairs (`√−1² = −1`). -/
def cmulI (x y : CPolyG ℚ × CPolyG ℚ) : CPolyG ℚ × CPolyG ℚ :=
  (csubG (cmulG x.1 y.1) (cmulG x.2 y.2), caddG (cmulG x.1 y.2) (cmulG x.2 y.1))

/-- `csubI (a,b) (c,d) = (a−c, b−d)`: `k(√−1)`-subtraction on pairs. -/
def csubI (x y : CPolyG ℚ × CPolyG ℚ) : CPolyG ℚ × CPolyG ℚ :=
  (csubG x.1 y.1, csubG x.2 y.2)

/-- `cisZeroI (a,b)`: `k(√−1)`-zero test on a pair (both parts vanish). -/
def cisZeroI (x : CPolyG ℚ × CPolyG ℚ) : Bool := cisZeroG x.1 && cisZeroG x.2

/-- `divByTminusI p = q` with `p = (t − √−1)·q`: synthetic (Ruffini) division of a `k(√−1)[t]`-poly
by `t − √−1`, exact when `p(√−1) = 0`; the remainder is dropped. -/
def divByTminusI (p : List (CPolyG ℚ × CPolyG ℚ)) : List (CPolyG ℚ × CPolyG ℚ) :=
  let I : CPolyG ℚ × CPolyG ℚ := ([], [CField.one])     -- √−1
  -- Horner from the top: coefficients of the quotient, high→low, then reverse.
  let rec go : List (CPolyG ℚ × CPolyG ℚ) → CPolyG ℚ × CPolyG ℚ →
      List (CPolyG ℚ × CPolyG ℚ) → List (CPolyG ℚ × CPolyG ℚ)
    | [], _, acc => acc                                   -- last (lowest) coeff is the remainder, dropped
    | a :: rest, carry, acc =>
        -- current quotient coefficient = carry; next carry = a + √−1·carry.
        go rest (caddG' a (cmulI I carry)) (carry :: acc)
  -- `caddG'` on pairs:
  go (p.reverse) ([], []) [] |>.drop 0
where
  /-- pair addition for the synthetic-division carry. -/
  caddG' (x y : CPolyG ℚ × CPolyG ℚ) : CPolyG ℚ × CPolyG ℚ := (caddG x.1 y.1, caddG x.2 y.2)

/-- `cCoupledDECancelTan dbound b0 b2 c1 c2 n`: hypertangent RDE cancellation over `k = ℚ(x)`,
`t = tan(x)`, `η = 1`, `a = −1`, solving `(Dq₁; Dq₂) + [[b₀−nt, −b₂], [b₂, b₀−nt]]·(q₁; q₂) = (c₁; c₂)`
for `q₁, q₂ ∈ k[t]` of `t`-degree `≤ n` (`D = tanDeriv`). Recurses structurally on `n`: each level a
base `cCoupledDESystem` solve (ansatz degree `≤ dbound`) after evaluating the `cᵢ` at `t = √−1`, then a
`t − √−1` division dropping the degree. Returns `some (q₁, q₂)` or `none`. -/
def cCoupledDECancelTan (dbound : ℕ) (b0 b2 : CPolyG ℚ) :
    (c1 c2 : List (CPolyG ℚ)) → (n : ℕ) → Option (List (CPolyG ℚ) × List (CPolyG ℚ))
  | c1, c2, 0 =>
    -- n = 0: c₁, c₂ must be in k (degree-0 in t); solve the base coupled system directly.
    if tdeg c1 = 0 && tdeg c2 = 0 then
      match cCoupledDESystem (-1) b0 b2 (tcoeff c1 0) (tcoeff c2 0) dbound with
      | none => none
      | some (s1, s2) => some ([s1], [s2])
    else none
  | c1, c2, n + 1 =>
    let nN : ℚ := ((n : ℚ) + 1)                              -- n (as ℚ for nη scaling), η = 1
    -- z₁ + z₂√−1 = c₁(√−1) + c₂(√−1)√−1.
    let e1 := evalAtI c1                                     -- c₁(√−1) = (re, im)
    let e2 := evalAtI c2                                     -- c₂(√−1)
    -- c₂(√−1)·√−1 = (−e2.im, e2.re); z = e1 + that.
    let z1 := csubG e1.1 e2.2
    let z2 := caddG e1.2 e2.1
    -- base solve CoupledDESystem(b₀, b₂ − nη, z₁, z₂), η = 1 ⇒ shift b₂ by −(n+1).
    let b2shift := csubG b2 (cscaleG nN [CField.one])
    match cCoupledDESystem (-1) b0 b2shift z1 z2 dbound with
    | none => none
    | some (s1, s2) =>
      -- numerator of c·p: real = c₁ − z₁ + nη(s₁t + s₂); imag = c₂ − z₂ + nη(s₂t − s₁).
      -- s₁t = [0, s₁], s₂t = [0, s₂] as t-polynomials.
      let s1t : List (CPolyG ℚ) := [[], s1]
      let s2t : List (CPolyG ℚ) := [[], s2]
      let realNum := tadd (tsub c1 [z1]) (cscaleListQ nN (tadd s1t [s2]))
      let imagNum := tadd (tsub c2 [z2]) (cscaleListQ nN (tsub s2t [s1]))
      -- assemble the k(√−1)[t]-polynomial (pairs) and divide by t − √−1.
      let len := max realNum.length imagNum.length
      let cpairs : List (CPolyG ℚ × CPolyG ℚ) :=
        (List.range len).map (fun k => (realNum.getD k [], imagNum.getD k []))
      let quot := divByTminusI cpairs
      let d1 : List (CPolyG ℚ) := quot.map Prod.fst
      let d2 : List (CPolyG ℚ) := quot.map Prod.snd
      match cCoupledDECancelTan dbound b0 (caddG b2 [CField.one]) d1 d2 n with
      | none => none
      | some (h1, h2) =>
        -- return (h₁t + h₂ + s₁, h₂t − h₁ + s₂).
        let h1t : List (CPolyG ℚ) := [[]] ++ h1     -- h₁·t (shift up by one t-degree)
        let h2t : List (CPolyG ℚ) := [[]] ++ h2
        let q1 := tadd (tadd h1t h2) [s1]
        let q2 := tsub (tadd h2t [s2]) h1
        some (q1, q2)

end CPolyG

/-! ### Validation — a worked tangent example

`k = ℚ(x)`, `D = d/dx`, `t = tan(x)`. The `t`-polynomial coupled system
`(Dq₁; Dq₂) + [[−2t, −4x], [4x, −2t]]·(q₁; q₂) = (−t²+2t−8x²+1; 2(1−2x))` (`a = −1`, degree bound
`n = 2`), solved by `cCoupledDECancelTan` with `b₀ = 0`, `b₂ = 4x`; the solution is `q₁ = t − 1`,
`q₂ = 2x` (so `y₁ = (t−1)/(t²+1)`, `y₂ = 2x/(t²+1)`). -/

open CPolyG

/-- `xQ = x ∈ ℚ[x]` as a `CPolyG ℚ` (low→high `[0, 1]`). -/
def xQ : CPolyG ℚ := [0, 1]

/-- Worked base coupled-system datum `coupledExB2 = 4x−2` (`b₁ = 0`, `z₁ = 2−8x²`, `z₂ = 4−4x`,
`a = −1`; solution `(s₁, s₂) = (−1, 2x+1)`). -/
def coupledExB2 : CPolyG ℚ := [-2, 4]          -- 4x − 2
/-- Worked base system `coupledExZ1 = 2 − 8x²` (low→high). -/
def coupledExZ1 : CPolyG ℚ := [2, 0, -8]       -- 2 − 8x²
/-- Worked base system `coupledExZ2 = 4 − 4x` (low→high). -/
def coupledExZ2 : CPolyG ℚ := [4, -4]          -- 4 − 4x

/-- `coupledClearedCheck a b1 b2 z1 z2 y1 y2`: `true` iff `(y₁, y₂)` solves the base coupled system over
ℚ(x), i.e. both cleared residuals `Dyᵢ + … − zᵢ` are `cisZeroG`. -/
def coupledClearedCheck (a : ℚ) (b1 b2 z1 z2 y1 y2 : CPolyG ℚ) : Bool :=
  let r1 := csubG (caddG (caddG (cderivQ y1) (cmulG b1 y1)) (cscaleG a (cmulG b2 y2))) z1
  let r2 := csubG (caddG (caddG (cderivQ y2) (cmulG b2 y1)) (cmulG b1 y2)) z2
  cisZeroG r1 && cisZeroG r2

/-! ### Base coupled-system soundness from the cleared check

The bridge `coupledClearedCheck = true ⟹ the two field identities over ℚ[X]`
(`coupledClearedCheck_sound`), via `cisZeroG_iff` and the `toPolyG` ring/derivation homs. The check is
dischargeable through `cConstSolveUniqueQ_sound`, so the `*_of_check` lemmas here are the
self-certifying intermediate. -/

/-- `coupledClearedCheck_sound`: if `coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true` then `(y₁, y₂)`
solves the base coupled system at the `ℚ[X]` level — `D(y₁) + b₁·y₁ + C a·(b₂·y₂) = z₁` and
`D(y₂) + b₂·y₁ + b₁·y₂ = z₂` (`D = Polynomial.derivative`). -/
theorem coupledClearedCheck_sound (a : ℚ) (b1 b2 z1 z2 y1 y2 : CPolyG ℚ)
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (toPolyG y1) + toPolyG b1 * toPolyG y1
        + Polynomial.C a * (toPolyG b2 * toPolyG y2) = toPolyG z1 ∧
      Polynomial.derivative (toPolyG y2) + toPolyG b2 * toPolyG y1
        + toPolyG b1 * toPolyG y2 = toPolyG z2 := by
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
theorem cCoupledDESystem_sound_of_check (a : ℚ) (b1 b2 z1 z2 : CPolyG ℚ) (d : ℕ)
    (y1 y2 : CPolyG ℚ)
    (_hsome : cCoupledDESystem a b1 b2 z1 z2 d = some (y1, y2))
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (toPolyG y1) + toPolyG b1 * toPolyG y1
        + Polynomial.C a * (toPolyG b2 * toPolyG y2) = toPolyG z1 ∧
      Polynomial.derivative (toPolyG y2) + toPolyG b2 * toPolyG y1
        + toPolyG b1 * toPolyG y2 = toPolyG z2 :=
  coupledClearedCheck_sound a b1 b2 z1 z2 y1 y2 hcheck

-- **Sanity print** (book p.266 step 4): `CoupledDESystem(0, 4x−2, 2−8x², 4−4x) = (−1, 2x+1)`.
#eval (cCoupledDESystem (-1) ([] : CPolyG ℚ) coupledExB2 coupledExZ1 coupledExZ2 1).map
  (fun p => ((p.1 : List ℚ), (p.2 : List ℚ)))

/-- `coupledDESystem_example`: the base coupled system (`a = −1`)
`(Dy₁; Dy₂) + [[0, −(4x−2)], [4x−2, 0]]·(y₁; y₂) = (2−8x²; 4−4x)` solves to `(s₁, s₂) = (−1, 2x+1)`,
verified by `coupledClearedCheck`. -/
theorem coupledDESystem_example :
    (match cCoupledDESystem (-1) ([] : CPolyG ℚ) coupledExB2 coupledExZ1 coupledExZ2 1 with
      | some (y1, y2) =>
          coupledClearedCheck (-1) [] coupledExB2 coupledExZ1 coupledExZ2 y1 y2
      | none => false) = true := by native_decide

#print axioms coupledDESystem_example

/-! ### The `t`-polynomial bivariate bridge `toPoly2 : ℚ[x][t]`

A `t`-polynomial `p : List (CPolyG ℚ)` reads into `(ℚ[X])[X]` via `toPoly2 p = Σ_k C(toPolyG p_k)·tᵏ`.
The tangent cleared-check operations become the `ℚ[x][t]` ring operations and the derivation
`D = ∂/∂x + (t²+1)·∂/∂t`, so a passing `cancelTanClearedCheck` lifts to a genuine `ℚ[x][t]` identity. -/

open CPolyG in
/-- `toPoly2 p`: bivariate bridge `List (CPolyG ℚ) → ℚ[x][t]`, Horner over `t`,
`toPoly2 (c :: cs) = C(toPolyG c) + X·toPoly2 cs`. -/
noncomputable def toPoly2 : List (CPolyG ℚ) → Polynomial (Polynomial ℚ)
  | [] => 0
  | c :: cs => Polynomial.C (toPolyG c) + Polynomial.X * toPoly2 cs

@[simp] theorem toPoly2_nil : toPoly2 [] = 0 := rfl

@[simp] theorem toPoly2_cons (c : CPolyG ℚ) (cs : List (CPolyG ℚ)) :
    toPoly2 (c :: cs) = Polynomial.C (toPolyG c) + Polynomial.X * toPoly2 cs := rfl

/-- `toPoly2_eq_sum_getD`: `toPoly2 p = Σ_{k<N} C(toPolyG (p.getD k []))·Xᵏ` for any `N ≥ p.length`. -/
theorem toPoly2_eq_sum_getD (p : List (CPolyG ℚ)) (N : ℕ) (hN : p.length ≤ N) :
    toPoly2 p = ∑ k ∈ Finset.range N,
      Polynomial.C (toPolyG (p.getD k [])) * Polynomial.X ^ k := by
  induction p generalizing N with
  | nil =>
    simp only [toPoly2_nil, List.getD_nil, toPolyG_nil, map_zero, zero_mul, Finset.sum_const_zero]
  | cons c cs ih =>
    cases N with
    | zero => simp at hN
    | succ M =>
      rw [toPoly2_cons, Finset.sum_range_succ', ih M (by simpa using hN), Finset.mul_sum]
      simp only [List.getD_cons_succ, pow_succ, List.getD_cons_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- `getD_range_map`: `((List.range n).map f).getD k [] = f k` for `k < n`. -/
theorem getD_range_map (f : ℕ → CPolyG ℚ) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f).getD k [] = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- `getD_out`: `p.getD k [] = []` for `p.length ≤ k`. -/
theorem getD_out (p : List (CPolyG ℚ)) (k : ℕ) (hk : p.length ≤ k) : p.getD k [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl

open CPolyG in
/-- `toPoly2_eq_zero_of_tisZero`: `tisZero p = true ⟹ toPoly2 p = 0`. -/
theorem toPoly2_eq_zero_of_tisZero (p : List (CPolyG ℚ)) (h : tisZero p = true) :
    toPoly2 p = 0 := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    rw [tisZero, List.all_cons, Bool.and_eq_true] at h
    rw [toPoly2_cons, (cisZeroG_iff c).mp h.1, map_zero, ih h.2, mul_zero, add_zero]

open CPolyG in
/-- `toPoly2_tadd`: `toPoly2 (tadd p q) = toPoly2 p + toPoly2 q`. -/
theorem toPoly2_tadd (p q : List (CPolyG ℚ)) :
    toPoly2 (tadd p q) = toPoly2 p + toPoly2 q := by
  set N := max p.length q.length with hN
  rw [toPoly2_eq_sum_getD (tadd p q) N (by rw [tadd]; simp [hN]),
    toPoly2_eq_sum_getD p N (le_max_left _ _), toPoly2_eq_sum_getD q N (le_max_right _ _),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [tadd, getD_range_map _ _ _ hk, toPolyG_caddG, map_add, add_mul]

open CPolyG in
/-- `toPoly2_tsub`: `toPoly2 (tsub p q) = toPoly2 p − toPoly2 q`. -/
theorem toPoly2_tsub (p q : List (CPolyG ℚ)) :
    toPoly2 (tsub p q) = toPoly2 p - toPoly2 q := by
  set N := max p.length q.length with hN
  rw [toPoly2_eq_sum_getD (tsub p q) N (by rw [tsub]; simp [hN]),
    toPoly2_eq_sum_getD p N (le_max_left _ _), toPoly2_eq_sum_getD q N (le_max_right _ _),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [tsub, getD_range_map _ _ _ hk, toPolyG_csubG, map_sub, sub_mul]

open CPolyG in
/-- `toPoly2_coeff`: `(toPoly2 p).coeff k = toPolyG (p.getD k [])`. -/
theorem toPoly2_coeff (p : List (CPolyG ℚ)) (k : ℕ) :
    (toPoly2 p).coeff k = toPolyG (p.getD k []) := by
  induction p generalizing k with
  | nil => simp
  | cons c cs ih =>
    rw [toPoly2_cons, Polynomial.coeff_add]
    cases k with
    | zero => simp
    | succ m =>
      rw [List.getD_cons_succ, Polynomial.coeff_X_mul, ih m]
      simp

open CPolyG in
/-- `toPoly2_map_cmulG`: `toPoly2 (p.map (cmulG s)) = C(toPolyG s) · toPoly2 p`. -/
theorem toPoly2_map_cmulG (s : CPolyG ℚ) (p : List (CPolyG ℚ)) :
    toPoly2 (p.map (cmulG s)) = Polynomial.C (toPolyG s) * toPoly2 p := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, toPoly2_cons, toPoly2_cons, ih, toPolyG_cmulG, map_mul]
    ring

open CPolyG in
/-- `toPolyG_foldl_caddG`: `toPolyG ((List.range n).foldl (fun acc i => caddG acc (g i)) init)
= toPolyG init + Σ_{i<n} toPolyG (g i)`. -/
theorem toPolyG_foldl_caddG (g : ℕ → CPolyG ℚ) :
    ∀ (n : ℕ) (init : CPolyG ℚ),
      toPolyG ((List.range n).foldl (fun acc i => caddG acc (g i)) init)
        = toPolyG init + ∑ i ∈ Finset.range n, toPolyG (g i) := by
  intro n
  induction n with
  | zero => intro init; simp
  | succ m ih =>
    intro init
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      toPolyG_caddG, ih, Finset.sum_range_succ]
    ring

open CPolyG in
/-- `toPoly2_mulT`: `toPoly2 (mulT p q) = toPoly2 p · toPoly2 q`, where `mulT` is the Cauchy-product
`(mulT p q)_k = Σ_{i≤k} p_i·q_{k−i}`. -/
theorem toPoly2_mulT (p q : List (CPolyG ℚ)) :
    toPoly2 ((List.range (p.length + q.length)).map (fun k =>
        (List.range (k + 1)).foldl (fun acc i =>
          caddG acc (cmulG (p.getD i []) (q.getD (k - i) []))) []))
      = toPoly2 p * toPoly2 q := by
  apply Polynomial.ext
  intro k
  rw [toPoly2_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  by_cases hk : k < p.length + q.length
  · rw [getD_range_map _ _ _ hk, toPolyG_foldl_caddG, toPolyG_nil, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [toPolyG_cmulG, toPoly2_coeff, toPoly2_coeff]
  · rw [getD_out _ _ (by rw [List.length_map, List.length_range]; omega), toPolyG_nil]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [toPoly2_coeff, toPoly2_coeff]
    rcases le_or_gt p.length i with hip | hip
    · rw [getD_out p _ hip, toPolyG_nil, zero_mul]
    · rw [getD_out q (k - i) (by omega), toPolyG_nil, mul_zero]

open CPolyG in
/-- `tanDeriv_dpdt_getD`: the formal `t`-derivative reads coefficientwise,
`dpdt.getD k [] = cscaleG ((k:ℚ)+1) (p.getD (k+1) [])`. -/
theorem tanDeriv_dpdt_getD (p : List (CPolyG ℚ)) (k : ℕ) :
    ((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1)).getD k []
      = cscaleG ((k : ℚ) + 1) (p.getD (k + 1) []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_drop,
    List.getD_eq_getElem?_getD, show (0 + k) = k from by ring, show (1 + k) = (k + 1) from by ring]
  cases p[k + 1]? with
  | none => simp [cscaleG]
  | some a => simp

open CPolyG in
/-- `toPoly2_dpdt`: `toPoly2 dpdt = D_t (toPoly2 p)` (`Polynomial.derivative`) for `dpdt` the formal
`dp/dt` list. -/
theorem toPoly2_dpdt (p : List (CPolyG ℚ)) :
    toPoly2 ((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1))
      = Polynomial.derivative (toPoly2 p) := by
  apply Polynomial.ext
  intro k
  rw [toPoly2_coeff, tanDeriv_dpdt_getD, toPolyG_cscaleG, Polynomial.coeff_derivative,
    toPoly2_coeff]
  simp only [CFieldSpec.toK, id_eq]
  rw [map_add, map_one, Polynomial.C_eq_natCast]
  ring

open CPolyG in
/-- `toPoly2_mulDt`: `toPoly2 mulDt = (X²+1)·toPoly2 dpdt` for `mulDt` the `(t²+1)·dpdt` list. -/
theorem toPoly2_mulDt (dpdt : List (CPolyG ℚ)) :
    toPoly2 ((List.range (dpdt.length + 2)).map (fun k =>
        caddG (if k ≥ 2 then dpdt.getD (k - 2) [] else []) (dpdt.getD k [])))
      = (Polynomial.X ^ 2 + 1) * toPoly2 dpdt := by
  apply Polynomial.ext
  intro k
  rw [toPoly2_coeff, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
  by_cases hk : k < dpdt.length + 2
  · rw [getD_range_map _ _ _ hk, toPolyG_caddG, toPoly2_coeff, apply_ite toPolyG, toPolyG_nil]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, toPoly2_coeff]
    · rw [if_neg h2, toPoly2_coeff]
  · have hcoeffk : (toPoly2 dpdt).coeff k = 0 := by
      rw [toPoly2_coeff, getD_out _ _ (by omega), toPolyG_nil]
    rw [getD_out _ _ (by rw [List.length_map, List.length_range]; omega), toPolyG_nil, hcoeffk]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, toPoly2_coeff, getD_out _ _ (by omega), toPolyG_nil, add_zero]
    · rw [if_neg h2, add_zero]

open CPolyG in
/-- `toPoly2_tanDeriv`: the tangent derivation is bivariate `D = ∂/∂x + (t²+1)·∂/∂t`,
`toPoly2 (tanDeriv p) = toPoly2 (p.map cderivQ) + (X²+1)·D_t(toPoly2 p)` over `ℚ[x][t]`. -/
theorem toPoly2_tanDeriv (p : List (CPolyG ℚ)) :
    toPoly2 (tanDeriv p)
      = toPoly2 (p.map cderivQ)
        + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 p) := by
  show toPoly2 (tadd (p.map cderivQ)
      ((List.range (((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1)).length + 2)).map
        (fun k => caddG
          (if k ≥ 2 then ((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1)).getD (k - 2) []
            else [])
          (((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1)).getD k [])))) = _
  rw [toPoly2_tadd, toPoly2_mulDt, toPoly2_dpdt]

/-! ### Validation — the tangent RDE cancellation runs end-to-end (`cCoupledDECancelTan`)

The tangent coupled system over `t = tan(x)`, with `b₀ = 0`, `b₂ = 4x`, `c₁ = −t²+2t−8x²+1`,
`c₂ = 2−4x`, degree bound `n = 2` (diagonal shift `−2t = −n·η·t`). -/

/-- `cancelTanC1 = −t²+2t−8x²+1` as a `t`-polynomial (`t⁰ ↦ 1−8x²`, `t¹ ↦ 2`, `t² ↦ −1`). -/
def cancelTanC1 : List (CPolyG ℚ) := [[1, 0, -8], [2], [-1]]
/-- `cancelTanC2 = 2−4x` as a `t`-polynomial (constant in `t`). -/
def cancelTanC2 : List (CPolyG ℚ) := [[2, -4]]

/-- `cancelTanClearedCheck b0 b2 c1 c2 q1 q2`: `true` iff `(q₁, q₂)` solves the tangent `t`-polynomial
system `(Dq₁; Dq₂) + [[b₀−2t, −b₂],[b₂, b₀−2t]](q₁; q₂) = (c₁; c₂)` (`a = −1`, `n = 2`, `D = tanDeriv`),
checked as both cleared residuals being `tisZero`. -/
def cancelTanClearedCheck (b0 b2 : CPolyG ℚ) (c1 c2 q1 q2 : List (CPolyG ℚ)) : Bool :=
  -- diagonal shift `±2t`: as a t-polynomial, `2t = [0, 2]` (ℚ[x]-coefficients [0] then [2]).
  let twoT : List (CPolyG ℚ) := [[], [2]]
  -- matrix·(q₁;q₂): row1 = (b₀−2t)q₁ + (−b₂)q₂; row2 = b₂q₁ + (b₀+2t)q₂  (as t-polynomials).
  let mulConst : CPolyG ℚ → List (CPolyG ℚ) → List (CPolyG ℚ) := fun s p => p.map (cmulG s)
  let mulT : List (CPolyG ℚ) → List (CPolyG ℚ) → List (CPolyG ℚ) := fun p q =>
    let n := p.length + q.length
    (List.range n).map (fun k =>
      (List.range (k + 1)).foldl (fun acc i =>
        caddG acc (cmulG (p.getD i []) (q.getD (k - i) []))) [])
  let row1 := tadd (tsub (mulConst b0 q1) (mulT twoT q1)) (mulConst (cscaleG (-1) b2) q2)
  let row2 := tadd (mulConst b2 q1) (tsub (mulConst b0 q2) (mulT twoT q2))
  let r1 := tsub (tadd (tanDeriv q1) row1) c1
  let r2 := tsub (tadd (tanDeriv q2) row2) c2
  tisZero r1 && tisZero r2

open CPolyG in
/-- `toPoly2_twoT`: `toPoly2 [[],[2]] = C(C 2)·X` (the diagonal `2t` as a `ℚ[x][t]` polynomial). -/
theorem toPoly2_twoT :
    toPoly2 ([[], [2]] : List (CPolyG ℚ)) = Polynomial.C (Polynomial.C 2) * Polynomial.X := by
  show toPoly2 ([[], [2]] : List (CPolyG ℚ)) = _
  rw [toPoly2_cons, toPoly2_cons, toPoly2_nil]
  simp only [toPolyG_nil, map_zero, mul_zero, add_zero, zero_add]
  rw [show toPolyG ([2] : CPolyG ℚ) = Polynomial.C 2 by
    rw [show ([2] : CPolyG ℚ) = (2 : ℚ) :: ([] : CPolyG ℚ) from rfl, toPolyG_cons, toPolyG_nil]
    simp [CFieldSpec.toK]]
  ring

open CPolyG in
/-- `cancelTanClearedCheck_sound`: if `cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true` then `(q₁, q₂)`
solves the tangent `t`-polynomial system at the `ℚ[x][t]` level — both rows of
`(Dq; …) + [[b₀−2t, −b₂],[b₂, b₀−2t]]·q = c`, `D = ∂/∂x + (t²+1)·∂/∂t`. -/
theorem cancelTanClearedCheck_sound (b0 b2 : CPolyG ℚ) (c1 c2 q1 q2 : List (CPolyG ℚ))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
    (toPoly2 (q1.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q1))
        + (Polynomial.C (toPolyG b0) * toPoly2 q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q1)
        + Polynomial.C (toPolyG (cscaleG (-1) b2)) * toPoly2 q2
      = toPoly2 c1 ∧
      (toPoly2 (q2.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q2))
        + Polynomial.C (toPolyG b2) * toPoly2 q1
        + (Polynomial.C (toPolyG b0) * toPoly2 q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q2)
      = toPoly2 c2 := by
  rw [cancelTanClearedCheck, Bool.and_eq_true] at hcheck
  obtain ⟨h1, h2⟩ := hcheck
  have e1 := toPoly2_eq_zero_of_tisZero _ h1
  have e2 := toPoly2_eq_zero_of_tisZero _ h2
  simp only [toPoly2_tsub, toPoly2_tadd, toPoly2_tanDeriv, toPoly2_map_cmulG, toPoly2_mulT,
    toPoly2_twoT, sub_eq_zero] at e1 e2
  exact ⟨by linear_combination e1, by linear_combination e2⟩

/-- `cCoupledDECancelTan_sound_of_check`: if `cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2)`
and the returned pair passes `cancelTanClearedCheck`, then `(q₁, q₂)` solves the tangent coupled
`t`-polynomial system at the `ℚ[x][t]` level (composition with `cancelTanClearedCheck_sound`). -/
theorem cCoupledDECancelTan_sound_of_check (dbound : ℕ) (b0 b2 : CPolyG ℚ)
    (c1 c2 q1 q2 : List (CPolyG ℚ)) (n : ℕ)
    (_hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
    (toPoly2 (q1.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q1))
        + (Polynomial.C (toPolyG b0) * toPoly2 q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q1)
        + Polynomial.C (toPolyG (cscaleG (-1) b2)) * toPoly2 q2
      = toPoly2 c1 ∧
      (toPoly2 (q2.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q2))
        + Polynomial.C (toPolyG b2) * toPoly2 q1
        + (Polynomial.C (toPolyG b0) * toPoly2 q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q2)
      = toPoly2 c2 :=
  cancelTanClearedCheck_sound b0 b2 c1 c2 q1 q2 hcheck

-- **Sanity print** (book p.267): `cCoupledDECancelTan` returns `q₁ = t − 1`, `q₂ = 2x`.
#eval (cCoupledDECancelTan 1 ([] : CPolyG ℚ) [0, 4] cancelTanC1 cancelTanC2 2).map
  (fun p => (p.1.map (fun c => (c : List ℚ)), p.2.map (fun c => (c : List ℚ))))

/-- `rischDE_cancelTan_example`: the tangent coupled system over `t = tan(x)` (`b₀ = 0`, `b₂ = 4x`,
`c₁ = −t²+2t−8x²+1`, `c₂ = 2−4x`, degree bound `n = 2`) solves via `cCoupledDECancelTan` to
`q₁ = t − 1`, `q₂ = 2x`, verified by `cancelTanClearedCheck`. -/
theorem rischDE_cancelTan_example :
    (match cCoupledDECancelTan 1 ([] : CPolyG ℚ) [0, 4] cancelTanC1 cancelTanC2 2 with
      | some (q1, q2) =>
          cancelTanClearedCheck [] [0, 4] cancelTanC1 cancelTanC2 q1 q2
      | none => false) = true := by native_decide

#print axioms rischDE_cancelTan_example

/-! ### Restatements of the soundness against the intended wording (anonymous `example`s)

The base-solve and tangent soundness lemmas restated: from the engine's own cleared check the returned
`t`-polynomials solve the genuine coupled differential systems over `ℚ[x]` / `ℚ[x][t]`. -/

open CPolyG

-- ★ Base coupled-system soundness, `native_decide`-free: a self-certifying `cCoupledDESystem` solve gives
-- the two `ℚ[X]` row identities `D(y₁) + b₁y₁ + a·b₂y₂ = z₁`, `D(y₂) + b₂y₁ + b₁y₂ = z₂`.
example (a : ℚ) (b1 b2 z1 z2 y1 y2 : CPolyG ℚ) (d : ℕ)
    (hsome : cCoupledDESystem a b1 b2 z1 z2 d = some (y1, y2))
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (toPolyG y1) + toPolyG b1 * toPolyG y1
        + Polynomial.C a * (toPolyG b2 * toPolyG y2) = toPolyG z1 ∧
      Polynomial.derivative (toPolyG y2) + toPolyG b2 * toPolyG y1
        + toPolyG b1 * toPolyG y2 = toPolyG z2 :=
  cCoupledDESystem_sound_of_check a b1 b2 z1 z2 d y1 y2 hsome hcheck

-- ★ Tangent RDE cancellation soundness, `native_decide`-free: a self-certifying `cCoupledDECancelTan` solve
-- gives both rows of the §8.4 tangent coupled `t`-system over `ℚ[x][t]` (`D = ∂/∂x + (t²+1)∂/∂t`).
example (dbound : ℕ) (b0 b2 : CPolyG ℚ) (c1 c2 q1 q2 : List (CPolyG ℚ)) (n : ℕ)
    (hsome : cCoupledDECancelTan dbound b0 b2 c1 c2 n = some (q1, q2))
    (hcheck : cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true) :
    (toPoly2 (q1.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q1))
        + (Polynomial.C (toPolyG b0) * toPoly2 q1
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q1)
        + Polynomial.C (toPolyG (cscaleG (-1) b2)) * toPoly2 q2
      = toPoly2 c1 ∧
      (toPoly2 (q2.map cderivQ) + (Polynomial.X ^ 2 + 1) * Polynomial.derivative (toPoly2 q2))
        + Polynomial.C (toPolyG b2) * toPoly2 q1
        + (Polynomial.C (toPolyG b0) * toPoly2 q2
            - Polynomial.C (Polynomial.C 2) * Polynomial.X * toPoly2 q2)
      = toPoly2 c2 :=
  cCoupledDECancelTan_sound_of_check dbound b0 b2 c1 c2 q1 q2 n hsome hcheck

#print axioms coupledClearedCheck_sound
#print axioms cancelTanClearedCheck_sound

end DeepWiki.SymbolicIntegration
