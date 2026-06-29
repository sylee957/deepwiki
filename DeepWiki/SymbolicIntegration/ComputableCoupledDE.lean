import DeepWiki.SymbolicIntegration.ComputableParametric

/-! # The Coupled Differential System and the tangent RDE cancellation (Bronstein Chapter 8)

Bronstein's **coupled differential system** problem (Ch. 8, *Symbolic Integration I*, 2005, p.257):
given a differential field `K` of characteristic `0`, `f₁, f₂, g₁, g₂ ∈ K`, and a constant
`a ∈ Const_D(K)` with `√a ∉ K`, decide whether the system

```
  (Dy₁; Dy₂) + [[f₁, a·f₂], [f₂, f₁]] · (y₁; y₂) = (g₁; g₂)                            (8.2)
```

has a solution `(y₁, y₂) ∈ K × K`, and find one. Writing `y = y₁ + y₂√a`, `f = f₁ + f₂√a`,
`g = g₁ + g₂√a`, the system (8.2) is **equivalent** (Bronstein eq. 8.3, since `D√a = 0`) to the single
Risch differential equation `Dy + f·y = g` over `K(√a)` — its real and imaginary parts are exactly the
two rows of (8.2). This is *the* engine that finishes the RDE oracle's last gap: the **tangent
cancellation case** `PolyRischDECancelTan` (book p.215, `t = tan(x)`, `Dt = t²+1`, `δ = 2`), which the
§6.6 dispatcher in `ComputableRischDE` deferred, recurses precisely into this coupled system over the
**base** field `k` rather than into a Risch DE over the isomorphic copy `k(√−1)` (the whole point of
Ch. 8 — keeping the recursion over `k`, book p.258).

## The tangent reduction (Bronstein §8.4, the hypertangent case)

For `t = tan(x)` (`Dt/(t²+1) = η ∈ k`, `δ = 2`), the cancellation case of the degree-bounded polynomial
equation `Dq + b·q = c` has `b₂ ∈ k`, `b₁ = b₀ − nηt` (`n` = the degree bound, `b₀ ∈ k`). The
`CoupledDECancelTan(b₀, b₂, c₁, c₂, D, n)` box (book p.265) solves the `t`-polynomial system

```
  (Dq₁; Dq₂) + [[b₀ − nηt, −b₂], [b₂, b₀ + nηt]] · (q₁; q₂) = (c₁; c₂)
```

(`a = −1`) for `q₁, q₂ ∈ k[t]` of degree `≤ n`, degree-by-degree from the top: at each degree `m` the
leading-coefficient relation (book eq. 8.10) is the **base coupled system in `k`**
`CoupledDESystem(b₀, b₂, coeff(c₁,tᵐ), coeff(c₂,tᵐ))`, then `c₁, c₂` are reduced and the degree drops
(book p.265, the trace of Example 8.4.1).

## What this file delivers (computable over ℚ(x), `native_decide`-validated)

* **`cCoupledDESystem fuel a b1 b2 z1 z2 dbound`** — the **base coupled system solver** over `k = ℚ(x)`
  (`D = d/dx`): solve `(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]] · (y₁; y₂) = (z₁; z₂)` for `y₁, y₂ ∈ ℚ(x)`,
  with `a ∈ ℚ` the constant and `b₁, b₂, z₁, z₂ ∈ ℚ[x]` polynomial coefficients (the case the §8.4
  tangent recursion reaches — its leading-coefficient base calls have polynomial data). Implemented by a
  **polynomial ansatz** `y₁ = Σ uᵢxⁱ`, `y₂ = Σ vᵢxⁱ` of degree `≤ dbound`: the two rows of (8.2) become
  polynomial identities, whose coefficient-wise vanishing is a single ℚ-linear system in the `2(dbound+1)`
  unknowns `uᵢ, vᵢ`, solved exactly by the §7.3 unique-linear-solve `cConstSolveUniqueQ` (`crref`).
  Returns `some (y₁, y₂) : CPolyG ℚ × CPolyG ℚ` (the two solution polynomials), or `none`.

* **`cCoupledDECancelTan fuel b0 b2 c1 c2 dbound nbound`** — the **tangent RDE cancellation** box (book
  p.265) over `k = ℚ(x)`, `t = tan(x)`, `η = Dt/(t²+1) = 1` (so the `−nηt`/`+nηt` shifts are `∓n·t`).
  Solves the `t`-polynomial coupled system above for `q₁, q₂ ∈ k[t]` of degree `≤ nbound`,
  degree-by-degree from the top, each step a `cCoupledDESystem` base solve. Returns `some (q₁, q₂)`
  (`q₁, q₂` as `t`-polynomials with `ℚ[x]`-coefficients), or `none`. This *is* the `PolyRischDECancelTan`
  that `ComputableRischDE`'s §6.6 dispatcher deferred.

## Validation (`native_decide`) — Bronstein Example 8.4.1 (book p.265–267)

`k = ℚ(x)`, `D = d/dx`, `t = tan(x)`, the coupled system (8.11)

```
  (Dy₁; Dy₂) + [[0, −4x], [4x, 0]] · (y₁; y₂) = (−(t²−2t+8x²−1)/(t²+1); 2(1−2x)/(t²+1))
```

which arises from `∫ −((tan²x−2tan x+8x²−1)tan(x²)+4x−2)/((tan²x+1)(tan²x²+1)) dx` (8.12). After the §6.x
reduction (book p.266) the equation becomes (8.14), equivalent to the `t`-polynomial system (8.15)

```
  (Dq₁; Dq₂) + [[−2t, −4x], [4x, −2t]] · (q₁; q₂) = (−t²+2t−8x²+1; 2(1−2x))
```

with degree bound `n = 2`. Running `cCoupledDECancelTan` on `b₀ = 0, b₂ = 4x, c₁ = −t²+2t−8x²+1,
c₂ = 2−2x, n = 2` returns the book's solution `q₁ = t − 1`, `q₂ = −1 + 2x + 1 = 2x` (book eq. before
p.267's conclusion: `q₁ = h₁t + h₂ + s₁ = t − 1`, `q₂ = h₂t − h₁ + s₂ = 2x`), so

```
  y₁ = (t − 1)/(t²+1)   and   y₂ = 2x/(t²+1)
```

(book p.267). `coupledDESystem_example` pins the base-case solve `CoupledDESystem(0, 4x−2, −8x²+1, 4−4x)
= (−1, 2x+1)` (book p.266 step 4, `a = −1`) by the cleared system identity (`cisZeroG` of each row's
residual), and `rischDE_cancelTan_example` runs the full `cCoupledDECancelTan` and checks the returned
`(q₁, q₂)` *actually solves* the system (8.15) by clearing the polynomial identity of both rows — the
tangent RDE cancellation case that `ComputableRischDE` left deferred now **computes** its solution. No
`sorry`; the headline carries only the native-compiler axioms (`#print axioms`).

## What is deferred (honest, documented)

The `cCoupledDESystem` base solve is implemented for **polynomial** coefficient data over ℚ(x) via the
degree-bounded ansatz — exactly the data the §8.4 tangent recursion produces. The full Ch. 8 algorithm's
**denominator / pole bounds on the pair** (the §8.1–8.3 `WeakNormalizer` / `RdeNormalDenominator` /
`RdeBoundDegree` analogues for the 2-vector, book p.257–264) — which would handle a coupled system with
genuine rational-function poles in `t` and reduce it to the polynomial ansatz — are documented but not
run; the ansatz degree bound `dbound` is supplied by the caller (the tangent recursion uses the
right-hand-side degree, which suffices on the worked example). The §8.3 **nonlinear** case for general
`δ ≥ 2` monomials (other than the hypertangent `t²+1`, where `√−1` generates a usable irreducible) has
no general algorithm in the book itself (book p.263); only the hypertangent specialization is realized.
The §8.2 **hyperexponential** coupled case (`CoupledDECancelExp`, book p.261) is the symmetric
continuation. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

namespace CPolyG

/-! ### The base coupled differential system over ℚ(x) (`cCoupledDESystem`, Bronstein eq. 8.2/8.10)

`CoupledDESystem(b₁, b₂, z₁, z₂)` solves `(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]](y₁; y₂) = (z₁; z₂)` for
`y₁, y₂ ∈ k = ℚ(x)`, `D = d/dx`. For the polynomial coefficient data the §8.4 tangent recursion feeds
it (`b₁, b₂, z₁, z₂ ∈ ℚ[x]`), a polynomial solution `y₁, y₂ ∈ ℚ[x]` of bounded degree exists when the
system is solvable, found by undetermined coefficients. The two rows expand to:

```
  Dy₁ + b₁·y₁ + a·b₂·y₂ = z₁
  Dy₂ + b₂·y₁ + b₁·y₂ = z₂
```

With `y₁ = Σ_{i≤d} uᵢxⁱ`, `y₂ = Σ_{i≤d} vᵢxⁱ`, every coefficient of the two residual polynomials is a
ℚ-linear form in `u₀..u_d, v₀..v_d`; setting them all to zero is one ℚ-linear system, solved by
`cConstSolveUniqueQ`. -/

/-- **ℚ-coefficient vector of a `CPolyG ℚ` padded to length `n`** `padCoeffsQ p n`: the low→high
coefficient list of `p`, truncated/zero-extended to exactly `n` entries. Used to read each residual
polynomial's coefficients as the rows of the ℚ-linear system for the coupled-system ansatz. -/
def padCoeffsQ (p : CPolyG ℚ) (n : ℕ) : List ℚ :=
  (List.range n).map (fun i => (p : List ℚ).getD i 0)

/-- **Linear map "multiply the degree-`d` ansatz `Σ xⁱ` by `m`, as a coefficient matrix"**
`mulMatrixQ m d nrows`: the `nrows × (d+1)` ℚ-matrix whose column `i` is the coefficient vector
(length `nrows`) of `m · xⁱ`, for the unknowns `u₀..u_d`. Row `r`, column `i` is the `x^r`-coefficient
of `m·xⁱ`, i.e. `coeff(m, r − i)`. Multiplying the unknown vector `(u₀,…,u_d)` by this matrix gives the
coefficient vector of `m·(Σ uᵢxⁱ)`. -/
def mulMatrixQ (m : CPolyG ℚ) (d nrows : ℕ) : List (List ℚ) :=
  (List.range nrows).map (fun r =>
    (List.range (d + 1)).map (fun i =>
      if r ≥ i then (m : List ℚ).getD (r - i) 0 else 0))

/-- **Linear map "`D(Σ uᵢxⁱ) = Σ i·uᵢ·x^{i−1}`, as a coefficient matrix"** `derivMatrixQ d nrows`:
the `nrows × (d+1)` ℚ-matrix whose action on `(u₀,…,u_d)` gives the coefficient vector of
`d/dx(Σ uᵢxⁱ) = Σ_{i≥1} i·uᵢ·x^{i−1}`. Row `r`, column `i` is `i` when `i = r+1`, else `0`. -/
def derivMatrixQ (d nrows : ℕ) : List (List ℚ) :=
  (List.range nrows).map (fun r =>
    (List.range (d + 1)).map (fun i => if (i : ℕ) = r + 1 then ((i : ℚ)) else (0 : ℚ)))

/-- **Entrywise sum of two equally-shaped ℚ-matrices** `matAddQ A B`: row- and column-wise `+`. The
coupled-system rows are sums of a `derivMatrixQ` block and `mulMatrixQ` blocks, assembled before the
ℚ-linear solve. -/
def matAddQ (A B : List (List ℚ)) : List (List ℚ) :=
  List.zipWith (fun ra rb => List.zipWith (· + ·) ra rb) A B

/-- **Horizontal block-concatenation of two ℚ-matrices** `hcatQ A B`: append each row of `B` to the
corresponding row of `A` (the unknowns split as `[u₀..u_d | v₀..v_d]`, so each equation's row is the
`u`-block beside the `v`-block). -/
def hcatQ (A B : List (List ℚ)) : List (List ℚ) :=
  List.zipWith (· ++ ·) A B

/-- **Computable base coupled differential system over ℚ(x)** `cCoupledDESystem fuel a b1 b2 z1 z2 d`
(Bronstein Ch. 8, eq. 8.2/8.10, the `CoupledDESystem` recursion target, `D = d/dx`, `k = ℚ(x)`):
solve `(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]] · (y₁; y₂) = (z₁; z₂)` for `y₁, y₂ ∈ ℚ[x]` of degree `≤ d`,
with `a ∈ ℚ` the constant (`a = −1` for the tangent reduction) and `b₁, b₂, z₁, z₂ ∈ ℚ[x]`.

Polynomial ansatz `y₁ = Σ_{i≤d} uᵢxⁱ`, `y₂ = Σ_{i≤d} vᵢxⁱ`. The two rows become the residuals

```
  R₁ = D y₁ + b₁·y₁ + (a·b₂)·y₂ − z₁ = 0
  R₂ = D y₂ + b₂·y₁ + b₁·y₂ − z₂ = 0
```

Pick `nrows` large enough to hold every coefficient of `R₁, R₂` (one more than the max degree among
`D(xᵈ)`, `b₁·xᵈ`, `b₂·xᵈ`, `z₁`, `z₂`). The coefficient of `x^r` in each `Rₖ` is a ℚ-linear form in
`(u₀..u_d, v₀..v_d)`; stacking row `R₁`'s `nrows` coefficient-equations above `R₂`'s gives a
`2·nrows × 2(d+1)` ℚ-system `M·(u;v) = rhs` (`rhs` = the `zₖ` coefficients), solved for the **unique**
`(u;v)` by `cConstSolveUniqueQ`. Returns `some (y₁, y₂)` (the reconstructed polynomials) or `none`
("no polynomial solution of degree `≤ d`"). -/
def cCoupledDESystem (_fuel : ℕ) (a : ℚ) (b1 b2 z1 z2 : CPolyG ℚ) (d : ℕ) :
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

/-! ### The tangent RDE cancellation `cCoupledDECancelTan` (Bronstein §8.4, book p.265)

`t = tan(x)`, `Dt = t²+1`, `η = Dt/(t²+1) = 1`. The cancellation case of `Dq + b·q = c` (`δ = 2`) has
`b = b₁ + b₂√−1` with `b₂ ∈ k`, `b₁ = b₀ − n·η·t`. The `CoupledDECancelTan` box solves the `t`-polynomial
system (book p.265)

```
  (Dq₁; Dq₂) + [[b₀ − nηt, −b₂], [b₂, b₀ + nηt]] · (q₁; q₂) = (c₁; c₂)
```

(`a = −1`) for `q₁, q₂ ∈ k[t]` of degree `≤ n`, degree-by-degree from the top: at degree `m`, the
leading coefficients (book eq. 8.10) solve the base `CoupledDESystem(b₀, b₂, coeff(c₁,tᵐ),
coeff(c₂,tᵐ))`, then `c₁, c₂` are reduced and the degree drops. Here the monomial coefficients are in
`k = ℚ(x)`, carried as `CPolyG ℚ` (we run over polynomial `b₀, b₂, c₁, c₂`, the worked-example data). -/

/-- **`t`-monomial derivation `D = κ_D + (t²+1)·d/dt` over `ℚ[x][t]`** `tanDeriv p`: the derivation of a
`t`-polynomial `p` (coefficients in `ℚ[x]`, themselves `CPolyG ℚ`) for the tangent monomial `Dt = t²+1`.
Coefficientwise `d/dx` plus `(t²+1)·dp/dt`. The `t = tan(x)` analogue of `cmonomialDeriv`, over the
concrete coefficient field `ℚ(x)` represented as `CPolyG ℚ`. -/
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

/-- **`tᵐ`-coefficient of a `t`-polynomial** `tcoeff p m`: the degree-`m` coefficient (an element of
`ℚ(x)`, here `CPolyG ℚ`), `[]` (zero) past the end. The `coefficient(c, tᵐ)` of the §8.4 box. -/
def tcoeff (p : List (CPolyG ℚ)) (m : ℕ) : CPolyG ℚ := p.getD m []

/-- **`t`-degree of a `t`-polynomial over `ℚ(x)`** `tdeg p`: the highest index with a nonzero
(`ℚ(x)`-)coefficient, or `0` for the zero polynomial. The `deg(c)` of the §8.4 loop. -/
def tdeg (p : List (CPolyG ℚ)) : ℕ :=
  ((p.zipIdx.filter (fun (c, _) => ¬ cisZeroG c)).map (fun (_, i) => i)).foldl max 0

/-- **`t`-polynomial is zero** `tisZero p`: every `ℚ(x)`-coefficient is zero. The `c = 0` test. -/
def tisZero (p : List (CPolyG ℚ)) : Bool := p.all cisZeroG

/-- **Scale a `t`-polynomial coefficientwise by `s·tᵐ`** `tshiftScale s m`: the single-term
`t`-polynomial `s·tᵐ` (`s ∈ ℚ(x) = CPolyG ℚ`), as the list `[0,…,0,s]` with `m` leading zeros. The
`q ← q + sₖtᵐ` accumulation step. -/
def tshiftScale (s : CPolyG ℚ) (m : ℕ) : List (CPolyG ℚ) :=
  (List.replicate m ([] : CPolyG ℚ)) ++ [s]

/-- **Coefficientwise subtraction of `t`-polynomials over `ℚ(x)`** `tsub p q`: `pₖ − qₖ` per `t`-degree.
The `c ← c − …` reduction step. -/
def tsub (p q : List (CPolyG ℚ)) : List (CPolyG ℚ) :=
  let n := max p.length q.length
  (List.range n).map (fun k => csubG (p.getD k []) (q.getD k []))

/-- **Coefficientwise addition of `t`-polynomials over `ℚ(x)`** `tadd p q`: `pₖ + qₖ`. -/
def tadd (p q : List (CPolyG ℚ)) : List (CPolyG ℚ) :=
  let n := max p.length q.length
  (List.range n).map (fun k => caddG (p.getD k []) (q.getD k []))

/-- **Scale a `t`-polynomial over `ℚ(x)` by a `ℚ`-constant** `cscaleListQ s p`: multiply every
`ℚ[x]`-coefficient of the `t`-polynomial `p` by the scalar `s ∈ ℚ`. The `nη·(…)` scaling step of the
§8.4 box (`η = 1`, so `nη = n`). -/
def cscaleListQ (s : ℚ) (p : List (CPolyG ℚ)) : List (CPolyG ℚ) := p.map (cscaleG s)

/-! #### Projection mod `t²+1` and division by `t − √−1` over `k(√−1)[t]`

The §8.4 box works in `k(√−1)[t]`. We represent a `k(√−1)`-element as a **pair** `(re, im)` of
`CPolyG ℚ` (so `re + im·√−1`, `√−1² = −1`), and a `k(√−1)[t]`-polynomial as a `t`-list of such pairs.
The two operations the box needs are (i) *project a `k[t]` `t`-polynomial at `t = √−1`* (reduce mod
`t²+1`), giving its value `re + im·√−1 ∈ k(√−1)`, and (ii) *divide a `k(√−1)[t]`-polynomial by
`t − √−1`* (exact, since the numerator vanishes at `t = √−1` by construction). -/

/-- **Evaluate a `k[t]` `t`-polynomial at `t = √−1`** `evalAtI p = (re, im)` with `p(√−1) = re + im·√−1`
(`re, im ∈ k = ℚ(x)`): reduce `p` mod `t²+1` (Horner from the top, `t·(u+v√−1) = −v + u√−1` using
`t² = −1`). The §8.4 step `c₁(√−1) + c₂(√−1)√−1 = z₁ + z₂√−1`. -/
def evalAtI (p : List (CPolyG ℚ)) : CPolyG ℚ × CPolyG ℚ :=
  p.foldr (fun (a : CPolyG ℚ) (acc : CPolyG ℚ × CPolyG ℚ) =>
    -- acc = (u, v) standing for u + v√−1; new = a + √−1·acc = a + (u + v√−1)√−1 = (a − v) + u√−1.
    (caddG a (cscaleG (-1) acc.2), acc.1)) ([], [])

/-- **`k(√−1)`-multiplication on pairs** `cmulI (a,b) (c,d) = (ac − bd, ad + bc)` (`(a+b√−1)(c+d√−1)`,
`√−1² = −1`). -/
def cmulI (x y : CPolyG ℚ × CPolyG ℚ) : CPolyG ℚ × CPolyG ℚ :=
  (csubG (cmulG x.1 y.1) (cmulG x.2 y.2), caddG (cmulG x.1 y.2) (cmulG x.2 y.1))

/-- **`k(√−1)`-subtraction on pairs** `csubI (a,b) (c,d) = (a−c, b−d)`. -/
def csubI (x y : CPolyG ℚ × CPolyG ℚ) : CPolyG ℚ × CPolyG ℚ :=
  (csubG x.1 y.1, csubG x.2 y.2)

/-- **`k(√−1)`-zero test on a pair** `cisZeroI (a,b)`: both parts vanish. -/
def cisZeroI (x : CPolyG ℚ × CPolyG ℚ) : Bool := cisZeroG x.1 && cisZeroG x.2

/-- **Synthetic division of a `k(√−1)[t]`-polynomial by `t − √−1`** `divByTminusI p = q` with
`p = (t − √−1)·q` (exact when `p(√−1) = 0`). `p` is a `t`-list of `k(√−1)`-pairs, low→high; Ruffini /
synthetic division by the root `√−1 = (0,1)`: from the top coefficient down,
`qⱼ = pⱼ₊₁ + √−1·qⱼ₊₁`. Returns the quotient `t`-list of pairs (degree one lower); the remainder
`p(√−1)` is dropped (zero by construction). The §8.4 step `c ← (…)/p`, `p = t − √−1`. -/
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

/-- **Computable tangent RDE cancellation** `cCoupledDECancelTan fuel dbound b0 b2 c1 c2 n` (Bronstein
§8.4, the `CoupledDECancelTan(b₀, b₂, c₁, c₂, D, n)` box, book p.265), over `k = ℚ(x)`, `t = tan(x)`,
`η = Dt/(t²+1) = 1`, `a = −1`. Given `b₀, b₂ ∈ ℚ[x]`, the `t`-polynomials `c₁, c₂` (coefficients in
`ℚ[x] = CPolyG ℚ`), the degree-bound `n` (recursed down), and a base-solve degree bound `dbound`,
solves the `t`-polynomial coupled system

```
  (Dq₁; Dq₂) + [[b₀ − n·t, −b₂], [b₂, b₀ − n·t]] · (q₁; q₂) = (c₁; c₂)
```

(`η = 1` so `nηt = n·t`) for `q₁, q₂ ∈ k[t]` of `t`-degree `≤ n` — the symmetric eq-8.2 real form
`[[f₁, af₂], [f₂, f₁]]` of `Dq + b·q = c` with `f₁ = b₀ − nηt` on both diagonals (Bronstein's box
prints the (2,2) entry as `b₀ + nηt`, a misprint — Example 8.4.1's system (8.15) has `−` there). The
box, **recursing on `n`**:

```
if n = 0 then
    if c₁ ∈ k and c₂ ∈ k then return CoupledDESystem(b₀, b₂, c₁, c₂) else "no solution"
p ← t − √−1
c₁(√−1) + c₂(√−1)√−1 = z₁ + z₂√−1                              (z₁, z₂ ∈ k, via evalAtI)
(s₁, s₂) ← CoupledDESystem(b₀, b₂ − nη, z₁, z₂)                 (base solve in k, η = 1)
if "no solution" then return "no solution"
c ← (c₁ − z₁ + nη(s₁t + s₂) + (c₂ − z₂ + nη(s₂t − s₁))√−1) / p   (divByTminusI)
c = d₁ + d₂√−1                                                  (d₁, d₂ ∈ k[t])
(h₁, h₂) ← CoupledDECancelTan(b₀, b₂ + η, d₁, d₂, D, n − 1)
if "no solution" then return "no solution"
return (h₁t + h₂ + s₁, h₂t − h₁ + s₂)
```

`D` is the tangent monomial derivation (`tanDeriv`); the `nη(s₁t+s₂)` etc. terms are formed over `k[t]`
(`η = 1`). `cCoupledDESystem` does the base solve with ansatz degree `≤ dbound`. The recursion is
**structural on `n`** (decremented each level — this is what bounds it, so it whnf-reduces and admits the
`cCoupledDECancelTan.induct` recursion principle used by the soundness proof); `fuel` is a spare bound
threaded unchanged. Returns `some (q₁, q₂)` (the two `t`-polynomials with `ℚ[x]`-coefficients), or `none`. -/
def cCoupledDECancelTan (fuel dbound : ℕ) (b0 b2 : CPolyG ℚ) :
    (c1 c2 : List (CPolyG ℚ)) → (n : ℕ) → Option (List (CPolyG ℚ) × List (CPolyG ℚ))
  | c1, c2, 0 =>
    -- n = 0: c₁, c₂ must be in k (degree-0 in t); solve the base coupled system directly.
    if tdeg c1 = 0 && tdeg c2 = 0 then
      match cCoupledDESystem fuel (-1) b0 b2 (tcoeff c1 0) (tcoeff c2 0) dbound with
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
    match cCoupledDESystem fuel (-1) b0 b2shift z1 z2 dbound with
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
      match cCoupledDECancelTan fuel dbound b0 (caddG b2 [CField.one]) d1 d2 n with
      | none => none
      | some (h1, h2) =>
        -- return (h₁t + h₂ + s₁, h₂t − h₁ + s₂).
        let h1t : List (CPolyG ℚ) := [[]] ++ h1     -- h₁·t (shift up by one t-degree)
        let h2t : List (CPolyG ℚ) := [[]] ++ h2
        let q1 := tadd (tadd h1t h2) [s1]
        let q2 := tsub (tadd h2t [s2]) h1
        some (q1, q2)

end CPolyG

/-! ### Validation — Bronstein Example 8.4.1 (book p.265–267)

`k = ℚ(x)`, `D = d/dx`, `t = tan(x)`. After the §6.x reduction the equation (8.14) becomes the
`t`-polynomial coupled system (8.15)

```
  (Dq₁; Dq₂) + [[−2t, −4x], [4x, −2t]] · (q₁; q₂) = (−t²+2t−8x²+1; 2(1−2x))
```

with `a = −1`, `b = 4x√−1 − 2t`, degree bound `n = 2`. The `CoupledDECancelTan` box is applied with
`b₀ = 0`, `b₂ = 4x`, `c₁ = −t²+2t−8x²+1`, `c₂ = 2−2x` (the `−2t` on the diagonal is the `−n·η·t` shift
with `n = 2`, `η = 1`). The book's solution (p.267) is `q₁ = t − 1`, `q₂ = 2x`, hence
`y₁ = (t−1)/(t²+1)`, `y₂ = 2x/(t²+1)`. -/

open CPolyG

/-- `x ∈ ℚ[x]` as a `CPolyG ℚ` coefficient (low→high `[0, 1]`). -/
def xQ : CPolyG ℚ := [0, 1]

/-- Example 8.4.1's base coupled system data (book p.266 step 4): `b₁ = 0`, `b₂ = 4x−2`,
`z₁ = 2(1−4x²) = 2−8x²`, `z₂ = 4(1−x) = 4−4x`, `a = −1`. Solution `(s₁, s₂) = (−1, 2x+1)`. *(The book
writes the `CoupledDESystem` call as `(0, 4x−2, −8x²+1, 4−4x)`, but the system it then displays has
right-hand side `(2(1−4x²); 4(1−x))`; the `−8x²+1` third argument is a misprint for `2−8x²`, the value
that `c₁(√−1) + c₂(√−1)√−1` actually produces — and the value that makes `(−1, 2x+1)` solve the
displayed system.)* -/
def coupledExB2 : CPolyG ℚ := [-2, 4]          -- 4x − 2
/-- Example 8.4.1 base system `z₁ = 2(1−4x²) = 2 − 8x²` (low→high). -/
def coupledExZ1 : CPolyG ℚ := [2, 0, -8]       -- 2 − 8x²
/-- Example 8.4.1 base system `z₂ = 4(1−x) = 4 − 4x` (low→high). -/
def coupledExZ2 : CPolyG ℚ := [4, -4]          -- 4 − 4x

/-- **Cleared base-coupled-system check** `coupledClearedCheck a b1 b2 z1 z2 y1 y2`: `true` iff
`(y₁, y₂)` solves `(Dy₁; Dy₂) + [[b₁, a·b₂],[b₂, b₁]](y₁; y₂) = (z₁; z₂)` over ℚ(x) (`D = d/dx`),
checked as the two polynomial identities `Dy₁ + b₁y₁ + ab₂y₂ − z₁ = 0` and `Dy₂ + b₂y₁ + b₁y₂ − z₂ = 0`
(by `cisZeroG` of each residual; `CPolyG ℚ` arithmetic is exact). -/
def coupledClearedCheck (a : ℚ) (b1 b2 z1 z2 y1 y2 : CPolyG ℚ) : Bool :=
  let r1 := csubG (caddG (caddG (cderivQ y1) (cmulG b1 y1)) (cscaleG a (cmulG b2 y2))) z1
  let r2 := csubG (caddG (caddG (cderivQ y2) (cmulG b2 y1)) (cmulG b1 y2)) z2
  cisZeroG r1 && cisZeroG r2

/-! ### ★ Base coupled-system soundness from the engine's own cleared check (`native_decide`-free)

The base solve `cCoupledDESystem` ends in `cConstSolveUniqueQ` (ℚ-Gaussian elimination, `crref`). We close
the coupled-system soundness through the engine's *own* cleared-residual self-check `coupledClearedCheck`:
the bridge `coupledClearedCheck = true ⟹ the two field identities over ℚ[X]` (`coupledClearedCheck_sound`
below) is `native_decide`-FREE (pure `cisZeroG_iff` + the `toPolyG` ring/derivation homs).

**This self-check is now `native_decide`-FREE *dischargeable*, not merely reachable:**
`ComputableLinearSolveCorrect` proves `cConstSolveUniqueQ_sound` (abstract ℚ-Gaussian-elimination
correctness) and `ComputableCoupledDEAssembly` proves the matrix-assembly faithful, giving
`coupledClearedCheck_of_cCoupledDESystem` (the engine's check always passes on a returned solve) and hence
the **unconditional** `cCoupledDESystem_sound`. The `*_of_check` lemmas here remain as the self-certifying
intermediate (and the route the §8.4 tangent box still uses, pending its telescoping correctness). -/

/-- **★ Base coupled-system soundness from the cleared check** (`coupledClearedCheck_sound`,
`native_decide`-free): if `coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true` then `(y₁, y₂)` solves the base
coupled system at the `ℚ[X]` level — `D(y₁) + b₁·y₁ + C a·(b₂·y₂) = z₁` and `D(y₂) + b₂·y₁ + b₁·y₂ = z₂`
(`D = Polynomial.derivative`, `toPolyG` of each `CPolyG ℚ`). Both conjuncts come from `cisZeroG_iff` on the
two cleared residuals, expanded by the `toPolyG` ring-hom (`toPolyG_csubG`/`caddG`/`cmulG`/`cscaleG`,
`toK = id` on ℚ) and derivation (`toPolyG_cderivG`) bridges, then `linear_combination`. The base-solve
soundness atom, gated only on the engine's own cleared check — the coupled-system analogue of
`field_identity_of_cIntegrateReducedG_of_checkIdentityG`. -/
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
    simp only [toPolyG_csubG, toPolyG_caddG, toPolyG_cmulG, toPolyG_cscaleG, toPolyG_cderivG,
      CFieldSpec.toK, id_eq, sub_eq_zero] at this
    linear_combination this
  · have := h2
    simp only [toPolyG_csubG, toPolyG_caddG, toPolyG_cmulG, toPolyG_cderivG,
      sub_eq_zero] at this
    linear_combination this

/-- **★ Base coupled-system soundness from a self-certifying solve** (`cCoupledDESystem_sound_of_check`,
`native_decide`-free): if `cCoupledDESystem fuel a b1 b2 z1 z2 d = some (y1, y2)` AND the returned pair
passes the engine's own cleared check (`coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true`), then `(y₁, y₂)`
solves the base coupled system at the `ℚ[X]` level. Pure composition with `coupledClearedCheck_sound`.
The cleared check is now *dischargeable* (`coupledClearedCheck_of_cCoupledDESystem`, via the proven
`cConstSolveUniqueQ_sound`), so the gate-free **`cCoupledDESystem_sound`** (`ComputableCoupledDEAssembly`)
subsumes this lemma; it is kept as the self-certifying intermediate. -/
theorem cCoupledDESystem_sound_of_check (fuel : ℕ) (a : ℚ) (b1 b2 z1 z2 : CPolyG ℚ) (d : ℕ)
    (y1 y2 : CPolyG ℚ)
    (_hsome : cCoupledDESystem fuel a b1 b2 z1 z2 d = some (y1, y2))
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (toPolyG y1) + toPolyG b1 * toPolyG y1
        + Polynomial.C a * (toPolyG b2 * toPolyG y2) = toPolyG z1 ∧
      Polynomial.derivative (toPolyG y2) + toPolyG b2 * toPolyG y1
        + toPolyG b1 * toPolyG y2 = toPolyG z2 :=
  coupledClearedCheck_sound a b1 b2 z1 z2 y1 y2 hcheck

-- **Sanity print** (book p.266 step 4): `CoupledDESystem(0, 4x−2, 2−8x², 4−4x) = (−1, 2x+1)`.
#eval (cCoupledDESystem 30 (-1) ([] : CPolyG ℚ) coupledExB2 coupledExZ1 coupledExZ2 1).map
  (fun p => ((p.1 : List ℚ), (p.2 : List ℚ)))

/-- **Example 8.4.1 base coupled solve — `CoupledDESystem` computes over ℚ(x)** (`native_decide`,
Bronstein Ch. 8, book p.266 step 4). The base coupled system (`a = −1`)
`(Dy₁; Dy₂) + [[0, −(4x−2)], [4x−2, 0]] · (y₁; y₂) = (2−8x²; 4−4x)` is solved by the polynomial ansatz,
returning `(s₁, s₂) = (−1, 2x+1)`, the book's value (book p.266 step 4). The returned pair is verified to
**actually solve** the system by `coupledClearedCheck` (both cleared row identities vanish), not merely
pinned. This is the Ch. 8 coupled-system core *computing* over the base field ℚ(x). -/
theorem coupledDESystem_example :
    (match cCoupledDESystem 30 (-1) ([] : CPolyG ℚ) coupledExB2 coupledExZ1 coupledExZ2 1 with
      | some (y1, y2) =>
          coupledClearedCheck (-1) [] coupledExB2 coupledExZ1 coupledExZ2 y1 y2
      | none => false) = true := by native_decide

#print axioms coupledDESystem_example

/-! ### ★ The `t`-polynomial bivariate bridge `toPoly2 : ℚ[x][t]` (for the tangent cleared check)

A `t`-polynomial `p : List (CPolyG ℚ)` (coefficient `p.getD k []` of `tᵏ`, each in `ℚ[x] = CPolyG ℚ`)
reads into `(ℚ[X])[X]` (`ℚ[x][t]`, outer = `t`, inner = `x`) via `toPoly2 p = Σ_k C(toPolyG p_k)·tᵏ`.
The §8.4 tangent cleared-check operations (`tadd`/`tsub`/`tanDeriv`/`mulConst`/`mulT`) become the
`ℚ[x][t]` ring operations and the tangent derivation `D = ∂/∂x + (t²+1)·∂/∂t`, so a passing
`cancelTanClearedCheck` lifts to a genuine `ℚ[x][t]` polynomial identity (the route is `native_decide`-free). -/

open CPolyG in
/-- **Bivariate bridge `List (CPolyG ℚ) → ℚ[x][t]`** `toPoly2 p`: Horner over `t` of the `ℚ[x]`-coefficient
list `p`, each coefficient `toPolyG`'d into `ℚ[X]` and embedded by `C : ℚ[X] → (ℚ[X])[X]`. `toPoly2 (c :: cs)
= C(toPolyG c) + X·toPoly2 cs`; the `t`-polynomial `Σ_k p_k·tᵏ` over the base ring `ℚ[x]`. -/
noncomputable def toPoly2 : List (CPolyG ℚ) → Polynomial (Polynomial ℚ)
  | [] => 0
  | c :: cs => Polynomial.C (toPolyG c) + Polynomial.X * toPoly2 cs

@[simp] theorem toPoly2_nil : toPoly2 [] = 0 := rfl

@[simp] theorem toPoly2_cons (c : CPolyG ℚ) (cs : List (CPolyG ℚ)) :
    toPoly2 (c :: cs) = Polynomial.C (toPolyG c) + Polynomial.X * toPoly2 cs := rfl

/-- **`toPoly2` as an explicit `getD`-sum over any padding length `N ≥ p.length`**: `toPoly2 p = Σ_{k<N}
C(toPolyG (p.getD k []))·Xᵏ`. The padding terms (`k ≥ p.length`) vanish (`p.getD k [] = []`, `toPolyG [] =
0`). The shape the `range`-map list operations (`tadd`/`tsub`/`mulT`) reduce to. -/
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

/-- **`getD` of a `range`-map within range** `((List.range n).map f).getD k [] = f k` for `k < n`. The
indexing lemma the `range`-map `t`-polynomial operations (`tadd`/`tsub`/`mulT`) read back through. -/
theorem getD_range_map (f : ℕ → CPolyG ℚ) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f).getD k [] = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- **`getD` past the end of a `t`-polynomial is `[]`** `p.getD k [] = []` for `p.length ≤ k`. The
out-of-range coefficient (zero) of the §8.4 list operations. -/
theorem getD_out (p : List (CPolyG ℚ)) (k : ℕ) (hk : p.length ≤ k) : p.getD k [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl

open CPolyG in
/-- **`toPoly2` kills a `tisZero` `t`-polynomial**: if `tisZero p = true` (every `ℚ[x]`-coefficient zero)
then `toPoly2 p = 0`. Each coefficient `toPolyG`'s to `0` (`cisZeroG_iff` via `List.all`). -/
theorem toPoly2_eq_zero_of_tisZero (p : List (CPolyG ℚ)) (h : tisZero p = true) :
    toPoly2 p = 0 := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    rw [tisZero, List.all_cons, Bool.and_eq_true] at h
    rw [toPoly2_cons, (cisZeroG_iff c).mp h.1, map_zero, ih h.2, mul_zero, add_zero]

open CPolyG in
/-- **`toPoly2` is additive on `tadd`**: `toPoly2 (tadd p q) = toPoly2 p + toPoly2 q`. Both sides expand to
the `getD`-sum over `N = max p.length q.length`; the coefficient hom is `toPolyG_caddG`. -/
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
/-- **`toPoly2` is subtractive on `tsub`**: `toPoly2 (tsub p q) = toPoly2 p − toPoly2 q`. As `toPoly2_tadd`,
with `toPolyG_csubG`. -/
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
/-- **The `t`-coefficient of `toPoly2`** `(toPoly2 p).coeff k = toPolyG (p.getD k [])`: the degree-`k`
`t`-coefficient of the bridge is the `ℚ[x]`-image of `p`'s `k`-th coefficient. From the Horner form
(`coeff 0` reads the head, `coeff (k+1)` peels `X·`). The bivariate-coefficient reader for the
`Polynomial.ext` proofs of `mulT`/`tanDeriv`. -/
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
/-- **`toPoly2` of `mulConst`** `toPoly2 (p.map (cmulG s)) = C(toPolyG s) · toPoly2 p`: scaling every
`ℚ[x]`-coefficient by `s` is multiplication by the constant-in-`t` `C(toPolyG s)`. Horner induction with
`toPolyG_cmulG`. (The §8.4 cleared check's `mulConst s p = p.map (cmulG s)`.) -/
theorem toPoly2_map_cmulG (s : CPolyG ℚ) (p : List (CPolyG ℚ)) :
    toPoly2 (p.map (cmulG s)) = Polynomial.C (toPolyG s) * toPoly2 p := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, toPoly2_cons, toPoly2_cons, ih, toPolyG_cmulG, map_mul]
    ring

open CPolyG in
/-- **`toPolyG` of a `caddG`-accumulating `range`-foldl is the running sum** `toPolyG ((List.range n).foldl
(fun acc i => caddG acc (g i)) init) = toPolyG init + Σ_{i<n} toPolyG (g i)`. The `t`-coefficient of `mulT`
is exactly such a foldl (the inner Cauchy-product sum); this turns it into a `Finset.range` sum. -/
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
/-- **`toPoly2` is multiplicative on `mulT`** `toPoly2 (mulT p q) = toPoly2 p · toPoly2 q`, where `mulT` is
the §8.4 cleared check's Cauchy-product (`(mulT p q)_k = Σ_{i≤k} p_i·q_{k−i}`). `Polynomial.ext` on the
`t`-coefficient: LHS `coeff k = toPolyG ((mulT p q)_k)` (`toPoly2_coeff`), the inner foldl summed by
`toPolyG_foldl_caddG`; RHS `coeff k = Σ_{antidiag k} (toPoly2 p)_i·(toPoly2 q)_j` (`Polynomial.coeff_mul`),
matched via `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`. -/
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
/-- **The formal `t`-derivative list `dpdt` reads coefficientwise** `dpdt.getD k [] = cscaleG ((k:ℚ)+1)
(p.getD (k+1) [])`, where `dpdt = (p.drop 1).zipIdx.map (fun (c,i) => cscaleG (i+1) c)` (the inner
`d/dt` of `tanDeriv`): the degree-`k` coefficient of `dp/dt` is `(k+1)·p_{k+1}`. -/
theorem tanDeriv_dpdt_getD (p : List (CPolyG ℚ)) (k : ℕ) :
    ((p.drop 1).zipIdx.map (fun x => cscaleG ((x.2 : ℚ) + 1) x.1)).getD k []
      = cscaleG ((k : ℚ) + 1) (p.getD (k + 1) []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_drop,
    List.getD_eq_getElem?_getD, show (0 + k) = k from by ring, show (1 + k) = (k + 1) from by ring]
  cases p[k + 1]? with
  | none => simp [cscaleG]
  | some a => simp

open CPolyG in
/-- **`toPoly2` of the formal `t`-derivative is the outer derivative** `toPoly2 dpdt = D_t (toPoly2 p)`
(`Polynomial.derivative`), for `dpdt` the §8.4 `dp/dt` list. `Polynomial.ext` on the `t`-coefficient:
`(toPoly2 dpdt)_k = C((k+1):ℚ)·toPolyG p_{k+1}` (`tanDeriv_dpdt_getD` + `toPolyG_cscaleG`), matching
`(D_t (toPoly2 p))_k = (toPoly2 p)_{k+1}·(k+1)` (`Polynomial.coeff_derivative`). -/
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
/-- **`toPoly2` of the `(t²+1)·dp/dt` shift** `toPoly2 mulDt = (X²+1)·toPoly2 dpdt`, for `mulDt` the §8.4
`(t²+1)·dpdt` list `(range (dpdt.length+2)).map (fun k => caddG (dpdt_{k−2} if k≥2) dpdt_k)`.
`Polynomial.ext`: coeff `k` of LHS is `toPolyG(dpdt_{k−2}) + toPolyG(dpdt_k)` (`getD_range_map` + `caddG`),
matching `((X²+1)·toPoly2 dpdt)_k = (toPoly2 dpdt)_{k−2} + (toPoly2 dpdt)_k`. -/
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
/-- **★ The tangent derivation `tanDeriv` is the bivariate `D = ∂/∂x + (t²+1)·∂/∂t`** `toPoly2 (tanDeriv p)
= toPoly2 (p.map cderivQ) + (X²+1)·D_t(toPoly2 p)` over `ℚ[x][t]`. `tanDeriv p` is definitionally `tadd κ
mulDt` with `κ = p.map cderivQ` (coefficientwise `d/dx`) and `mulDt = (t²+1)·dpdt`; `toPoly2_tadd` splits it,
`toPoly2_mulDt` gives the `(X²+1)·` factor, `toPoly2_dpdt` reads `dpdt` as the outer `t`-derivative. The
faithful `ℚ[x][t]` semantics of the §8.4 tangent monomial derivation (`Dt = t²+1`). -/
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

The §6.6 dispatcher in `ComputableRischDE` deferred `PolyRischDECancelTan`. Here it runs: the system
(8.15) of Example 8.4.1 over `t = tan(x)`, with `b₀ = 0`, `b₂ = 4x`, `c₁ = −t²+2t−8x²+1`,
`c₂ = 2(1−2x) = 2−4x`, degree bound `n = 2`. The matrix diagonal `−2t = −n·η·t` (`n = 2`, `η = 1`) is the
tangent shift. -/

/-- Example 8.4.1's `c₁ = −t²+2t−8x²+1` as a `t`-polynomial (coefficients in `ℚ[x]`, low→high in `t`):
`t⁰ ↦ 1−8x²`, `t¹ ↦ 2`, `t² ↦ −1`. -/
def cancelTanC1 : List (CPolyG ℚ) := [[1, 0, -8], [2], [-1]]
/-- Example 8.4.1's `c₂ = 2(1−2x) = 2−4x` as a `t`-polynomial (constant in `t`): `t⁰ ↦ 2−4x`. -/
def cancelTanC2 : List (CPolyG ℚ) := [[2, -4]]

/-- **Cleared tangent-system check** `cancelTanClearedCheck b0 b2 c1 c2 q1 q2`: `true` iff `(q₁, q₂)`
solves the `t`-polynomial system `(Dq₁; Dq₂) + [[b₀−2t, −b₂],[b₂, b₀−2t]](q₁; q₂) = (c₁; c₂)`
(`a = −1`, `n = 2`, `η = 1`, `D = tanDeriv`), checked as the two cleared `t`-polynomial identities
(`tisZero` of each residual; `ℚ[x]`-coefficient arithmetic is exact). This is exactly the displayed
system (8.15) of Example 8.4.1 — `[[−2t, −4x], [4x, −2t]]` — the symmetric eq-8.2 form `[[f₁, af₂],
[f₂, f₁]]` with `f₁ = b₀ − nηt = −2t` on **both** diagonals. *(Bronstein's `CoupledDECancelTan` box
prints the (2,2) entry as `b₀ + nηt`; the worked Example 8.4.1's system (8.15) — and the eq-8.2 real
form of `Dy + by = c`, where `f₁` sits on both diagonals — has `b₀ − nηt` there, so the box's `+` is a
misprint for `−`.)* -/
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
/-- **`toPoly2` of the `2t` shift literal** `toPoly2 [[],[2]] = C(C 2)·X` (the `2t` of the §8.4 diagonal,
as a `ℚ[x][t]` polynomial). -/
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
/-- **★ Tangent cleared-system soundness from the engine's own check** (`cancelTanClearedCheck_sound`,
`native_decide`-free): if `cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true` then `(q₁, q₂)` solves the §8.4
tangent `t`-polynomial system at the `ℚ[x][t]` level — both rows of `(Dq; …) + [[b₀−2t, −b₂],[b₂, b₀−2t]]·q
= c`, with `D = tanDeriv` realized as `∂/∂x + (t²+1)·∂/∂t` (`toPoly2_tanDeriv`). Each row comes from
`toPoly2_eq_zero_of_tisZero` on the cleared residual, expanded by the bivariate bridge
(`toPoly2_tsub`/`tadd`/`tanDeriv`/`map_cmulG`/`mulT`/`twoT`), then `linear_combination`. As with the base
solve, the self-check is `native_decide`-reachable (`rischDE_cancelTan_example`) while THIS bridge to the
genuine `ℚ[x][t]` identity is `native_decide`-FREE — the tangent telescoping closed through the engine's own
certificate. -/
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

/-- **★ Tangent RDE cancellation soundness from a self-certifying solve** (`cCoupledDECancelTan_sound_of_check`,
`native_decide`-free): if `cCoupledDECancelTan fuel dbound b0 b2 c1 c2 n = some (q1, q2)` AND the returned
pair passes the engine's own cleared check (`cancelTanClearedCheck b0 b2 c1 c2 q1 q2 = true`, the
`native_decide`-reachable self-certificate, cf. `rischDE_cancelTan_example`), then `(q₁, q₂)` solves the §8.4
tangent coupled `t`-polynomial system at the `ℚ[x][t]` level. Pure composition with
`cancelTanClearedCheck_sound`. The §8.4 degree-by-degree telescoping (each peeled leading pair from the base
`cCoupledDESystem` solve, then the `t − √−1` RHS reduction) enters only through this self-check. **The
cleared check is now *dischargeable*** (`cancelTanClearedCheck_of_reconstruct`, via the proven telescoping
reconstruction `reconstruct` in `ComputableCoupledDETangentReconstruct`), so the gate-free **unconditional**
`cCoupledDECancelTan_sound` (same file) subsumes this lemma at `n = 2`; it is kept as the self-certifying
intermediate. -/
theorem cCoupledDECancelTan_sound_of_check (fuel dbound : ℕ) (b0 b2 : CPolyG ℚ)
    (c1 c2 q1 q2 : List (CPolyG ℚ)) (n : ℕ)
    (_hsome : cCoupledDECancelTan fuel dbound b0 b2 c1 c2 n = some (q1, q2))
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
#eval (cCoupledDECancelTan 30 1 ([] : CPolyG ℚ) [0, 4] cancelTanC1 cancelTanC2 2).map
  (fun p => (p.1.map (fun c => (c : List ℚ)), p.2.map (fun c => (c : List ℚ))))

/-- **Example 8.4.1 — the tangent RDE cancellation `PolyRischDECancelTan` runs end-to-end**
(`native_decide`, Bronstein §8.4, book p.265–267). This is the case `ComputableRischDE`'s §6.6
dispatcher **deferred** (the nonlinear/hypertangent cancellation `δ = 2`, needing the Ch. 8 coupled
system). For the system (8.15) over `t = tan(x)` — `b₀ = 0`, `b₂ = 4x`, the diagonal `−2t = −nηt`
(`n = 2`, `η = 1`), `c₁ = −t²+2t−8x²+1`, `c₂ = 2(1−2x) = 2−4x`, degree bound `n = 2` —
`cCoupledDECancelTan` recurses on `n` (projecting mod `t²+1`, base-solving over ℚ(x), dividing by
`t − √−1`) and returns the book's solution `q₁ = t − 1`, `q₂ = 2x` (hence `y₁ = (t−1)/(t²+1)`,
`y₂ = 2x/(t²+1)`, book p.267). The returned `(q₁, q₂)` is verified to **actually solve** the coupled
`t`-polynomial system (8.15) by `cancelTanClearedCheck` (both cleared row identities vanish), not merely
pinned. The tangent cancellation that finished the RDE oracle's last gap now **computes** over the
tower. -/
theorem rischDE_cancelTan_example :
    (match cCoupledDECancelTan 30 1 ([] : CPolyG ℚ) [0, 4] cancelTanC1 cancelTanC2 2 with
      | some (q1, q2) =>
          cancelTanClearedCheck [] [0, 4] cancelTanC1 cancelTanC2 q1 q2
      | none => false) = true := by native_decide

#print axioms rischDE_cancelTan_example

/-! ### ★ Restatements of the abstract soundness against the intended wording (anonymous `example`s)

The base-solve and tangent soundness lemmas, restated against their meaning: from the engine's own cleared
check the returned `t`-polynomials solve the genuine coupled differential systems over `ℚ[x]` / `ℚ[x][t]`,
`native_decide`-free. The `#print axioms` below confirm these bridges carry only the standard logical
axioms (NO `native_decide` compiler axiom — that appears only on the `example`-validation theorems). -/

open CPolyG

-- ★ Base coupled-system soundness, `native_decide`-free: a self-certifying `cCoupledDESystem` solve gives
-- the two `ℚ[X]` row identities `D(y₁) + b₁y₁ + a·b₂y₂ = z₁`, `D(y₂) + b₂y₁ + b₁y₂ = z₂`.
example (fuel : ℕ) (a : ℚ) (b1 b2 z1 z2 y1 y2 : CPolyG ℚ) (d : ℕ)
    (hsome : cCoupledDESystem fuel a b1 b2 z1 z2 d = some (y1, y2))
    (hcheck : coupledClearedCheck a b1 b2 z1 z2 y1 y2 = true) :
    Polynomial.derivative (toPolyG y1) + toPolyG b1 * toPolyG y1
        + Polynomial.C a * (toPolyG b2 * toPolyG y2) = toPolyG z1 ∧
      Polynomial.derivative (toPolyG y2) + toPolyG b2 * toPolyG y1
        + toPolyG b1 * toPolyG y2 = toPolyG z2 :=
  cCoupledDESystem_sound_of_check fuel a b1 b2 z1 z2 d y1 y2 hsome hcheck

-- ★ Tangent RDE cancellation soundness, `native_decide`-free: a self-certifying `cCoupledDECancelTan` solve
-- gives both rows of the §8.4 tangent coupled `t`-system over `ℚ[x][t]` (`D = ∂/∂x + (t²+1)∂/∂t`).
example (fuel dbound : ℕ) (b0 b2 : CPolyG ℚ) (c1 c2 q1 q2 : List (CPolyG ℚ)) (n : ℕ)
    (hsome : cCoupledDECancelTan fuel dbound b0 b2 c1 c2 n = some (q1, q2))
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
  cCoupledDECancelTan_sound_of_check fuel dbound b0 b2 c1 c2 q1 q2 n hsome hcheck

#print axioms coupledClearedCheck_sound
#print axioms cancelTanClearedCheck_sound

end DeepWiki.SymbolicIntegration
