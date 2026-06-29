import DeepWiki.SymbolicIntegration.ComputableParametric
import DeepWiki.SymbolicIntegration.ComputableTowerField

/-! # Computable structure decision: are exp/log monomials a genuine tower? (Bronstein Chapter 9)

Bronstein, *Symbolic Integration I*, Chapter 9 ("Structure Theorems", book p.269–296) decides the
**algebraic structure** of a set of exp/log monomials over a differential field: whether a candidate
`log(u)` or `exp(u)` is a *new transcendental monomial* over the field already built, or whether it
satisfies a relation (so it is algebraic / redundant). The two structure theorems and their decision
corollaries are:

* **§9.3 The Risch Structure Theorem** (Theorem 9.3.1, book p.283, after Risch [77]). Let `C` be a
  field, `x` transcendental over `C`, and `(K, D)` an elementary extension of `(C(x), d/dx)` with
  `Const_D(K) = C`. Write `K = C(x)(t₁,…,tₙ)`, with the index sets (eq. 9.6/9.7, book p.282)
  ```
    E_{K/C(x)} = {i : tᵢ transcendental over C(x)(t₁,…,t_{i-1}), Dtᵢ/tᵢ = Daᵢ, aᵢ ∈ …}   (exponentials)
    L_{K/C(x)} = {i : tᵢ transcendental over C(x)(t₁,…,t_{i-1}), Dtᵢ  = Daᵢ/aᵢ, aᵢ ∈ …*}  (logarithms)
  ```
  If there are `v ∈ K` and `u ∈ K*` with `Dv = Du/u`, then there are `rᵢ ∈ ℚ` with
  `v + Σ_{i∈L} rᵢtᵢ + Σ_{i∈E} rᵢaᵢ ∈ C` (where `tᵢ = exp(aᵢ)` for `i ∈ E`).

* **Corollary 9.3.1** (book p.284, the **decision criterion**). For `a ∈ K*`, `b ∈ K`:
  - **(i)** `Da/a` is the derivative of an element of `K` **iff** there are `rᵢ ∈ ℚ` with
    `Σ_{i∈L} rᵢ Dtᵢ + Σ_{i∈E} rᵢ (Dtᵢ/tᵢ) = Da/a`                                            (9.8)
  - **(ii)** `Db` is the logarithmic derivative of a `K`-radical **iff** there are `rᵢ ∈ ℚ` with
    `Σ_{i∈L} rᵢ Dtᵢ + Σ_{i∈E} rᵢ (Dtᵢ/tᵢ) = Db`                                              (9.9)

  The algorithms follow (book p.285, via Theorems 5.1.1/5.1.2): a new **logarithm** `log(a)` (`Dt =
  Da/a`) is a *new monomial* over `K` (transcendental, same constants) **unless** `Da/a` is the
  derivative of an element of `K` — i.e. unless (9.8) has a ℚ-solution; a new **exponential** `exp(b)`
  (`Dt/t = Db`) is a *new monomial* **unless** `Db` is the logarithmic derivative of a `K`-radical —
  i.e. unless (9.9) has a ℚ-solution.

* **§9.4 The Rothstein–Caviness Structure Theorem** (Theorem 9.4.1, book p.293, after Rothstein &
  Caviness [84]). The **same** statement and decision corollary (Corollary 9.4.1, eq. 9.21/9.22 ≡
  9.8/9.9) for *log-explicit Liouvillian* extensions (the book: "The proof and corresponding algorithms
  are exactly the same than for Corollary 9.3.1"). It lifts the Risch structure decision off
  *elementary* towers onto the wider Liouvillian class the integration algorithm actually meets.

## The computable core delivered here (over `k = ℚ(x)`, the reachable base; `native_decide`-validated)

For a **logarithmic tower** `C(x)(log u₁, …, log uₘ)` — every `tᵢ ∈ L`, no exponentials — the new-log
test (9.8) collapses to a **ℚ-linear-dependence test among the logarithmic derivatives** `wᵢ = Duᵢ/uᵢ ∈
ℚ(x)`: a candidate `log(u)` (`w = Du/u`) is a *new transcendental monomial* over `C(x)(log u₁,…,log uₘ)`
**iff** `w ∉ span_ℚ{w₁,…,wₘ}` (there are no `rᵢ ∈ ℚ` with `Du/u = Σ rᵢ Duᵢ/uᵢ`). That is exactly the
worked relation `log(x²) = 2 log(x)` ⟺ `D(x²)/x² = 2·D(x)/x` (dependent) versus `log(x), log(x+1)`
(independent). The `span_ℚ` test is *honest computable ℚ-linear algebra*: clear the rational functions
`{w₁,…,wₘ,w}` to a common denominator, equate numerator coefficients, and run the §7.1 nullspace solver
`cNullspaceBasisQ` (`crref` over ℚ) — `w` is dependent iff a relation has nonzero `w`-coefficient.

* **`cLogIsNewMonomial`** — decides whether a candidate `log(u)` is a *new* monomial vs. a ℚ-linear
  relation among the existing logarithmic derivatives, per Corollary 9.3.1(i). The arguments arrive as
  the logarithmic derivatives `Duᵢ/uᵢ` (already reduced `QFunNZG ℚ` values), which the caller builds from
  the `uᵢ`.
* **`cExpIsNewMonomial`** — the exponential analogue (Corollary 9.3.1(ii)): a candidate `exp(b)` is a
  *new* monomial **unless** `Db` is the logarithmic derivative of a `K`-radical, i.e. (over the
  reachable base, where there are no exponential monomials to combine with) unless `Db ∈ span_ℚ{Duᵢ/uᵢ}`
  — the *same* ℚ-linear-dependence test, now on `Db` against the existing logarithmic derivatives.

## What is documented / deferred

The **full** Risch / Rothstein–Caviness structure theorem keeps both index sets `E` and `L`
simultaneously and the general nested tower `C(x)(t₁,…,tₙ)`: the test (9.8)/(9.9) ranges over
`Σ_{i∈L} rᵢ Dtᵢ + Σ_{i∈E} rᵢ (Dtᵢ/tᵢ)`, so over a genuine tower the matrix entries lie in the *upper*
field `C(x)(t₁,…,t_{i-1})` and one recurses level by level (the "algorithms following Corollary 9.3.1",
book p.285, threading the §5.1 integration result `Dv = Du/u`). The reachable base case `k = ℚ(x)` (a
*single* level of log/exp monomials over `ℚ(x)`, `Const = ℚ`) is what lands here, the level the §5.12 /
§6.6 callers actually reach. The general multi-level recursion, the `exp`-of-radical witness
construction (the §5.12 in-field integration), the √−1 / arc-tangent tower of Lemmas 9.3.2/9.3.3, and
the §9.1 module of differentials (`Ω_{K/k}`, Mathlib `KaehlerDifferential`) underpinning the proofs are
the documented continuation. No abstract correctness is proved (the structure theorem `Dv = Du/u ↔ …` is
not formalized); every landed decision is `native_decide`-validated on its cleared ℚ-linear relation.
No `sorry`. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

namespace CPolyG

/-! ### The ℚ-linear-dependence test among rational-function logarithmic derivatives

Corollary 9.3.1(i)/(ii) (eq. 9.8/9.9) reduce, for a *logarithmic* tower over `ℚ(x)` (the reachable
base), to: is the rational function `w` in the ℚ-linear span of `w₁,…,wₘ`? A ℚ-relation
`r·w = Σ rᵢ wᵢ` (`r, rᵢ ∈ ℚ`) holds **iff**, after clearing all the `wⱼ ∈ ℚ(x)` to a common denominator
`d = lcm(denominators)` so each becomes a numerator polynomial `nⱼ = wⱼ·d ∈ ℚ[x]`, the *coefficient
vectors* of `{n₁,…,nₘ, n}` are ℚ-linearly dependent with a relation that uses `n` (the last column)
nontrivially. We assemble the coefficient matrix (one **column** per `wⱼ`, one **row** per `x`-power up
to the max degree) and run the §7.1 nullspace solver `cNullspaceBasisQ`. -/

/-- **Coefficient column of a `QFunNZG ℚ` cleared to a common denominator.** `cClearedNumCoeffs d w`
returns the dense `ℚ`-coefficient list of the polynomial `w·d ∈ ℚ[x]` (well-defined as a polynomial
because `d` is a common multiple of `w`'s denominator), via `qnormPairG`-reducing `w` first then
`numerator·(d/denom)`.
The `LinearConstraints`-style clearing (cf. §7.1): a ℚ-relation `Σ rⱼ wⱼ = 0` becomes the polynomial
relation `Σ rⱼ (wⱼ·d) = 0`, i.e. a ℚ-linear relation among these coefficient lists. -/
def cClearedNumCoeffs (fuel : ℕ) (d : CPolyG ℚ) (w : QFunNZG ℚ) : CPolyG ℚ :=
  let wn := qnormPairG fuel w.1.1 w.1.2            -- `w` in lowest terms `(a, b)`
  -- `w·d = a·(d / b)` as a polynomial (`b ∣ d` since `d` is a common multiple of all denominators).
  cmulG wn.1 (cdivG fuel d wn.2)

/-- **The ℚ-linear span / dependence engine** `cLinearDepData fuel ws w = (matrix, m)` for the rational
functions `ws = [w₁,…,wₘ]` and a candidate `w`, over `k = ℚ(x)`. Clears all of `w₁,…,wₘ,w` to the common
denominator `d = lcm(all denominators)` (so each `wⱼ·d ∈ ℚ[x]`), assembles the **coefficient matrix**
`M` whose row `i` is `[coeff(w₁·d, xⁱ), …, coeff(wₘ·d, xⁱ), coeff(w·d, xⁱ)]` (`m+1` columns, one per
generator with `w` last; rows `i = 0 .. maxdeg`), and returns `(M, m)`. A ℚ-relation `Σ rⱼ wⱼ + r·w = 0`
is exactly a nullspace vector of `M`; `w ∈ span_ℚ{wⱼ}` iff some nullspace vector has nonzero last
(`w`-)coordinate. -/
def cLinearDepData (fuel : ℕ) (ws : List (QFunNZG ℚ)) (w : QFunNZG ℚ) :
    List (List ℚ) × ℕ :=
  let all := ws ++ [w]
  -- common denominator `d = lcm(denom wⱼ)` over the lowest-terms forms.
  let dens := all.map (fun u => (qnormPairG fuel u.1.1 u.1.2).2)
  let d := dens.foldl (fun acc den => cLcmQ fuel acc den) [(1 : ℚ)]
  let cols : List (CPolyG ℚ) := all.map (fun u => cClearedNumCoeffs fuel d u)
  let nrows := (cols.map cdegG).foldl Nat.max 0 + 1
  let M : List (List ℚ) :=
    (List.range nrows).map (fun i =>
      cols.map (fun c => (cnormG c).getD i 0))
  (M, ws.length)

/-- **The new-logarithm structure decision** `cLogIsNewMonomial fuel logDerivs w` (Bronstein §9.3,
Corollary 9.3.1(i), eq. 9.8, book p.284/285), over the logarithmic tower `C(x)(log u₁,…,log uₘ)`,
`k = ℚ(x)`, `Const = ℚ`. Given the logarithmic derivatives `logDerivs = [Du₁/u₁, …, Duₘ/uₘ] ∈ ℚ(x)` of
the existing log-monomials and a candidate `log(u)`'s logarithmic derivative `w = Du/u ∈ ℚ(x)`, returns
`true` iff `log(u)` is a **new transcendental monomial** over `C(x)(log u₁,…,log uₘ)` — i.e. iff `Du/u`
is **not** the derivative of an element of the field, i.e. iff there are **no** `rᵢ ∈ ℚ` with
`Du/u = Σ rᵢ (Duᵢ/uᵢ)` (eq. 9.8 with the exponential part `E` empty). Decided by the §7.1 ℚ-nullspace
solver: `cNullspaceBasisQ` of the cleared coefficient matrix; `log(u)` is **dependent** (NOT new) iff
some kernel vector uses the `w`-column (last coordinate) nontrivially. Returns `true` (NEW) when no such
relation exists. -/
def cLogIsNewMonomial (fuel : ℕ) (logDerivs : List (QFunNZG ℚ)) (w : QFunNZG ℚ) : Bool :=
  let (M, m) := cLinearDepData fuel logDerivs w
  let basis := cNullspaceBasisQ M (m + 1)
  -- `log(u)` is a *new* monomial iff NO nullspace relation involves the `w`-column (index `m`).
  !(basis.any (fun rel => rel.getD m 0 ≠ 0))

/-- **The new-exponential structure decision** `cExpIsNewMonomial fuel logDerivs b` (Bronstein §9.3,
Corollary 9.3.1(ii), eq. 9.9, book p.284/285), over `k = ℚ(x)`, `Const = ℚ`. Given a candidate
`exp(b)`'s exponent derivative `Db ∈ ℚ(x)` and the existing logarithmic derivatives `logDerivs =
[Du₁/u₁,…]`, returns `true` iff `exp(b)` is a **new transcendental monomial** — i.e. iff `Db` is **not**
the logarithmic derivative of a `K`-radical, i.e. (over the reachable base, where `K` has no exponential
monomials yet to contribute the `E`-part of eq. 9.9) iff there are **no** `rᵢ ∈ ℚ` with
`Db = Σ rᵢ (Duᵢ/uᵢ)`. This is the *same* ℚ-linear-dependence test as the logarithm case, now applied to
the exponent derivative `Db` against the existing logarithmic derivatives (eq. 9.9 with the
exponential-monomial part of the span empty at the base). -/
def cExpIsNewMonomial (fuel : ℕ) (logDerivs : List (QFunNZG ℚ)) (b : QFunNZG ℚ) : Bool :=
  cLogIsNewMonomial fuel logDerivs b

/-- **Membership form** `cLogRelationExists fuel logDerivs w = !cLogIsNewMonomial …`: `true` iff
`w = Du/u` **is** a ℚ-linear combination of the existing logarithmic derivatives — i.e. `log(u)` is
*dependent* (a relation exists, eq. 9.8 solvable). The complement of `cLogIsNewMonomial`, exposed for the
validation against the worked `log(x²) = 2 log(x)` relation. -/
def cLogRelationExists (fuel : ℕ) (logDerivs : List (QFunNZG ℚ)) (w : QFunNZG ℚ) : Bool :=
  !cLogIsNewMonomial fuel logDerivs w

/-- **The ℚ-relation coefficients (if a single relation pins them)** `cLogRelationCoeffs fuel logDerivs
w`: when `cLogRelationExists` and the kernel is one-dimensional with a nonzero `w`-coordinate, returns
`some [r₁,…,rₘ]` with `Du/u = Σ rᵢ (Duᵢ/uᵢ)` (normalizing the `w`-column coefficient to `−1`, so the
kernel vector reads `[r₁,…,rₘ, −1]`); else `none`. The explicit `rᵢ ∈ ℚ` of eq. 9.8 — e.g. `[2]` for
`log(x²) = 2 log(x)`. -/
def cLogRelationCoeffs (fuel : ℕ) (logDerivs : List (QFunNZG ℚ)) (w : QFunNZG ℚ) : Option (List ℚ) :=
  let (M, m) := cLinearDepData fuel logDerivs w
  let basis := cNullspaceBasisQ M (m + 1)
  match basis.find? (fun rel => rel.getD m 0 ≠ 0) with
  | none => none
  | some rel =>
    let wc := rel.getD m 0                          -- the `w`-column coefficient `r` in `Σ rⱼwⱼ + r·w = 0`
    -- `Du/u = Σ (−rⱼ/r) (Duⱼ/uⱼ)`: solve `r·w = −Σ rⱼ wⱼ` for `w`.
    some ((List.range m).map (fun j => - (rel.getD j 0) / wc))

end CPolyG

/-! ### Validation — Bronstein §9.3 / Corollary 9.3.1: the logarithmic-monomial structure decision

The reachable base: `k = ℚ(x)`, `D = d/dx`, a logarithmic tower over `ℚ(x)`. The logarithmic
derivatives are rational functions in `ℚ(x)` (so `QFunNZG ℚ` values):

* `log(x)`        ⟹ `D(x)/x   = 1/x`           ⟹ `[1]/[0,1]`
* `log(x²)`       ⟹ `D(x²)/x² = 2x/x² = 2/x`   ⟹ `[2]/[0,1]`     (equals `2·(1/x)`, so DEPENDENT)
* `log(x+1)`      ⟹ `D(x+1)/(x+1) = 1/(x+1)`   ⟹ `[1]/[1,1]`     (INDEPENDENT of `1/x`)

The worked Risch structure relation `log(x²) = 2 log(x)` is `D(x²)/x² = 2·D(x)/x`, i.e. the candidate
`log(x²)`'s logarithmic derivative `2/x` *is* `2·` the existing `D(x)/x = 1/x` — a ℚ-linear relation
(coefficient `r₁ = 2`), so `cLogIsNewMonomial` returns `false` (not a new monomial). Against `log(x)`,
the candidate `log(x+1)` with `1/(x+1) ∉ span_ℚ{1/x}` is a **new** transcendental monomial
(`cLogIsNewMonomial = true`). -/

open CPolyG

/-- A ℚ(x) fraction `num/den` as a `QFunNZG ℚ` element (the validation coefficient builder, mirroring
`QFunNZ.ofNumDen` one tower level down; `den ≠ 0` by `native_decide`). -/
def qFracStructG (num den : List ℚ) (h : CPolyG.cisZeroG den = false := by native_decide) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-- `D(x)/x = 1/x`: the logarithmic derivative of `log(x)`. Numerator `[1]`, denominator `x = [0,1]`. -/
def structLogDerivX : QFunNZG ℚ := qFracStructG [1] [0, 1]
/-- `D(x²)/x² = 2/x`: the logarithmic derivative of `log(x²)`. Numerator `[2]`, denominator `x = [0,1]`
(`2x/x² = 2/x`). Equal to `2·structLogDerivX`, so `log(x²) = 2 log(x)` is a ℚ-linear relation. -/
def structLogDerivX2 : QFunNZG ℚ := qFracStructG [2] [0, 1]
/-- `D(x+1)/(x+1) = 1/(x+1)`: the logarithmic derivative of `log(x+1)`. Numerator `[1]`, denominator
`x+1 = [1,1]`. Independent of `1/x` over ℚ. -/
def structLogDerivX1 : QFunNZG ℚ := qFracStructG [1] [1, 1]

-- **Sanity prints.** Against the existing monomial `log(x)` (`logDerivs = [1/x]`):
--   `log(x²)` (`w = 2/x`) is DEPENDENT (relation `2/x = 2·(1/x)`)  ⟹ `cLogIsNewMonomial = false`;
--   `log(x+1)` (`w = 1/(x+1)`) is a NEW monomial                  ⟹ `cLogIsNewMonomial = true`.
#eval CPolyG.cLogIsNewMonomial 30 [structLogDerivX] structLogDerivX2   -- expect false
#eval CPolyG.cLogIsNewMonomial 30 [structLogDerivX] structLogDerivX1   -- expect true
#eval CPolyG.cLogRelationCoeffs 30 [structLogDerivX] structLogDerivX2  -- expect some [2]

/-- **Cleared ℚ-relation check** `structRelationCheck fuel logDerivs w rs`: `true` iff the ℚ-coefficients
`rs = [r₁,…,rₘ]` actually satisfy `w = Σ rᵢ (Duᵢ/uᵢ)` over `ℚ(x)`, by `CField.isZero` of the cleared
difference `w − Σ rᵢ (logDerivsᵢ)` — the rational-function identity certifying that the detected relation
is genuine (eq. 9.8). -/
def structRelationCheck (logDerivs : List (QFunNZG ℚ)) (w : QFunNZG ℚ) (rs : List ℚ) : Bool :=
  let combo := (List.zip logDerivs rs).foldl
    (fun acc (wi, r) => CField.add acc (CField.mul (qFracStructG [r] [1]) wi)) CField.zero
  CField.isZero (CField.sub w combo)

/-- **Bronstein §9.3 — the logarithmic-monomial structure decision computes** (`native_decide`,
Corollary 9.3.1(i), eq. 9.8, book p.284/285). Over the logarithmic tower `C(x)(log x)` (`k = ℚ(x)`,
`Const = ℚ`, the existing logarithmic derivative `D(x)/x = 1/x`):

1. **`log(x²)` is NOT a new monomial.** `cLogIsNewMonomial` returns `false`: the candidate's logarithmic
   derivative `D(x²)/x² = 2/x` lies in `span_ℚ{1/x}` (the ℚ-linear relation `2/x = 2·(1/x)`, i.e.
   `log(x²) = 2 log(x)`). The detected coefficient `cLogRelationCoeffs = some [2]` is verified to
   **actually satisfy** `D(x²)/x² = 2·D(x)/x` over `ℚ(x)` by `structRelationCheck` (the cleared identity).
2. **`log(x+1)` IS a new monomial.** `cLogIsNewMonomial` returns `true`: `D(x+1)/(x+1) = 1/(x+1) ∉
   span_ℚ{1/x}`, so `log(x+1)` is a new transcendental monomial over `C(x)(log x)`.

This is the §9.3 deliverable: the Risch structure theorem's decision criterion (Corollary 9.3.1(i)) —
*is a candidate `log(u)` a genuine new transcendental, or a ℚ-linear relation among the existing
logarithmic derivatives?* — **computes** over `ℚ(x)` as honest ℚ-linear algebra (`cNullspaceBasisQ` /
`crref`), with the detected relation verified against the rational-function identity. -/
theorem structureTheorem_example :
    (-- (1) `log(x²)` is dependent on `log(x)` — relation detected and verified `D(x²)/x² = 2·D(x)/x`.
     (CPolyG.cLogIsNewMonomial 30 [structLogDerivX] structLogDerivX2 == false)
     && (match CPolyG.cLogRelationCoeffs 30 [structLogDerivX] structLogDerivX2 with
         | some rs => structRelationCheck [structLogDerivX] structLogDerivX2 rs && (rs == [2])
         | none => false)
     -- (2) `log(x+1)` is a NEW transcendental monomial over `C(x)(log x)`.
     && (CPolyG.cLogIsNewMonomial 30 [structLogDerivX] structLogDerivX1 == true)) = true := by
  native_decide

#print axioms structureTheorem_example

/-! ### Validation — the exponential analogue (Corollary 9.3.1(ii), eq. 9.9)

Over `k = ℚ(x)` with the logarithmic monomial `log(x)` present (`D(x)/x = 1/x`): a candidate `exp(b)`
with exponent derivative `Db = 2/x` is **not** a new monomial — `Db = 2·D(x)/x` is the logarithmic
derivative of the `K`-radical `x²` (`exp(2 log x) = x²` is already in the field, up to a constant power),
so `cExpIsNewMonomial = false`. A candidate `exp(b)` with `Db = 1/(x+1) ∉ span_ℚ{1/x}` IS a new
transcendental exponential monomial (`cExpIsNewMonomial = true`). -/

/-- **Bronstein §9.3 — the exponential-monomial structure decision computes** (`native_decide`,
Corollary 9.3.1(ii), eq. 9.9, book p.284/285). Over `C(x)(log x)` (`k = ℚ(x)`):

1. **`exp(b)` with `Db = 2/x` is NOT new.** `cExpIsNewMonomial = false`: `Db = 2/x ∈ span_ℚ{D(x)/x}`
   (`2·(1/x)`), so `Db` is the logarithmic derivative of the radical `x²` — `exp(b)` is `x²` up to a
   constant power, already in the field. The relation `[2]` is verified by `structRelationCheck`.
2. **`exp(b)` with `Db = 1/(x+1)` IS new.** `cExpIsNewMonomial = true`: `1/(x+1) ∉ span_ℚ{1/x}`.

The exponential decision (Corollary 9.3.1(ii)) shares the *same* ℚ-linear-dependence engine as the
logarithm decision, applied to the exponent derivative `Db` against the existing logarithmic
derivatives. -/
theorem expStructureTheorem_example :
    ((CPolyG.cExpIsNewMonomial 30 [structLogDerivX] structLogDerivX2 == false)
     && (match CPolyG.cLogRelationCoeffs 30 [structLogDerivX] structLogDerivX2 with
         | some rs => structRelationCheck [structLogDerivX] structLogDerivX2 rs && (rs == [2])
         | none => false)
     && (CPolyG.cExpIsNewMonomial 30 [structLogDerivX] structLogDerivX1 == true)) = true := by
  native_decide

#print axioms expStructureTheorem_example

/-! ### Validation — independence of `{log(x), log(x+1)}` and a 3-element relation

A check that the engine handles `m > 1`: against the genuine 2-element tower `C(x)(log x, log(x+1))`
(both `1/x` and `1/(x+1)` present, ℚ-independent), the candidate `log(x²)` (`2/x`) is *still* dependent
(`2·(1/x) + 0·(1/(x+1))`), with relation `[2, 0]`; the candidate `log(x²+x) = log(x(x+1)) = log x +
log(x+1)` (`D(x²+x)/(x²+x) = (2x+1)/(x²+x) = 1/x + 1/(x+1)`) is dependent with relation `[1, 1]`. -/

/-- `D(x²+x)/(x²+x) = (2x+1)/(x²+x) = 1/x + 1/(x+1)`: the logarithmic derivative of `log(x²+x)`.
Numerator `2x+1 = [1,2]`, denominator `x²+x = [0,1,1]`. Equals `1·(1/x) + 1·(1/(x+1))`. -/
def structLogDerivX2pX : QFunNZG ℚ := qFracStructG [1, 2] [0, 1, 1]

-- **Sanity prints.** Against the 2-element tower `[1/x, 1/(x+1)]`:
--   `log(x²+x)` (`(2x+1)/(x²+x)`) is DEPENDENT with relation `[1,1]` (`1/x + 1/(x+1)`).
#eval CPolyG.cLogIsNewMonomial 30 [structLogDerivX, structLogDerivX1] structLogDerivX2pX  -- false
#eval CPolyG.cLogRelationCoeffs 30 [structLogDerivX, structLogDerivX1] structLogDerivX2pX -- some [1,1]

/-- **Bronstein §9.3 — multi-monomial structure decision computes** (`native_decide`, Corollary 9.3.1,
book p.284/285). Over the genuine 2-element logarithmic tower `C(x)(log x, log(x+1))` (`k = ℚ(x)`, the
ℚ-independent logarithmic derivatives `1/x` and `1/(x+1)`):

1. `log(x²+x) = log(x(x+1))` is NOT a new monomial — its logarithmic derivative `(2x+1)/(x²+x) = 1/x +
   1/(x+1)` lies in `span_ℚ{1/x, 1/(x+1)}` with relation `[1, 1]`, verified by `structRelationCheck`
   (`log(x²+x) = log x + log(x+1)`).
2. The two existing generators are genuinely **independent**: `log(x)` is a new monomial relative to
   `log(x+1)` alone and vice versa (so the 2-element tower is a real transcendence-degree-2 extension).

This exercises the ℚ-linear-relation engine with `m = 2` generators, confirming the structure decision
scales past the single-generator base. -/
theorem multiStructureTheorem_example :
    (-- `log(x²+x)` is dependent on `{log x, log(x+1)}` with the verified relation `[1,1]`.
     (CPolyG.cLogIsNewMonomial 30 [structLogDerivX, structLogDerivX1] structLogDerivX2pX == false)
     && (match CPolyG.cLogRelationCoeffs 30 [structLogDerivX, structLogDerivX1] structLogDerivX2pX with
         | some rs => structRelationCheck [structLogDerivX, structLogDerivX1] structLogDerivX2pX rs
                        && (rs == [1, 1])
         | none => false)
     -- the two generators are independent of each other.
     && (CPolyG.cLogIsNewMonomial 30 [structLogDerivX1] structLogDerivX == true)
     && (CPolyG.cLogIsNewMonomial 30 [structLogDerivX] structLogDerivX1 == true)) = true := by
  native_decide

#print axioms multiStructureTheorem_example

end DeepWiki.SymbolicIntegration
