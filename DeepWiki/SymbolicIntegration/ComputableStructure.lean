import DeepWiki.SymbolicIntegration.ComputableParametric
import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd
import DeepWiki.SymbolicIntegration.ComputableTowerField

/-! # Structure decision: is a candidate exp/log a new transcendental monomial?

The Risch / Rothstein–Caviness structure decision over a logarithmic tower `C(x)(log u₁,…,log uₘ)`
with base `k = ℚ(x)`: a candidate `log(u)` (or `exp(b)`) is a new transcendental monomial iff its
(logarithmic) derivative is not a ℚ-linear combination of the existing logarithmic derivatives
`Duᵢ/uᵢ ∈ ℚ(x)` — decided by clearing to a common denominator and running the ℚ-nullspace solver
`cNullspaceBasisQ`. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

namespace CPolyG

/-! ### The ℚ-linear-dependence test among rational-function logarithmic derivatives

A ℚ-relation `r·w = Σ rᵢ wᵢ` holds iff, after clearing all `wⱼ ∈ ℚ(x)` to a common denominator
`d = lcm(denominators)`, the coefficient vectors of the numerators `wⱼ·d ∈ ℚ[x]` are ℚ-linearly
dependent with a relation using the `w`-column nontrivially. -/

/-- `cClearedNumCoeffs d w`: the dense `ℚ`-coefficient list of `w·d ∈ ℚ[x]` (well-defined because `d`
is a common multiple of `w`'s denominator), via `qnormPairG`-reducing `w` then `numerator·(d/denom)`. -/
def cClearedNumCoeffs (d : CPolyG ℚ) (w : QFunNZG ℚ) : CPolyG ℚ :=
  let wn := qnormPairG w.1.1 w.1.2            -- `w` in lowest terms `(a, b)`
  -- `w·d = a·(d / b)` as a polynomial (`b ∣ d` since `d` is a common multiple of all denominators).
  cmulG wn.1 (cdivWf d wn.2)

/-- `cLinearDepData ws w = (M, m)`: clear `w₁,…,wₘ,w` to the common denominator `d = lcm(denominators)`
and assemble the coefficient matrix `M` with row `i` = `[coeff(w₁·d, xⁱ), …, coeff(wₘ·d, xⁱ),
coeff(w·d, xⁱ)]` (`w` last). A ℚ-relation `Σ rⱼ wⱼ + r·w = 0` is exactly a nullspace vector of `M`;
`w ∈ span_ℚ{wⱼ}` iff some nullspace vector has nonzero last coordinate. -/
def cLinearDepData (ws : List (QFunNZG ℚ)) (w : QFunNZG ℚ) :
    List (List ℚ) × ℕ :=
  let all := ws ++ [w]
  -- common denominator `d = lcm(denom wⱼ)` over the lowest-terms forms.
  let dens := all.map (fun u => (qnormPairG u.1.1 u.1.2).2)
  let d := dens.foldl (fun acc den => cLcmQ acc den) [(1 : ℚ)]
  let cols : List (CPolyG ℚ) := all.map (fun u => cClearedNumCoeffs d u)
  let nrows := (cols.map cdegG).foldl Nat.max 0 + 1
  let M : List (List ℚ) :=
    (List.range nrows).map (fun i =>
      cols.map (fun c => (cnormG c).getD i 0))
  (M, ws.length)

/-- `cLogIsNewMonomial logDerivs w = true` iff a candidate `log(u)` with logarithmic derivative
`w = Du/u ∈ ℚ(x)` is a new transcendental monomial over `C(x)(log u₁,…,log uₘ)` (`logDerivs =
[Du₁/u₁, …, Duₘ/uₘ]`) — i.e. iff there are no `rᵢ ∈ ℚ` with `Du/u = Σ rᵢ (Duᵢ/uᵢ)`, decided by
`cNullspaceBasisQ` on the cleared coefficient matrix. -/
def cLogIsNewMonomial (logDerivs : List (QFunNZG ℚ)) (w : QFunNZG ℚ) : Bool :=
  let (M, m) := cLinearDepData logDerivs w
  let basis := cNullspaceBasisQ M (m + 1)
  -- `log(u)` is a *new* monomial iff NO nullspace relation involves the `w`-column (index `m`).
  !(basis.any (fun rel => rel.getD m 0 ≠ 0))

/-- **The new-exponential structure decision** `cExpIsNewMonomial logDerivs b` (Bronstein §9.3,
Corollary 9.3.1(ii), eq. 9.9, book p.284/285), over `k = ℚ(x)`, `Const = ℚ`. Given a candidate
`exp(b)`'s exponent derivative `Db ∈ ℚ(x)` and the existing logarithmic derivatives `logDerivs =
[Du₁/u₁,…]`, returns `true` iff `exp(b)` is a **new transcendental monomial** — i.e. iff `Db` is **not**
the logarithmic derivative of a `K`-radical, i.e. (over the reachable base, where `K` has no exponential
monomials yet to contribute the `E`-part of eq. 9.9) iff there are **no** `rᵢ ∈ ℚ` with
`Db = Σ rᵢ (Duᵢ/uᵢ)`. This is the *same* ℚ-linear-dependence test as the logarithm case, now applied to
the exponent derivative `Db` against the existing logarithmic derivatives (eq. 9.9 with the
exponential-monomial part of the span empty at the base). -/
def cExpIsNewMonomial (logDerivs : List (QFunNZG ℚ)) (b : QFunNZG ℚ) : Bool :=
  cLogIsNewMonomial logDerivs b

/-- **Membership form** `cLogRelationExists logDerivs w = !cLogIsNewMonomial …`: `true` iff
`w = Du/u` **is** a ℚ-linear combination of the existing logarithmic derivatives — i.e. `log(u)` is
*dependent* (a relation exists, eq. 9.8 solvable). The complement of `cLogIsNewMonomial`, exposed for the
validation against the worked `log(x²) = 2 log(x)` relation. -/
def cLogRelationExists (logDerivs : List (QFunNZG ℚ)) (w : QFunNZG ℚ) : Bool :=
  !cLogIsNewMonomial logDerivs w

/-- **The ℚ-relation coefficients (if a single relation pins them)** `cLogRelationCoeffs logDerivs
w`: when `cLogRelationExists` and the kernel is one-dimensional with a nonzero `w`-coordinate, returns
`some [r₁,…,rₘ]` with `Du/u = Σ rᵢ (Duᵢ/uᵢ)` (normalizing the `w`-column coefficient to `−1`, so the
kernel vector reads `[r₁,…,rₘ, −1]`); else `none`. The explicit `rᵢ ∈ ℚ` of eq. 9.8 — e.g. `[2]` for
`log(x²) = 2 log(x)`. -/
def cLogRelationCoeffs (logDerivs : List (QFunNZG ℚ)) (w : QFunNZG ℚ) : Option (List ℚ) :=
  let (M, m) := cLinearDepData logDerivs w
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

/-- A ℚ(x) fraction `num/den` as a `QFunNZG ℚ` element (the validation coefficient builder over the
generic ℚ(x) carrier; `den ≠ 0` by `native_decide`). -/
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
#eval CPolyG.cLogIsNewMonomial [structLogDerivX] structLogDerivX2   -- expect false
#eval CPolyG.cLogIsNewMonomial [structLogDerivX] structLogDerivX1   -- expect true
#eval CPolyG.cLogRelationCoeffs [structLogDerivX] structLogDerivX2  -- expect some [2]

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
     (CPolyG.cLogIsNewMonomial [structLogDerivX] structLogDerivX2 == false)
     && (match CPolyG.cLogRelationCoeffs [structLogDerivX] structLogDerivX2 with
         | some rs => structRelationCheck [structLogDerivX] structLogDerivX2 rs && (rs == [2])
         | none => false)
     -- (2) `log(x+1)` is a NEW transcendental monomial over `C(x)(log x)`.
     && (CPolyG.cLogIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
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
    ((CPolyG.cExpIsNewMonomial [structLogDerivX] structLogDerivX2 == false)
     && (match CPolyG.cLogRelationCoeffs [structLogDerivX] structLogDerivX2 with
         | some rs => structRelationCheck [structLogDerivX] structLogDerivX2 rs && (rs == [2])
         | none => false)
     && (CPolyG.cExpIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
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
#eval CPolyG.cLogIsNewMonomial [structLogDerivX, structLogDerivX1] structLogDerivX2pX  -- false
#eval CPolyG.cLogRelationCoeffs [structLogDerivX, structLogDerivX1] structLogDerivX2pX -- some [1,1]

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
     (CPolyG.cLogIsNewMonomial [structLogDerivX, structLogDerivX1] structLogDerivX2pX == false)
     && (match CPolyG.cLogRelationCoeffs [structLogDerivX, structLogDerivX1] structLogDerivX2pX with
         | some rs => structRelationCheck [structLogDerivX, structLogDerivX1] structLogDerivX2pX rs
                        && (rs == [1, 1])
         | none => false)
     -- the two generators are independent of each other.
     && (CPolyG.cLogIsNewMonomial [structLogDerivX1] structLogDerivX == true)
     && (CPolyG.cLogIsNewMonomial [structLogDerivX] structLogDerivX1 == true)) = true := by
  native_decide

#print axioms multiStructureTheorem_example

end DeepWiki.SymbolicIntegration
