import DeepWiki.SymbolicIntegration.ComputableLogPartTower

/-! # Computable Risch differential equation solver over the tower ℚ(x)[t] (Bronstein Chapter 6)
The **Risch differential equation** (RDE) problem (Bronstein, *Symbolic Integration I*, Ch. 6) is:
given a differential field `K` of characteristic `0` and `f, g ∈ K`, decide whether

```
  Dy + f·y = g                                                                            (6.1)
```

has a solution `y ∈ K`, and find one if so. The book studies the **transcendental case**: `K = k(t)`
is a simple monomial extension of a differential subfield `k`, with `D = κ_D + Dt·d/dt` the monomial
derivation. We take `k = ℚ(x)`, `D = d/dx`, so the carrier is the tower `ℚ(x)[t]` already built by the
integrator engine (`CPolyG QFunNZ`, `cmonomialDeriv Dt`).

Bronstein's RDE pipeline (Ch. 6, confirmed section numbers from the 2005 edition, p.181–215):

1. **§6.1 `WeakNormalizer`** + the **normal part of the denominator** (`RdeNormalDenominator`, §6.2's
   eq. 6.2 / Corollary 6.1.1). `WeakNormalizer(f, D)` returns `q ∈ k[t]` such that `f − Dq/q` is
   *weakly normalized*. `RdeNormalDenominator(f, g, D)` then either reports **no solution** or returns a
   quadruplet `(a, b, c, h)` with `a, h ∈ k[t]`, `b, c ∈ k⟨t⟩` such that every solution `y ∈ k(t)` of
   `Dy + f·y = g` has `q = y·h ∈ k⟨t⟩` solving `a·Dq + b·q = c` — reducing (6.1) to the simple part.
2. **§6.2 `RdeSpecialDenominator`** — the *special* part of the denominator, reducing the simple-part
   equation `a·Dq + b·q = c` (eq. 6.6, `a ∈ k[t]` with no special factor) to a **polynomial** equation
   over `k[t]`. The §6.2 reduction (eq. 6.7) replaces `q` by `h·pⁿ` and clears the special factor `p`;
   the lower bound `n` on `ν_p(q)` is computed case-by-case for the *primitive* (`Dt ∈ k`),
   *hyperexponential* (`Dt/t ∈ k`), and *nonlinear* monomials.
3. **§6.3 `RdeBoundDegree`** — an explicit upper bound on `deg_t(q)` for any polynomial solution `q`,
   again split by monomial type (primitive, hyperexponential, nonlinear, the `t = tan` case).
4. **§6.4 `SPDE`** (the *Sub-Problem of the Differential Equation*) — Rothstein's recursive reduction
   of the bounded-degree polynomial equation `a·Dq + b·q = c` to a smaller one, peeling `gcd(a, b)`.
5. **§6.5–6.6 `PolyRischDE`** — the non-cancellation and cancellation cases that finally solve the
   degree-bounded polynomial equation in `k[t]`.

## What this file delivers (the first two reachable stages, computable + `native_decide`-validated)

* **`cWeakNormalizer Dt fuel fnum fden`** (§6.1) — the `WeakNormalizer` algorithm box (book p.183) over
  the tower: split the denominator of `f = fnum/fden` into its normal part `dₙ`, form
  `d₁ = (dₙ/g)/gcd(dₙ/g, g)` with `g = gcd(dₙ, dₙ')`, solve `ExtendedEuclidean(fden/d₁, d₁, fnum)` for
  the residue-numerator `a`, build the residue resultant `r = res_t(a − z·Dd₁, d₁)`, and return
  `∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}` over the **positive integer roots** `nᵢ` of `r`. The positive integer
  roots are found by a bounded evaluation test (`cevalConst r n = 0`). For an already-weakly-normalized
  `f` (the post-Hermite RDE input), `r` has no positive integer roots and the result is `q = 1`.

* **`cRdeNormalDenominator Dt fuel fnum fden gnum gden`** (§6.2 / Corollary 6.1.1) — the
  `RdeNormalDenominator` algorithm box (book p.185): from the normal parts `dₙ, eₙ` of the denominators
  of `f, g`, compute `h = gcd(eₙ, eₙ')/gcd(p, p')` with `p = gcd(dₙ, eₙ)`, and return the reduction
  quadruplet `(a, b, c, h) = (dₙh, dₙhf − dₙ(Dh), dₙh²g, h)` (or **no solution** when `eₙ ∤ dₙh²`).

## Validation (`native_decide`)

Bronstein's **Example 6.1.2** (book p.186): `k = ℚ(x)`, `D = d/dx`, `t = tan(x)` (`Dt = 1 + t²`), the
equation `Dy + (t²+1)y = 1/t²`. So `f = t²+1` (denominator `1`), `g = 1/t²`. The book runs
`RdeNormalDenominator` and gets `dₙ = 1`, `eₙ = t²`, `p = 1`, `h = t`, `dₙh² = t²` divisible by `eₙ`,
and the quadruplet `(a, b, c, h) = (t, (t−1)(t²+1), 1, t)`, i.e. any solution is `y = q/t` with `q`
solving the reduced equation `t·Dq + (t−1)(t²+1)·q = 1` (book eq. 6.5). `native_decide` pins all four
output components against these book values (via `cisZeroG` of the cleared difference — `QFunNZ` has no
`DecidableEq`). `cWeakNormalizer` is checked to return `q = 1` here (`f` is already weakly normalized).

## What is NOT here (the remaining stages, honestly deferred)

This is one major algorithm; the deliverable is the **first two stages computing over the tower** plus
validation, not abstract correctness (no `Dy + fy = g ↔ …` theorem is proved). The remaining stages —
§6.2 `RdeSpecialDenominator` (the `pⁿ` special-factor clearing, case-split by monomial type),
§6.3 `RdeBoundDegree`, §6.4 `SPDE`, §6.5–6.6 `PolyRischDE` — require the parametric-logarithmic-
derivative subroutine (§5.12 / Ch. 7) for the hyperexponential degree bound and the recursive
polynomial solver; they are the natural continuation. No `sorry`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

namespace CPolyG

/-! ### Polynomial evaluation at a rational constant (positive-integer-root test for `WeakNormalizer`)

`cevalConst p c = p(c) ∈ QFunNZ` for a constant `c ∈ ℚ` lifted to `ℚ(x)`, by Horner. Used to test
candidate positive integers `n` for being roots of the residue resultant `r ∈ ℚ(x)[z]`
(`cisZero (cevalConst r n).num`), the §6.1 step "`(n₁,…,n_s) ← positive integer roots of r`". -/

/-- **Evaluate a `CPolyG QFunNZ` at a constant `c ∈ ℚ`** (lifted to `ℚ(x)`), by Horner from the top
coefficient down: `cevalConst [a₀,…,aₙ] c = a₀ + c(a₁ + c(… + c·aₙ))`. The result is a `QFunNZ`. -/
def cevalConst (p : CPolyG QFunNZ) (c : ℚ) : QFunNZ :=
  let cv : QFunNZ := ofConstNZ c
  ((p : List QFunNZ).foldr (fun a acc => CField.add a (CField.mul cv acc)) CField.zero)

/-- **`r` vanishes at the rational constant `c`** `cisRootConst r c`: `true` iff `cevalConst r c` is the
zero element of `QFunNZ` (its numerator polynomial is the zero list). Decides whether `c` is a root of
`r ∈ ℚ(x)[z]` over the tower. -/
def cisRootConst (r : CPolyG QFunNZ) (c : ℚ) : Bool :=
  CField.isZero (cevalConst r c)

/-- **Positive integer roots of `r` up to a bound** `cPosIntRoots r bound = [n ∈ {1,…,bound} : r(n) = 0]`
(the §6.1 step). The residue resultant's positive integer roots are the multiplicities `nᵢ` entering the
`WeakNormalizer` product; for an already-weakly-normalized `f` this list is empty. -/
def cPosIntRoots (r : CPolyG QFunNZ) (bound : ℕ) : List ℕ :=
  (List.range bound).filterMap (fun k =>
    let n : ℕ := k + 1
    if cisRootConst r ((n : ℚ)) then some n else none)

/-! ### `cWeakNormalizer` (Bronstein §6.1, the `WeakNormalizer(f, D)` algorithm box, book p.183)

`f ∈ k(t)` arrives as a numerator/denominator pair `(fnum, fden)` of `t`-polynomials over `ℚ(x)`. The
box returns `q ∈ k[t]` with `f − Dq/q` weakly normalized. -/

/-- **Computable weak normalizer** `cWeakNormalizer Dt fuel fnum fden = q ∈ ℚ(x)[t]` (Bronstein §6.1,
book p.183) with `f − Dq/q` weakly normalized w.r.t. `t`, for `f = fnum/fden`:

1. `(dₙ, dₛ) ← SplitFactor(fden, D)` — the normal part `dₙ` of the denominator.
2. `g ← gcd(dₙ, dₙ')` (`'` = `d/dt`), `d* ← dₙ/g`, `d₁ ← d*/gcd(d*, g)`.
3. `(a, _) ← ExtendedEuclidean(fden/d₁, d₁, fnum)`: `a·(fden/d₁) + b·d₁ = fnum`.
4. `r ← res_t(a − z·Dd₁, d₁)` (the residue resultant, `Dd₁ = cmonomialDeriv Dt d₁`).
5. `(n₁,…,n_s) ← positive integer roots of r` (bounded by `boundRoots`).
6. `return ∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}`.

When `f` is already weakly normalized (`r` has no positive integer root) the product is empty and the
result is `q = 1`. `boundRoots` caps the integer-root search. -/
def cWeakNormalizer (Dt : CPolyG QFunNZ) (fuel : ℕ) (fnum fden : CPolyG QFunNZ)
    (boundRoots : ℕ := 16) : CPolyG QFunNZ :=
  let dn := (cSplitFactorFast Dt fuel fden).1
  let g := cgcdFF fuel dn (cderivG dn)
  let dstar := cdivFF fuel dn g
  let d1 := cdivFF fuel dstar (cgcdFF fuel dstar g)
  let fdenOverD1 := cdivFF fuel fden d1
  let a := (cdiophantineG fuel fdenOverD1 d1 fnum).1
  let Dd1 := cmonomialDeriv Dt d1
  -- residue resultant `r(z) = res_t(a − z·Dd₁, d₁)`; reuse the §5.6 evaluation/interpolation template
  let r := cResidueResultantTower Dt fuel a d1
  let roots := cPosIntRoots r boundRoots
  roots.foldl (fun (acc : CPolyG QFunNZ) (n : ℕ) =>
    let gi := cgcdFF fuel (csubG a (cscaleG (ofConstNZ ((n : ℚ))) Dd1)) d1
    cmulG acc (cpowG gi n)) [CField.one]

/-! ### `cRdeNormalDenominator` (Bronstein §6.2 / Corollary 6.1.1, the algorithm box, book p.185)

`f, g ∈ k(t)` arrive as numerator/denominator pairs. The box returns either **no solution** or the
quadruplet `(a, b, c, h)` reducing `Dy + fy = g` to `a·Dq + b·q = c` with `q = y·h`. Encoded as
`Option (a, b, c, h)` (`none` = "no solution"). -/

/-- **Computable normal-denominator reduction** `cRdeNormalDenominator Dt fuel fnum fden gnum gden`
(Bronstein §6.2, book p.185), for a **weakly normalized** `f = fnum/fden` and `g = gnum/gden`. Returns
`none` ("no solution") or `some (a, b, c, h)` with `a, h ∈ ℚ(x)[t]`, `b, c ∈ ℚ(x)⟨t⟩` such that every
solution `y ∈ k(t)` of `Dy + fy = g` has `q = y·h ∈ k⟨t⟩` solving `a·Dq + b·q = c`:

1. `(dₙ, dₛ) ← SplitFactor(fden, D)`, `(eₙ, eₛ) ← SplitFactor(gden, D)`.
2. `p ← gcd(dₙ, eₙ)`, `h ← gcd(eₙ, eₙ') / gcd(p, p')` (`'` = `d/dt`).
3. **if** `eₙ ∤ dₙh²` **then** "no solution".
4. `return (dₙh, dₙhf − dₙ·Dh, dₙh²g, h)`.

Here `f` and `g` are cleared into the `t`-polynomial pieces: `a = dₙh`, and the (generally rational in
`t`) `b, c` are returned as **numerator polynomials over the common denominators** `fden`, `gden` —
specifically `b = dₙh·fnum − dₙ·Dh·fden` (numerator over `fden`) and `c = dₙh²·gnum` (numerator over
`gden`). The validation example has `fden = gden = 1`'s normal parts so the pieces are genuine
polynomials and match the book verbatim. -/
def cRdeNormalDenominator (Dt : CPolyG QFunNZ) (fuel : ℕ) (fnum fden gnum gden : CPolyG QFunNZ) :
    Option (CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ) :=
  let dn := (cSplitFactorFast Dt fuel fden).1
  let en := (cSplitFactorFast Dt fuel gden).1
  let p := cgcdFF fuel dn en
  let h := cdivFF fuel (cgcdFF fuel en (cderivG en)) (cgcdFF fuel p (cderivG p))
  let dnh2 := cmulG (cmulG dn h) h
  if cdvdG fuel en dnh2 then
    let a := cmulG dn h
    let Dh := cmonomialDeriv Dt h
    -- `b = dₙh·f − dₙ·Dh = (dₙh·fnum − dₙ·Dh·fden)/fden` (the numerator is divisible by `fden`).
    let b := cdivFF fuel (csubG (cmulG a fnum) (cmulG (cmulG dn Dh) fden)) fden
    -- `c = dₙh²·g = dₙh²·gnum/gden` (divisible by `gden` exactly when `eₙ ∣ dₙh²`, the test above).
    let c := cdivFF fuel (cmulG dnh2 gnum) gden
    some (a, b, c, h)
  else none

end CPolyG

/-! ### Validation — Bronstein Example 6.1.2 (book p.186): `t = tan(x)`, `Dt = 1 + t²`, `Dy+(t²+1)y=1/t²`

`k = ℚ(x)`, `D = d/dx`, the monomial `t = tan(x)` with `Dt = 1 + t²`. The equation
`Dy + (t²+1)y = 1/t²` arises from `∫ e^{tan(x)}/tan(x)² dx`. So `f = t²+1` (numerator `t²+1`,
denominator `1`) and `g = 1/t²` (numerator `1`, denominator `t²`). Bronstein's run:
`(dₙ, dₛ) = (1, t²+1)`, `(eₙ, eₛ) = (t², 1)`, `p = gcd(1, t²) = 1`, `h = gcd(t², 2t)/gcd(1,1) = t`,
`dₙh² = t²` divisible by `eₙ = t²`, and the reduction quadruplet is
`(a, b, c, h) = (t, (t−1)(t²+1), 1, t)` — the reduced equation `t·Dq + (t−1)(t²+1)q = 1` (eq. 6.5). -/

open CPolyG QFunNZ

/-- Example 6.1.2's monomial derivative `Dt = 1 + t²` (`t = tan(x)`; low→high in `t`,
ℚ-constant coefficients). -/
def rischDExampleDt : CPolyG QFunNZ := [ofConstNZ 1, ofConstNZ 0, ofConstNZ 1]

/-- Example 6.1.2's `f = t²+1`: numerator `t²+1`, denominator `1`. -/
def rischDExampleFnum : CPolyG QFunNZ := [ofConstNZ 1, ofConstNZ 0, ofConstNZ 1]
/-- Example 6.1.2's `f`-denominator `1`. -/
def rischDExampleFden : CPolyG QFunNZ := [ofConstNZ 1]

/-- Example 6.1.2's `g = 1/t²`: numerator `1`. -/
def rischDExampleGnum : CPolyG QFunNZ := [ofConstNZ 1]
/-- Example 6.1.2's `g`-denominator `t²` (low→high in `t`). -/
def rischDExampleGden : CPolyG QFunNZ := [ofConstNZ 0, ofConstNZ 0, ofConstNZ 1]

/-- Example 6.1.2's expected reduction component `a = t` (low→high in `t`). -/
def rischDExampleA : CPolyG QFunNZ := [ofConstNZ 0, ofConstNZ 1]
/-- Example 6.1.2's expected reduction component `b = (t−1)(t²+1) = t³ − t² + t − 1` (low→high in `t`). -/
def rischDExampleB : CPolyG QFunNZ := [ofConstNZ (-1), ofConstNZ 1, ofConstNZ (-1), ofConstNZ 1]
/-- Example 6.1.2's expected reduction component `c = 1`. -/
def rischDExampleC : CPolyG QFunNZ := [ofConstNZ 1]
/-- Example 6.1.2's expected reduction component `h = t` (low→high in `t`). -/
def rischDExampleH : CPolyG QFunNZ := [ofConstNZ 0, ofConstNZ 1]

-- **Sanity prints** (book p.186): the `RdeNormalDenominator` quadruplet `(a,b,c,h) = (t, t³−t²+t−1, 1, t)`
-- and the `WeakNormalizer` value `q = 1` (`f = t²+1` is already weakly normalized).
#eval (CPolyG.cRdeNormalDenominator rischDExampleDt 30 rischDExampleFnum rischDExampleFden
  rischDExampleGnum rischDExampleGden).map (fun (a, b, c, h) =>
    (((a : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
     ((b : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
     ((c : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)),
     ((h : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1))))
#eval (CPolyG.cWeakNormalizer rischDExampleDt 30 rischDExampleFnum rischDExampleFden : List QFunNZ).map
    (fun z : QFunNZ => Compute.qnorm 30 z.1)

/-- **Example 6.1.2 — the first two RDE stages execute over the tower** (`native_decide`, Bronstein §6.1
+ §6.2, book p.183/185/186). For `Dy + (t²+1)y = 1/t²` over ℚ(x)(t), `t = tan(x)`, `Dt = 1+t²`:

1. **Weak normalizer (§6.1).** `f = t²+1` is already weakly normalized — its denominator is `1`, so the
   residue resultant has no positive integer roots and `cWeakNormalizer` returns `q = 1`.
2. **Normal denominator (§6.2).** `cRdeNormalDenominator` returns `some (a, b, c, h)` with
   `(a, b, c, h) = (t, (t−1)(t²+1), 1, t)` — checked componentwise by `cisZeroG` of each cleared
   difference. So every solution `y` is `y = q/t` with `q` solving `t·Dq + (t−1)(t²+1)q = 1` (eq. 6.5).

This is the deliverable: the §6.1 `WeakNormalizer` and §6.2 `RdeNormalDenominator` stages of the Risch
differential equation algorithm *compute* over the monomial tower ℚ(x)[t] and return the book's values.
Abstract correctness (the `Dy + fy = g ↔ a·Dq + b·q = c` equivalence) is not proved here; the remaining
pipeline stages (special denominator, degree bound, SPDE, PolyRischDE) are documented in the module
docstring as the continuation. -/
theorem rischDE_normalDenominator_example :
    cisZeroG (csubG (cWeakNormalizer rischDExampleDt 30 rischDExampleFnum rischDExampleFden)
        [CField.one]) = true
    ∧ (match cRdeNormalDenominator rischDExampleDt 30 rischDExampleFnum rischDExampleFden
          rischDExampleGnum rischDExampleGden with
        | some (a, b, c, h) =>
            cisZeroG (csubG a rischDExampleA)
              && cisZeroG (csubG b rischDExampleB)
              && cisZeroG (csubG c rischDExampleC)
              && cisZeroG (csubG h rischDExampleH)
        | none => false) = true := by native_decide

#print axioms rischDE_normalDenominator_example

end DeepWiki.SymbolicIntegration
