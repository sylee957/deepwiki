import DeepWiki.SymbolicIntegration.ComputableMonomialDeriv
import DeepWiki.SymbolicIntegration.SubresultantCompute

/-! # Fraction-free `splitFactor` over the tower ℚ(x)[t] — the payoff of the subresultant PRS
The naive `cSplitFactor` (`ComputableMonomialDeriv`) runs Bronstein's `SplitFactor` with the Euclidean
gcd `cgcdExtG` over the field ℚ(x): every Euclidean step divides by the leading ℚ(x)-coefficient, so the
rational-function coefficients swell super-exponentially and Bronstein's degree-5 **Example 3.5.1** does
not finish in budget. This file replaces the gcd kernel with the **fraction-free** primitive
polynomial-remainder sequence of `SubresultantCompute` (`bpsremainder`/`bprimitivePartX`): the Euclidean
steps happen in ℚ[x] (pseudo-division, no field division), so the coefficients stay bounded.

* **Bridge `CPolyG QFunNZ ↔ BPoly`** (ℚ(x)[t] ↔ ℚ[x][t]). `clearDenoms` multiplies a `t`-polynomial
  through by the product of its ℚ(x)-coefficient denominators, giving a `BPoly` (each `t`-coefficient a
  ℚ[x] = `CPoly`); `liftBPolyToQFunNZ` re-reads a `BPoly` coefficient `c` as the `QFunNZ` `c/1`.

* **`cgcdFF`** clears denominators of both inputs, orders them by `t`-degree, runs the primitive PRS
  `primPRSgcd` (last nonzero primitive remainder = gcd in `t` up to ℚ[x]-content), lifts the result back
  and monic-normalizes it over ℚ(x)[t]. **`cSplitFactorFast`** is Bronstein's loop with `cgcdFF` for its
  two gcds and exact `cdivG` for the ratio.

* **The payoff:** `cSplitFactorFast` of Example 3.5.1's degree-5 `p` returns the book's normal part
  `pₙ` (degree 3) and special part `pₛ` (degree 2), pinned by `native_decide`. -/

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ### The bridge `CPolyG QFunNZ ↔ BPoly` -/

namespace CPolyG

/-- The numerator `CPoly` (`= ℚ[x]`) of a `QFunNZ` coefficient. -/
def qnumCoeff (c : QFunNZ) : CPoly := c.1.1

/-- The denominator `CPoly` (`= ℚ[x]`) of a `QFunNZ` coefficient. -/
def qdenCoeff (c : QFunNZ) : CPoly := c.1.2

/-- **Clear denominators** `clearDenoms p ∈ BPoly` (`= ℚ[x][t]`): multiply the `t`-polynomial `p` through
by the product of its ℚ(x)-coefficient denominators, so coefficient `i` becomes `numᵢ · ∏_{j≠i} denⱼ ∈
ℚ[x]`. Carries `p` from ℚ(x)[t] to ℚ[x][t] up to the (cleared) common-denominator unit. -/
def clearDenoms (p : CPolyG QFunNZ) : Compute.BPoly :=
  let cs : List QFunNZ := p
  let dens : List CPoly := cs.map qdenCoeff
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => Compute.cmul acc d) [1]
    Compute.cmul (qnumCoeff ci) prodOthers)

/-- **Lift back** `liftBPolyToQFunNZ p ∈ CPolyG QFunNZ`: read each `CPoly` (`= ℚ[x]`) coefficient `c` of a
`BPoly` as the `QFunNZ` rational function `c/1` (numerator `c`, denominator `[1]`). -/
def liftBPolyToQFunNZ (p : Compute.BPoly) : CPolyG QFunNZ :=
  p.map (fun c => (⟨(c, [1]), by
    show Compute.toPoly [1] ≠ 0
    simp [Compute.toPoly]⟩ : QFunNZ))

/-! ### The fraction-free gcd kernel — the primitive PRS over ℚ[x] -/

/-- **Primitive polynomial-remainder sequence** `primPRSgcd fuel P Q ∈ BPoly`: the gcd of `P, Q` in `t`
(over the coefficient ring ℚ[x]), up to a ℚ[x]-content factor. Each step takes the **primitive part** of
the **pseudo-remainder** (`bprimitivePartX (bpsremainder P Q)`), keeping every coefficient in ℚ[x] (no
field division, so no ℚ(x) swell); the last nonzero primitive remainder is the gcd. Requires
`bdeg P ≥ bdeg Q`; fuel-bounded (one step per `t`-degree drop). -/
def primPRSgcd : ℕ → Compute.BPoly → Compute.BPoly → Compute.BPoly
  | 0, P, _ => Compute.bprimitivePartX 30 P
  | fuel + 1, P, Q =>
    let P := Compute.bnorm P
    let Q := Compute.bnorm Q
    if Compute.bisZero Q then Compute.bprimitivePartX 30 P
    else
      let r := Compute.bprimitivePartX 30 (Compute.bpsremainder 60 P Q)
      primPRSgcd fuel Q r

/-- **Fraction-free monic gcd over ℚ(x)[t]** `cgcdFF fuel p q`: clear denominators of both inputs into
ℚ[x][t], order them by `t`-degree (the PRS needs the larger first), run the primitive PRS `primPRSgcd`
(gcd up to ℚ[x]-content), lift back to ℚ(x)[t], and **monic-normalize** (`cmonicG`). The Euclidean work
is fraction-free in ℚ[x], avoiding the ℚ(x)-coefficient swell of the naive `cgcdExtG`. -/
def cgcdFF (fuel : ℕ) (p q : CPolyG QFunNZ) : CPolyG QFunNZ :=
  let P := clearDenoms p
  let Q := clearDenoms q
  let (P, Q) := if Compute.bdeg P < Compute.bdeg Q then (Q, P) else (P, Q)
  cmonicG (liftBPolyToQFunNZ (primPRSgcd fuel P Q))

/-- **Exact division over ℚ(x)[t]** `cdivFF fuel p q = p / q`: the quotient via the generic Euclidean
`cdivG` (exact at the `splitFactor` call sites, where `q` divides `p`). -/
def cdivFF (fuel : ℕ) (p q : CPolyG QFunNZ) : CPolyG QFunNZ := cdivG fuel p q

/-! ### Fraction-free `splitFactor` -/

/-- **Fraction-free splitting-factorization loop** (Bronstein §3.5): `cSplitFactorFast Dt fuel p =
(pₙ, pₛ)`, the same recursion as `cSplitFactor` but with the fraction-free `cgcdFF` for the two gcds
`gcd(p, Dp)` and `gcd(p, dp/dt)`. One step extracts `S = gcd(p, Dp)/gcd(p, dp/dt)`; constant `S` ⇒ `p`
is normal, else recurse on `p/S` and accumulate `S` into the special part. Fuel-bounded; reduces in
native code over ℚ(x)[t] (`native_decide`) where the naive kernel did not finish. -/
def cSplitFactorFast (Dt : CPolyG QFunNZ) : ℕ → CPolyG QFunNZ → CPolyG QFunNZ × CPolyG QFunNZ
  | 0, p => (p, [CField.one])
  | fuel + 1, p =>
    let S := cdivFF (fuel + 1) (cgcdFF (fuel + 1) p (cmonomialDeriv Dt p))
      (cgcdFF (fuel + 1) p (cderivG p))
    if cdegG S = 0 then (p, [CField.one])
    else
      let (qn, qs) := cSplitFactorFast Dt fuel (cdivFF (fuel + 1) p S)
      (qn, cmulG S qs)

end CPolyG

/-! ### Sanity: the `(t−1)(t−2)` example computes with the fraction-free kernel

Re-running the `ComputableMonomialDeriv` sanity example through `cSplitFactorFast`: under `Dt = t − 1`
the root `t = 1` is special and `t = 2` normal, so the normal part is `~ (t − 2)` and the special part
`~ (t − 1)` — the same answer the naive `cSplitFactor` gives, now via the fraction-free gcd. -/

open CPolyG QFunNZ

/-- The fraction-free split of `(t−1)(t−2)` over ℚ(x)[t] has a **degree-1 normal part**. -/
example :
    CPolyG.cdegG (CPolyG.cSplitFactorFast cSplitFactorExampleDt 8 cSplitFactorExampleP).1 = 1 := by
  native_decide

/-- The fraction-free split of `(t−1)(t−2)` has a **degree-1 special part**. -/
example :
    CPolyG.cdegG (CPolyG.cSplitFactorFast cSplitFactorExampleDt 8 cSplitFactorExampleP).2 = 1 := by
  native_decide

/-- The monic-normalized special part of `(t−1)(t−2)` is `t − 1` (the special root). -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (CPolyG.cSplitFactorFast cSplitFactorExampleDt 8 cSplitFactorExampleP).2)
      [ofConstNZ (-1), ofConstNZ 1]) = true := by native_decide

/-- The monic-normalized normal part of `(t−1)(t−2)` is `t − 2` (the normal root). -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (CPolyG.cSplitFactorFast cSplitFactorExampleDt 8 cSplitFactorExampleP).1)
      [ofConstNZ (-2), ofConstNZ 1]) = true := by native_decide

/-! ### The payoff — Bronstein's Example 3.5.1 computes (`native_decide`)

`k = ℚ(x)`, `D = d/dx`, the monomial `t` with `Dt = −t² − (3/(2x))t + 1/(2x)`, and the degree-5
`p = 4x⁴t⁵ − 4x³(x+1)t⁴ + x²(2x−3)t³ + x(2x²+7x+2)t² − (4x²+4x−1)t + 2x−1`. Bronstein's worked answer
(book p.101) is the normal part `pₙ = 4x⁴t³ − 4x³(x+2)t² + 4x²(2x+1)t − 4x²` (degree 3) and the special
part `pₛ = t² + (1/x)t − (2x−1)/(4x²)` (degree 2). The fraction-free `cSplitFactorFast` returns exactly
these (monic-normalized), where the naive ℚ(x)-Euclidean kernel did not finish in budget. -/

namespace QFunNZ

/-- Build a `QFunNZ` coefficient from a numerator/denominator `CPoly`, denominator nonzero by `decide`. -/
def mkCoeff (num den : Compute.CPoly) (h : Compute.cisZero den = false := by decide) : QFunNZ :=
  ofNumDen num den h

end QFunNZ

open QFunNZ in
/-- Example 3.5.1's `Dt = −t² − (3/(2x))t + 1/(2x)` as a `CPolyG QFunNZ` (low→high in `t`). -/
def splitFastExample351Dt : CPolyG QFunNZ :=
  [mkCoeff [1] [0, 2], mkCoeff [-3] [0, 2], mkCoeff [-1] [1]]

open QFunNZ in
/-- Example 3.5.1's degree-5 `p = 4x⁴t⁵ − 4x³(x+1)t⁴ + x²(2x−3)t³ + x(2x²+7x+2)t² − (4x²+4x−1)t + 2x−1`
as a `CPolyG QFunNZ` (low→high in `t`; all coefficients are ℚ[x] polynomials, denominator `1`). -/
def splitFastExample351P : CPolyG QFunNZ :=
  [mkCoeff [-1, 2] [1],
   mkCoeff [1, -4, -4] [1],
   mkCoeff [0, 2, 7, 2] [1],
   mkCoeff [0, 0, -3, 2] [1],
   mkCoeff [0, 0, 0, -4, -4] [1],
   mkCoeff [0, 0, 0, 0, 4] [1]]

open QFunNZ in
/-- Example 3.5.1's expected normal part `pₙ = 4x⁴t³ − 4x³(x+2)t² + 4x²(2x+1)t − 4x²` (book p.101). -/
def splitFastExample351Pn : CPolyG QFunNZ :=
  [mkCoeff [0, 0, -4] [1],
   mkCoeff [0, 0, 4, 8] [1],
   mkCoeff [0, 0, 0, -8, -4] [1],
   mkCoeff [0, 0, 0, 0, 4] [1]]

open QFunNZ in
/-- Example 3.5.1's expected special part `pₛ = t² + (1/x)t − (2x−1)/(4x²)` (book p.101). -/
def splitFastExample351Ps : CPolyG QFunNZ :=
  [mkCoeff [1, -2] [0, 0, 4],
   mkCoeff [1] [0, 1],
   mkCoeff [1] [1]]

/-- **Example 3.5.1 normal and special degrees** — the fraction-free split returns
`(deg pₙ, deg pₛ) = (3, 2)`, matching Bronstein's worked answer. -/
example :
    (CPolyG.cdegG (CPolyG.cSplitFactorFast splitFastExample351Dt 8 splitFastExample351P).1,
     CPolyG.cdegG (CPolyG.cSplitFactorFast splitFastExample351Dt 8 splitFastExample351P).2) = (3, 2) := by
  native_decide

/-- **Example 3.5.1 normal part is the book's `pₙ`** — the monic-normalized normal part of the
fraction-free split equals `4x⁴t³ − 4x³(x+2)t² + 4x²(2x+1)t − 4x²` (monic), checked by `cisZeroG` of the
difference over ℚ(x)[t]. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (CPolyG.cSplitFactorFast splitFastExample351Dt 8 splitFastExample351P).1)
      (CPolyG.cmonicG splitFastExample351Pn)) = true := by native_decide

/-- **Example 3.5.1 special part is the book's `pₛ`** — the monic-normalized special part of the
fraction-free split equals `t² + (1/x)t − (2x−1)/(4x²)` (monic), checked by `cisZeroG` of the difference
over ℚ(x)[t]. This is the deliverable: the fraction-free kernel makes Bronstein's degree-5 Example 3.5.1
**compute** the book's `pₙ`/`pₛ` where the naive ℚ(x)-Euclidean kernel did not finish. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (CPolyG.cSplitFactorFast splitFastExample351Dt 8 splitFastExample351P).2)
      (CPolyG.cmonicG splitFastExample351Ps)) = true := by native_decide

/-- **Example 3.5.1** (Bronstein §3.5, p.101) COMPUTES: the fraction-free `cSplitFactorFast` on the
degree-5 `p` over ℚ(x)[t] (monomial `t` with `Dt = −t²−(3/2x)t+1/(2x)`) returns Bronstein's normal part
`pₙ = 4x⁴t³−4x³(x+2)t²+4x²(2x+1)t−4x²` (degree 3) and special part `pₛ = t²+(1/x)t−(2x−1)/(4x²)`
(degree 2), monic-normalized — by `native_decide`, where the naive ℚ(x)-Euclidean kernel did not
finish in budget. -/
theorem splitFactorFast_ex351 :
    (CPolyG.cdegG (CPolyG.cSplitFactorFast splitFastExample351Dt 8 splitFastExample351P).1,
       CPolyG.cdegG (CPolyG.cSplitFactorFast splitFastExample351Dt 8 splitFastExample351P).2) = (3, 2)
    ∧ CPolyG.cisZeroG (CPolyG.csubG
        (CPolyG.cmonicG (CPolyG.cSplitFactorFast splitFastExample351Dt 8 splitFastExample351P).1)
        (CPolyG.cmonicG splitFastExample351Pn)) = true
    ∧ CPolyG.cisZeroG (CPolyG.csubG
        (CPolyG.cmonicG (CPolyG.cSplitFactorFast splitFastExample351Dt 8 splitFastExample351P).2)
        (CPolyG.cmonicG splitFastExample351Ps)) = true := by native_decide

end DeepWiki.SymbolicIntegration
