import DeepWiki.SymbolicIntegration.ComputableSplitFactorFast
import DeepWiki.SymbolicIntegration.ComputableGenericBezout

/-! # Computable `CanonicalRepresentation` over the tower ℚ(x)[t] (Bronstein §3.5)
The abstract `canonicalRepresentation` (`CanonicalRepresentation`) splits `f ∈ k(t)` uniquely as
`f = fₚ + fₛ + fₙ` — polynomial + reduced (special-denominator) + simple (normal-denominator)
parts — via polynomial division, the denominator's splitting factorization, and an extended-Euclid
Bézout split. This file makes that **computable** over the differential tower ℚ(x)[t], reusing the
fraction-free splitting `cSplitFactorFast` (`ComputableSplitFactorFast`) for the denominator split.

* **`cextendedEuclideanSplit`** mirrors the abstract `extendedEuclideanSplit`: given a Bézout pair
  `(u, w)` with `u·dₙ + w·dₛ = 1`, it returns `(b, c) = ((u·r) mod dₛ, w·r + (u·r div dₛ)·dₙ)`
  solving `b·dₙ + c·dₛ = r`. The Bézout pair comes from `cgcdExtG dₙ dₛ` (gcd a nonzero constant `g`,
  since `dₙ, dₛ` are coprime), rescaled by `g⁻¹`.

* **`canonicalRepresentationFast Dt fuel (a, d)`** = `(fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))`:
  divide `a = q·d + r` (`cdivmodG`), split `d = dₛ·dₙ` (`cSplitFactorFast`), Bézout-split `r`.

* **Validation** (`canonicalRepFast_example`, `native_decide`): a small `f = t³/((t−1)(t−2))` over
  ℚ(x)(t) with `Dt = t − 1` (so `t = 1` special, `t = 2` normal); the three returned parts recombine
  to `f` — the identity `q + b/dₛ + c/dₙ = a/d`, checked by clearing denominators and `cisZeroG` of
  the difference over ℚ(x)[t].

**Bézout swell.** `cgcdExtG`'s cofactors over ℚ(x) can blow up (the fraction-free `cgcdFF` gives the
gcd but not cofactors). The small validation example here keeps it in budget; a fraction-free
*extended* PRS (cofactor-tracking) is the documented next optimization for larger inputs. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

/-! ### The computable canonical representation (over the tower ℚ(x)[t])

`canonicalRepresentationFast` is specialized to `QFunNZ` because its denominator split
`cSplitFactorFast` is the fraction-free splitting over ℚ(x)[t] (`cgcdFF`/`clearDenoms` are
`QFunNZ`-specific); the Bézout helpers `cbezoutOne`/`cextendedEuclideanSplit` above stay generic. -/

/-- **Computable `CanonicalRepresentation`** (Bronstein §3.5, p.103) over the tower ℚ(x)[t]:
`canonicalRepresentationFast Dt fuel (a, d) = (fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))` for `f = a/d`
(`d` monic). Steps: divide `a = q·d + r` (`cdivmodG`); split the denominator `d = dₛ·dₙ`
(`cSplitFactorFast`, fraction-free); Bézout-split `r` over the coprime `(dₙ, dₛ)`
(`cextendedEuclideanSplit` with `cbezoutOne`). The reduced part is `b/dₛ`, the simple part `c/dₙ`. -/
def canonicalRepresentationFast (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) :
    CPolyG QFunNZ × (CPolyG QFunNZ × CPolyG QFunNZ) × (CPolyG QFunNZ × CPolyG QFunNZ) :=
  let (q, r) := cdivmodG fuel a d
  let (dn, ds) := cSplitFactorFast Dt fuel d
  let (u, w) := cbezoutOne fuel dn ds
  let (b, c) := cextendedEuclideanSplit fuel dn ds r u w
  (q, (b, ds), (c, dn))

end CPolyG

/-! ### Validation — the parts recombine to `f` (`native_decide`)

`k = ℚ(x)` with `ℚ`-constant coefficients, monomial `t` with `Dt = t − 1` (so the root `t = 1` is
special, `t = 2` normal). Input `f = a/d` with `a = t³` and the monic `d = (t−1)(t−2) = t² − 3t + 2`.
`canonicalRepresentationFast` returns `(q, (b, dₛ), (c, dₙ))`; the load-bearing identity
`q + b/dₛ + c/dₙ = a/d` is checked by clearing denominators: combining the right over `dₛ·dₙ` gives
numerator `N = q·dₛ·dₙ + b·dₙ + c·dₛ`, so the identity is `N · d = a · (dₛ·dₙ)` — `cisZeroG` of the
difference over ℚ(x)[t]. (Scalar-robust: independent of the split's internal scalar ambiguity.) -/

open CPolyG QFunNZ

/-- Validation numerator `a = t³` over ℚ(x)[t] (ℚ-constant coefficients). -/
def canonicalRepFastExampleA : CPolyG QFunNZ :=
  [ofConstNZ 0, ofConstNZ 0, ofConstNZ 0, ofConstNZ 1]

/-- Validation denominator `d = (t−1)(t−2) = t² − 3t + 2` over ℚ(x)[t] (monic). -/
def canonicalRepFastExampleD : CPolyG QFunNZ :=
  [ofConstNZ 2, ofConstNZ (-3), ofConstNZ 1]

/-- Validation monomial derivative `Dt = t − 1` (root `t = 1` special, `t = 2` normal). -/
def canonicalRepFastExampleDt : CPolyG QFunNZ := [ofConstNZ (-1), ofConstNZ 1]

/-- **`canonicalRepresentationFast` recombines to `f`** (`native_decide`): for `f = t³/((t−1)(t−2))`
over ℚ(x)(t) with `Dt = t − 1`, the computed parts `(q, (b, dₛ), (c, dₙ))` satisfy the canonical
identity `q + b/dₛ + c/dₙ = a/d` — checked, after clearing denominators, as
`(q·dₛ·dₙ + b·dₙ + c·dₛ)·d = a·(dₛ·dₙ)` via `cisZeroG` of the difference over ℚ(x)[t]. This is the
deliverable: the computable `CanonicalRepresentation` engine executes over the tower and its output
genuinely reconstructs `f`. -/
theorem canonicalRepFast_example :
    (let res := CPolyG.canonicalRepresentationFast canonicalRepFastExampleDt 8
        canonicalRepFastExampleA canonicalRepFastExampleD
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      let dsdn := CPolyG.cmulG ds dn
      let num := CPolyG.caddG (CPolyG.caddG (CPolyG.cmulG q dsdn) (CPolyG.cmulG b dn))
        (CPolyG.cmulG c ds)
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cmulG num canonicalRepFastExampleD)
        (CPolyG.cmulG canonicalRepFastExampleA dsdn))) = true := by native_decide

end DeepWiki.SymbolicIntegration
