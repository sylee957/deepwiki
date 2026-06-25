import DeepWiki.SymbolicIntegration.ComputableTowerReduce
import DeepWiki.SymbolicIntegration.ComputableSplitFactorFast

/-! # Coefficient-swell benchmark: fraction-free `cgcdFF` vs naive Euclidean `cgcdExtG`
The tower integrator can run its `t`-polynomial gcd two ways at `α = QFunNZ = ℚ(x)`: the **fraction-free**
`cgcdFF` (clear denominators into `ℚ[x][t]`, primitive PRS — `ComputableSplitFactorFast`) or the generic
**Euclidean** `cgcdExtG` over the fraction field ℚ(x) (`GenericPolyEngine`). Euclidean division divides by
the leading ℚ(x)-coefficient each step, so the rational-function coefficients **swell**
super-exponentially; the fraction-free kernel keeps them bounded.

This file pins that swell with a concrete witness. With the gcd held **fixed at degree 2** (the
`commonFactor` `(t+x)(t−1/x)`) and only the *cofactor* `t`-degree scaling, the raw stored
coefficient-size of the gcd RESULT is:

| total `t`-degree of `p` | `cgcdFF` | `cgcdExtG` | `cgcdNormGcd` (Euclid + per-step `qnorm`) |
| --- | --- | --- | --- |
| 3 | 36 | 147 | 28 |
| 4 | 36 | 258 261 011 921 | 28 |

So `cgcdExtG`'s stored coefficient size jumps from 147 to ~2.6·10¹¹ for a single extra degree (it reaches
a 147-digit value by degree 5), while `cgcdFF` and the reducing variant stay flat. (`native_decide`
build-time confirms the runtime cost: at total degree 5, `cgcdFF` ≈ baseline but `cgcdExtG` is ~90 s.)

* **`cgcdNormGcd`** — a Euclidean gcd that applies `Compute.qnorm` (gcd-cancel to lowest terms, the
  concrete `QFunNZG.qreduceG` at this level) to every remainder coefficient each step. It produces the
  *same* monic gcd as `cgcdFF` (`benchNormGcd_agrees_cgcdFF`) and **removes the swell from the result**
  (`benchNormGcd_size_flat`). It does NOT, however, bound the swell as well as `cgcdFF` deeper in the
  tower: `qnorm` cancels only *common* factors, while Euclidean division still grows the coprime
  coefficient *degree* each step — so its per-step `qnorm` (an inner ℚ[x] gcd) cost compounds and it
  overtakes `cgcdFF` at higher degree. The genuine fix is the fraction-free PRS, kept QFunNZ-specific in
  `cgcdFF`; this file documents *why*. -/

namespace DeepWiki.SymbolicIntegration

open Compute QFunNZ CPolyG

namespace Bench

/-! ### Benchmark inputs — gcd fixed at degree 2, cofactor degree scaling -/

/-- Build a `QFunNZ` ℚ(x)-coefficient `num/den` (coefficient lists low→high in `x`); falls back to the
constant `0` if the denominator is the zero polynomial. The hand-constructor for benchmark coefficients
with genuine denominators. -/
def qc (num den : Compute.CPoly) : QFunNZ :=
  if h : Compute.cisZero den = false then ofNumDen num den h else ofConstNZ 0

/-- A linear `t`-polynomial `a0 + a1·t` as a `CPolyG QFunNZ` (low→high in `t`). -/
def lin (a0 a1 : QFunNZ) : CPolyG QFunNZ := [a0, a1]

/-- The ℚ(x) coefficient `x`. -/
def cX : QFunNZ := qc [0, 1] [1]
/-- The ℚ(x) coefficient `1/x` (a genuine denominator, so Euclidean division swells through it). -/
def cInvX : QFunNZ := qc [1] [0, 1]
/-- The ℚ(x) coefficient `x + 1`. -/
def cXp1 : QFunNZ := qc [1, 1] [1]
/-- The ℚ(x) coefficient `1/(x + 1)`. -/
def cInvXp1 : QFunNZ := qc [1] [1, 1]
/-- The ℚ(x) coefficient `x − 1`. -/
def cXm1 : QFunNZ := qc [-1, 1] [1]

/-- The fixed gcd target `(t + x)·(t − 1/x)` — degree 2 in `t` with ℚ(x) coefficients carrying genuine
denominators. Every benchmark `p`, `q` shares exactly this factor, so `gcd(p, q)` is its associate. -/
def commonFactor : CPolyG QFunNZ :=
  cmulG (lin cX (ofConstNZ 1)) (lin (qnegNZ cInvX) (ofConstNZ 1))

/-- The cofactor-coefficient cycle for `p` (period 5 through `x`, `1/x`, `x+1`, `1/(x+1)`, `x−1`). -/
def cycCoefA : ℕ → QFunNZ
  | 0 => cX | 1 => cInvX | 2 => cXp1 | 3 => cInvXp1 | 4 => cXm1 | n + 5 => cycCoefA n

/-- The cofactor-coefficient cycle for `q` (a phase-shifted permutation of `cycCoefA`, so the `p`- and
`q`-cofactors are coprime and `gcd(p, q) = commonFactor` exactly). -/
def cycCoefB : ℕ → QFunNZ
  | 0 => cInvXp1 | 1 => cXm1 | 2 => cX | 3 => cInvX | 4 => cXp1 | n + 5 => cycCoefB n

/-- The `p`-cofactor `∏_{i<k} (t + cycCoefA i)`, a `t`-polynomial of degree `k`. -/
def linProdA : ℕ → CPolyG QFunNZ
  | 0 => [ofConstNZ 1]
  | n + 1 => cmulG (lin (cycCoefA n) (ofConstNZ 1)) (linProdA n)

/-- The `q`-cofactor `∏_{i<k} (t − cycCoefB i)`, a `t`-polynomial of degree `k` coprime to `linProdA k`. -/
def linProdB : ℕ → CPolyG QFunNZ
  | 0 => [ofConstNZ 1]
  | n + 1 => cmulG (lin (qnegNZ (cycCoefB n)) (ofConstNZ 1)) (linProdB n)

/-- The benchmark dividend `p = commonFactor · linProdA k`, total `t`-degree `k + 2`. -/
def benchP (k : ℕ) : CPolyG QFunNZ := cmulG commonFactor (linProdA k)

/-- The benchmark divisor `q = commonFactor · linProdB k`, total `t`-degree `k + 2`; `gcd(benchP k,
benchQ k) = commonFactor` (degree 2) since the cofactors are coprime. -/
def benchQ (k : ℕ) : CPolyG QFunNZ := cmulG commonFactor (linProdB k)

/-- The fraction-free gcd of the benchmark pair (the fast kernel). -/
def benchFFGcd (k : ℕ) : CPolyG QFunNZ := cgcdFF 60 (benchP k) (benchQ k)

/-- The naive Euclidean gcd of the benchmark pair, monic-normalized (the swelling kernel). -/
def benchExtGcd (k : ℕ) : CPolyG QFunNZ := cmonicG (cgcdExtG 60 (benchP k) (benchQ k)).1

/-! ### The `qnorm`-in-the-loop gcd — the `qreduceG` fix prototype at `α = QFunNZ`

A Euclidean gcd that reduces every remainder coefficient to lowest terms (`Compute.qnorm`, the concrete
`QFunNZG.qreduceG` here) after each division step. It removes the *common-factor* swell, so the result
size stays flat; it does not bound the coprime coefficient-*degree* growth, so it is slower than `cgcdFF`
deeper in the tower (see the module docstring). -/

/-- Reduce one `QFunNZ` coefficient to lowest terms via `Compute.qnorm` (gcd-cancel of its
numerator/denominator) — the concrete `QFunNZG.qreduceG` at the ℚ(x) level. Falls back to the input if
the reduced denominator degenerates to zero. -/
def qnormCoeff (z : QFunNZ) : QFunNZ :=
  let r := Compute.qnorm 40 z.1
  if h : Compute.cisZero r.2 = false then
    ⟨r, fun hz => by
      rw [(Compute.cisZero_iff_toPoly_eq_zero r.2).mpr hz] at h; exact absurd h (by decide)⟩
  else z

/-- Reduce every coefficient of a `CPolyG QFunNZ` to lowest terms (`qnormCoeff` coefficientwise). -/
def normCoeffs (p : CPolyG QFunNZ) : CPolyG QFunNZ := (p : List QFunNZ).map qnormCoeff

/-- Euclidean division-with-remainder that `qnorm`-reduces each remainder's coefficients every step
(otherwise mirroring `cdivmodG`): `benchDivmodNorm fuel p q = (quotient, remainder)`. The per-step
reduction keeps the *integer* size of remainder coefficients bounded. -/
def benchDivmodNorm : ℕ → CPolyG QFunNZ → CPolyG QFunNZ → CPolyG QFunNZ × CPolyG QFunNZ
  | 0, p, _ => ([], cnormG p)
  | fuel + 1, p, q =>
    let p := cnormG p
    let q := cnormG q
    if cisZeroG q then ([], [])
    else if (p : List QFunNZ).length < (q : List QFunNZ).length then ([], p)
    else
      let c := CField.div (cleadG p) (cleadG q)
      let k := (p : List QFunNZ).length - (q : List QFunNZ).length
      let term := cshiftG k [c]
      let p' := normCoeffs (cnormG (csubG p (cmulG term q)))
      let (quo, rem) := benchDivmodNorm fuel p' q
      (caddG term quo, rem)

/-- The remainder of `benchDivmodNorm` (`cdivmodG`-style remainder with per-step `qnorm`). -/
def benchModNorm (fuel : ℕ) (p q : CPolyG QFunNZ) : CPolyG QFunNZ := (benchDivmodNorm fuel p q).2

/-- Plain (non-extended) Euclidean gcd loop with per-step coefficient `qnorm` (`benchModNorm` for the
remainder, `normCoeffs` after each step): the `qreduceG`-in-the-loop gcd at `α = QFunNZ`. -/
def benchNormGcdGo : ℕ → CPolyG QFunNZ → CPolyG QFunNZ → CPolyG QFunNZ
  | 0, a, _ => cnormG a
  | fuel + 1, a, b =>
    if cisZeroG b then cnormG a
    else benchNormGcdGo fuel b (normCoeffs (benchModNorm (fuel + 1) a b))

/-- The monic `qnorm`-in-the-loop gcd of the benchmark pair (the swell-controlled prototype). -/
def benchNormGcd (k : ℕ) : CPolyG QFunNZ :=
  normCoeffs (cmonicG (benchNormGcdGo 60 (benchP k) (benchQ k)))

/-! ### The swell measure and the pinned witnesses (`native_decide`) -/

/-- The raw stored size of one `QFunNZ` coefficient: total length of its numerator/denominator lists plus
the sum of `|num| + den` of each ℚ entry — a faithful proxy for the (unreduced) representation size. -/
def coeffSizeRaw (z : QFunNZ) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + c.num.natAbs + c.den) 0) +
    (z.1.2.foldl (fun a c => a + c.num.natAbs + c.den) 0)

/-- The raw stored size of a whole `CPolyG QFunNZ` (`coeffSizeRaw` summed over coefficients, plus the
`t`-length). Forcing this fully evaluates the gcd, so a timing harness cannot hide cost behind laziness. -/
def gcdSizeRaw (g : CPolyG QFunNZ) : ℕ :=
  (g : List QFunNZ).foldl (fun a z => a + coeffSizeRaw z) g.length

/-- **The benchmark gcd is degree 2** for the fraction-free kernel (`native_decide`): `gcd(p, q)` is the
associate of `commonFactor`, so the cofactor scaling does not change the *answer* — only the intermediate
coefficient size, which is what the swell witnesses measure. -/
theorem benchFFGcd_deg_two : cdegG (benchFFGcd 2) = 2 := by native_decide

/-- **The fraction-free and `qnorm`-loop kernels compute the same monic gcd** (`native_decide`): their
monic normalizations agree (`cisZeroG` of the difference), so `benchNormGcd` is a correct gcd — the
swell control is a pure performance variant, not a different answer. -/
theorem benchNormGcd_agrees_cgcdFF :
    cisZeroG (csubG (cmonicG (benchFFGcd 2)) (cmonicG (benchNormGcd 2))) = true := by native_decide

/-- **Fraction-free result size stays flat** (`native_decide`): the raw stored coefficient size of
`benchFFGcd` is `36` at total degree 3 **and** `36` at total degree 4 — no swell. -/
theorem benchFFGcd_size_flat :
    gcdSizeRaw (benchFFGcd 1) = 36 ∧ gcdSizeRaw (benchFFGcd 2) = 36 := by native_decide

/-- **The naive Euclidean result swells super-exponentially** (`native_decide`): the raw stored
coefficient size of `benchExtGcd` is `147` at total degree 3 but `258 261 011 921` (~2.6·10¹¹) at total
degree 4 — a single extra degree multiplies the stored size by over a billion. This is the
coefficient-swell signature the fraction-free kernel exists to avoid. -/
theorem benchExtGcd_size_swells :
    gcdSizeRaw (benchExtGcd 1) = 147 ∧ gcdSizeRaw (benchExtGcd 2) = 258261011921 := by native_decide

/-- **The `qnorm`-in-the-loop fix flattens the result size** (`native_decide`): the raw stored
coefficient size of `benchNormGcd` is `28` at both total degree 3 and 4 — reducing each remainder to
lowest terms removes the swell *from the result*, matching the fraction-free kernel rather than the naive
Euclidean one (`28`/`28` vs `147`/`2.6·10¹¹`). The remaining gap to `cgcdFF` is the per-step `qnorm`
cost, not the answer size (see the module docstring). -/
theorem benchNormGcd_size_flat :
    gcdSizeRaw (benchNormGcd 1) = 28 ∧ gcdSizeRaw (benchNormGcd 2) = 28 := by native_decide

end Bench

end DeepWiki.SymbolicIntegration
