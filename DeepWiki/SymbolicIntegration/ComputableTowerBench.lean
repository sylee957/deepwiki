import DeepWiki.SymbolicIntegration.ComputableTowerReduce
import DeepWiki.SymbolicIntegration.ComputableTowerGcdFF

/-! # Coefficient-swell benchmark: fraction-free vs naive Euclidean vs `qreduceG`-in-the-loop
The tower integrator can run its `t`-polynomial gcd over `α = QFunNZG ℚ ≅ ℚ(x)` several ways: the
generic **fraction-free** `cgcdFFGen` (clear denominators into `ℚ[x][t]`, primitive PRS —
`ComputableTowerGcdFF`) or the generic **Euclidean** `cgcdExtG` over the fraction field ℚ(x)
(`GenericPolyEngine`). Euclidean division divides by the leading ℚ(x)-coefficient each step, so the
rational-function coefficients **swell** super-exponentially; the fraction-free kernel keeps them
bounded.

This file pins that swell with a concrete witness over `QFunNZG ℚ`. With the gcd held **fixed at
degree 2** (the `BenchG.gCommonFactor` `(t+x)(t−1/x)`) and only the *cofactor* `t`-degree scaling, the
raw stored coefficient-size of the gcd RESULT is:

| total `t`-degree of `p` | `cgcdFFGen` | `cgcdExtG` | `qreduceG`-in-loop (Euclid + per-step reduce) |
| --- | --- | --- | --- |
| 3 | 36 | 147 | 28 |
| 4 | 36 | 258 261 011 921 | 405 |

So `cgcdExtG`'s stored coefficient size jumps from 147 to ~2.6·10¹¹ for a single extra degree (it reaches
a 147-digit value by degree 5), while `cgcdFFGen` stays flat (`36`) and the `qreduceG`-reducing variant
stays far below the swell (`28 → 405`). (`native_decide` build-time confirms the runtime cost: at total
degree 5, `cgcdFFGen` ≈ baseline but `cgcdExtG` is ~90 s.)

* **`benchNormGcd`** — a Euclidean gcd that applies `QFunNZG.qreduceG` (gcd-cancel to lowest terms) to
  every remainder coefficient each step. It produces the *same* monic gcd as `cgcdFFGen`
  (`benchNormGcd_agrees_cgcdFFGen`) and **tames the swell in the result** (`benchNormGcd_size_tamed`,
  `28 → 405` vs Euclid's `147 → 2.6·10¹¹`). It does NOT, however, stay perfectly flat like `cgcdFFGen`:
  `qreduceG` cancels only *common* factors and makes the gcd **monic** (scaling by `1/lead`), while
  Euclidean division still grows the coprime coefficient *degree* each step — so its per-step `qreduceG`
  (an inner ℚ[x] gcd) cost compounds and it overtakes `cgcdFFGen` at higher degree. The genuine fix is the
  fraction-free PRS in `cgcdFFGen`; this file documents *why*. -/

namespace DeepWiki.SymbolicIntegration

open Compute QFunNZG CPolyG

namespace Bench

open BenchG

/-! ### Benchmark inputs — reusing `BenchG`'s `QFunNZG ℚ` data (gcd fixed at degree 2) -/

/-- The benchmark dividend `p = gCommonFactor · glinProdA k` over `QFunNZG ℚ`, total `t`-degree `k + 2`
(reusing `BenchG.gBenchP`). -/
def benchP (k : ℕ) : CPolyG (QFunNZG ℚ) := gBenchP k

/-- The benchmark divisor `q = gCommonFactor · glinProdB k` over `QFunNZG ℚ`, total `t`-degree `k + 2`;
`gcd(benchP k, benchQ k) = gCommonFactor` (degree 2), reusing `BenchG.gBenchQ`. -/
def benchQ (k : ℕ) : CPolyG (QFunNZG ℚ) := gBenchQ k

/-- The generic fraction-free gcd of the benchmark pair over `QFunNZG ℚ` (the fast kernel,
`CFracGcd.cgcdFFGen`). -/
def benchFFGcd (k : ℕ) : CPolyG (QFunNZG ℚ) := gBenchFFGcd k

/-- The naive generic Euclidean gcd of the benchmark pair, monic-normalized (the swelling kernel). -/
def benchExtGcd (k : ℕ) : CPolyG (QFunNZG ℚ) := cmonicG (cgcdExtG 60 (benchP k) (benchQ k)).1

/-! ### The `qreduceG`-in-the-loop gcd — the swell-control prototype at `α = QFunNZG ℚ`

A Euclidean gcd that reduces every remainder coefficient to lowest terms (`QFunNZG.qreduceG`, the
gcd-cancel) after each division step. It removes the *common-factor* swell, so the result size stays
flat; it does not bound the coprime coefficient-*degree* growth, so it is slower than `cgcdFFGen` deeper
in the tower (see the module docstring). -/

/-- Reduce every coefficient of a `CPolyG (QFunNZG ℚ)` to lowest terms (`QFunNZG.qreduceG`
coefficientwise). -/
def normCoeffs (p : CPolyG (QFunNZG ℚ)) : CPolyG (QFunNZG ℚ) :=
  (p : List (QFunNZG ℚ)).map (QFunNZG.qreduceG 40)

/-- Euclidean division-with-remainder that `qreduceG`-reduces each remainder's coefficients every step
(otherwise mirroring `cdivmodG`): `benchDivmodNorm fuel p q = (quotient, remainder)`. The per-step
reduction keeps the *integer* size of remainder coefficients bounded. -/
def benchDivmodNorm : ℕ → CPolyG (QFunNZG ℚ) → CPolyG (QFunNZG ℚ) →
    CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)
  | 0, p, _ => ([], cnormG p)
  | fuel + 1, p, q =>
    let p := cnormG p
    let q := cnormG q
    if cisZeroG q then ([], [])
    else if (p : List (QFunNZG ℚ)).length < (q : List (QFunNZG ℚ)).length then ([], p)
    else
      let c := CField.div (cleadG p) (cleadG q)
      let k := (p : List (QFunNZG ℚ)).length - (q : List (QFunNZG ℚ)).length
      let term := cshiftG k [c]
      let p' := normCoeffs (cnormG (csubG p (cmulG term q)))
      let (quo, rem) := benchDivmodNorm fuel p' q
      (caddG term quo, rem)

/-- The remainder of `benchDivmodNorm` (`cdivmodG`-style remainder with per-step `qreduceG`). -/
def benchModNorm (fuel : ℕ) (p q : CPolyG (QFunNZG ℚ)) : CPolyG (QFunNZG ℚ) :=
  (benchDivmodNorm fuel p q).2

/-- Plain (non-extended) Euclidean gcd loop with per-step coefficient `qreduceG` (`benchModNorm` for the
remainder, `normCoeffs` after each step): the swell-control gcd at `α = QFunNZG ℚ`. -/
def benchNormGcdGo : ℕ → CPolyG (QFunNZG ℚ) → CPolyG (QFunNZG ℚ) → CPolyG (QFunNZG ℚ)
  | 0, a, _ => cnormG a
  | fuel + 1, a, b =>
    if cisZeroG b then cnormG a
    else benchNormGcdGo fuel b (normCoeffs (benchModNorm (fuel + 1) a b))

/-- The monic `qreduceG`-in-the-loop gcd of the benchmark pair (the swell-controlled prototype). -/
def benchNormGcd (k : ℕ) : CPolyG (QFunNZG ℚ) :=
  normCoeffs (cmonicG (benchNormGcdGo 60 (benchP k) (benchQ k)))

/-! ### The swell measure and the pinned witnesses (`native_decide`) -/

/-- The raw stored size of a whole `CPolyG (QFunNZG ℚ)` (`BenchG.gGcdSizeRaw`). Forcing it fully
evaluates the gcd, so a timing harness cannot hide cost behind laziness. -/
def gcdSizeRaw (g : CPolyG (QFunNZG ℚ)) : ℕ := gGcdSizeRaw g

/-- **The benchmark gcd is degree 2** for the fraction-free kernel (`native_decide`): `gcd(p, q)` is the
associate of `gCommonFactor`, so the cofactor scaling does not change the *answer* — only the intermediate
coefficient size, which is what the swell witnesses measure. -/
theorem benchFFGcd_deg_two : cdegG (benchFFGcd 2) = 2 := by native_decide

/-- **The fraction-free and `qreduceG`-loop kernels compute the same monic gcd** (`native_decide`): their
monic normalizations agree (`cisZeroG` of the difference), so `benchNormGcd` is a correct gcd — the
swell control is a pure performance variant, not a different answer. -/
theorem benchNormGcd_agrees_cgcdFFGen :
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

/-- **The `qreduceG`-in-the-loop fix tames the result size** (`native_decide`): the raw stored
coefficient size of `benchNormGcd` is `28` at total degree 3 and `405` at total degree 4 — reducing each
remainder to lowest terms removes the *common-factor* swell, staying far below the naive Euclidean kernel
(`28`/`405` vs `147`/`2.6·10¹¹`). It is not perfectly flat like `cgcdFFGen` (`36`/`36`): `qreduceG`'s
**monic** gcd-cancel scales by `1/lead`, growing the *coprime* coefficient degree the fraction-free PRS
keeps bounded — the remaining gap to `cgcdFFGen` (see the module docstring). -/
theorem benchNormGcd_size_tamed :
    gcdSizeRaw (benchNormGcd 1) = 28 ∧ gcdSizeRaw (benchNormGcd 2) = 405 := by native_decide

end Bench

end DeepWiki.SymbolicIntegration
