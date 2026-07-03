import DeepWiki.SymbolicIntegration.Computable.QFunReduce
import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFF

/-! # Coefficient-swell benchmark for `t`-polynomial gcd over `QFunNZG ℚ`
Compares the fraction-free `cgcdFFGen`, the naive Euclidean `cgcdExtG`, and a `qReduce`-in-the-loop
variant. Naive Euclidean coefficients swell super-exponentially; the fraction-free kernel stays flat and
`qReduce`-per-step tames but does not fully bound the swell. -/

namespace DeepWiki.SymbolicIntegration

open Compute QFunNZG CPolyG

namespace Bench

open BenchG

/-! ### Benchmark inputs — reusing `BenchG`'s `QFunNZG ℚ` data (gcd fixed at degree 2) -/

/-- The benchmark dividend `p = gCommonFactor · glinProdA k` over `QFunNZG ℚ`, total `t`-degree `k + 2`. -/
def benchP (k : ℕ) : CPolyG (QFunNZG ℚ) := gBenchP k

/-- The benchmark divisor `q = gCommonFactor · glinProdB k` over `QFunNZG ℚ`, total `t`-degree `k + 2`;
`gcd(benchP k, benchQ k) = gCommonFactor` (degree 2). -/
def benchQ (k : ℕ) : CPolyG (QFunNZG ℚ) := gBenchQ k

/-- The naive Euclidean gcd `cmonicG (cgcdWf …)` of the benchmark pair, monic-normalized (the swelling
kernel over the fraction field). -/
def benchExtGcd (k : ℕ) : CPolyG (QFunNZG ℚ) := cmonicG (cgcdWf (benchP k) (benchQ k)).1

/-! ### The `qReduce`-in-the-loop gcd — the swell-control prototype at `α = QFunNZG ℚ` -/

/-- Reduce every coefficient of a `CPolyG (QFunNZG ℚ)` to lowest terms (`qReduce`
coefficientwise). -/
def normCoeffs (p : CPolyG (QFunNZG ℚ)) : CPolyG (QFunNZG ℚ) :=
  (p : List (QFunNZG ℚ)).map qReduce

/-- Euclidean division-with-remainder that `qReduce`-reduces each remainder's coefficients every step
(otherwise mirroring `cdivmodG`): `benchDivmodNorm fuel p q = (quotient, remainder)`. -/
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

/-- The remainder of `benchDivmodNorm` (`cdivmodG`-style remainder with per-step `qReduce`). -/
def benchModNorm (fuel : ℕ) (p q : CPolyG (QFunNZG ℚ)) : CPolyG (QFunNZG ℚ) :=
  (benchDivmodNorm fuel p q).2

/-- Plain Euclidean gcd loop with per-step coefficient `qReduce` (`benchModNorm` remainder, `normCoeffs`
each step): the swell-control gcd at `α = QFunNZG ℚ`. -/
def benchNormGcdGo : ℕ → CPolyG (QFunNZG ℚ) → CPolyG (QFunNZG ℚ) → CPolyG (QFunNZG ℚ)
  | 0, a, _ => cnormG a
  | fuel + 1, a, b =>
    if cisZeroG b then cnormG a
    else benchNormGcdGo fuel b (normCoeffs (benchModNorm (fuel + 1) a b))

/-- The monic `qReduce`-in-the-loop gcd of the benchmark pair (the swell-controlled prototype). -/
def benchNormGcd (k : ℕ) : CPolyG (QFunNZG ℚ) :=
  normCoeffs (cmonicG (benchNormGcdGo 60 (benchP k) (benchQ k)))

/-! ### The swell measure and the pinned witnesses (`native_decide`) -/

/-- The raw stored size of a whole `CPolyG (QFunNZG ℚ)` (`BenchG.gGcdSizeRaw`). -/
def gcdSizeRaw (g : CPolyG (QFunNZG ℚ)) : ℕ := gGcdSizeRaw g

/-- The naive Euclidean result swells: `gcdSizeRaw (benchExtGcd 1) = 147` but `benchExtGcd 2` has raw
stored size `258261011921`. -/
theorem benchExtGcd_size_swells :
    gcdSizeRaw (benchExtGcd 1) = 147 ∧ gcdSizeRaw (benchExtGcd 2) = 258261011921 := by native_decide

/-- The `qReduce`-in-the-loop gcd tames the result size: `gcdSizeRaw (benchNormGcd 1) = 28` and
`benchNormGcd 2` has raw stored size `405`, far below the naive Euclidean kernel. -/
theorem benchNormGcd_size_tamed :
    gcdSizeRaw (benchNormGcd 1) = 28 ∧ gcdSizeRaw (benchNormGcd 2) = 405 := by native_decide

end Bench

end DeepWiki.SymbolicIntegration
