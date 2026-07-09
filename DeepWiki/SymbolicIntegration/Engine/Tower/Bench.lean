import DeepWiki.SymbolicIntegration.Engine.QFunReduce
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFF

/-! # Coefficient-swell benchmark for `t`-polynomial gcd over `QFunNZ ℚ`
Compares the fraction-free `cgcdFFGen`, the naive Euclidean `cgcdExtG`, and a `qReduce`-in-the-loop
variant. Naive Euclidean coefficients swell super-exponentially; the fraction-free kernel stays flat and
`qReduce`-per-step tames but does not fully bound the swell. -/

namespace DeepWiki.SymbolicIntegration

open QFunNZ CPoly

namespace Bench

open BenchG

/-! ### Benchmark inputs — reusing `BenchG`'s `QFunNZ ℚ` data (gcd fixed at degree 2) -/

/-- The benchmark dividend `p = gCommonFactor · glinProdA k` over `QFunNZ ℚ`, total `t`-degree `k + 2`. -/
def benchP (k : ℕ) : CPoly (QFunNZ ℚ) := gBenchP k

/-- The benchmark divisor `q = gCommonFactor · glinProdB k` over `QFunNZ ℚ`, total `t`-degree `k + 2`;
`gcd(benchP k, benchQ k) = gCommonFactor` (degree 2). -/
def benchQ (k : ℕ) : CPoly (QFunNZ ℚ) := gBenchQ k

/-- The naive Euclidean gcd `cmonic (cgcdWf …)` of the benchmark pair, monic-normalized (the swelling
kernel over the fraction field). -/
def benchExtGcd (k : ℕ) : CPoly (QFunNZ ℚ) := cmonic (cgcdWf (benchP k) (benchQ k)).1

/-! ### The `qReduce`-in-the-loop gcd — the swell-control prototype at `α = QFunNZ ℚ` -/

/-- Reduce every coefficient of a `CPoly (QFunNZ ℚ)` to lowest terms (`qReduce`
coefficientwise). -/
def normCoeffs (p : CPoly (QFunNZ ℚ)) : CPoly (QFunNZ ℚ) :=
  (p : List (QFunNZ ℚ)).map qReduce

/-- Euclidean division-with-remainder that `qReduce`-reduces each remainder's coefficients every step
(otherwise mirroring `cdivmodG`): `benchDivmodNorm fuel p q = (quotient, remainder)`. -/
def benchDivmodNorm : ℕ → CPoly (QFunNZ ℚ) → CPoly (QFunNZ ℚ) →
    CPoly (QFunNZ ℚ) × CPoly (QFunNZ ℚ)
  | 0, p, _ => ([], cnorm p)
  | fuel + 1, p, q =>
    let p := cnorm p
    let q := cnorm q
    if cisZero q then ([], [])
    else if (p : List (QFunNZ ℚ)).length < (q : List (QFunNZ ℚ)).length then ([], p)
    else
      let c := CField.div (clead p) (clead q)
      let k := (p : List (QFunNZ ℚ)).length - (q : List (QFunNZ ℚ)).length
      let term := cshift k [c]
      let p' := normCoeffs (cnorm (csub p (cmul term q)))
      let (quo, rem) := benchDivmodNorm fuel p' q
      (cadd term quo, rem)

/-- The remainder of `benchDivmodNorm` (`cdivmodG`-style remainder with per-step `qReduce`). -/
def benchModNorm (fuel : ℕ) (p q : CPoly (QFunNZ ℚ)) : CPoly (QFunNZ ℚ) :=
  (benchDivmodNorm fuel p q).2

/-- Plain Euclidean gcd loop with per-step coefficient `qReduce` (`benchModNorm` remainder, `normCoeffs`
each step): the swell-control gcd at `α = QFunNZ ℚ`. -/
def benchNormGcdGo : ℕ → CPoly (QFunNZ ℚ) → CPoly (QFunNZ ℚ) → CPoly (QFunNZ ℚ)
  | 0, a, _ => cnorm a
  | fuel + 1, a, b =>
    if cisZero b then cnorm a
    else benchNormGcdGo fuel b (normCoeffs (benchModNorm (fuel + 1) a b))

/-- The monic `qReduce`-in-the-loop gcd of the benchmark pair (the swell-controlled prototype). -/
def benchNormGcd (k : ℕ) : CPoly (QFunNZ ℚ) :=
  normCoeffs (cmonic (benchNormGcdGo 60 (benchP k) (benchQ k)))

/-! ### The swell measure and the pinned witnesses (`native_decide`) -/

/-- The raw stored size of a whole `CPoly (QFunNZ ℚ)` (`BenchG.gGcdSizeRaw`). -/
def gcdSizeRaw (g : CPoly (QFunNZ ℚ)) : ℕ := gGcdSizeRaw g

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
