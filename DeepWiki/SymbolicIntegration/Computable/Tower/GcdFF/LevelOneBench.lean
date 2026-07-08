import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFF.Denominators

/-! # Level-1 fraction-free gcd benchmark inputs

Benchmark inputs over `QFunNZG ℚ ≅ ℚ(x)` for comparing tower gcd behavior.
-/

namespace DeepWiki.SymbolicIntegration

/-! ### Level-1 benchmark inputs over `QFunNZG ℚ ≅ ℚ(x)` -/

namespace BenchG

open CPolyG QFunNZG

/-- Build a `QFunNZG ℚ` ℚ(x)-coefficient `num/den` (coefficient lists low→high in `x`), denominator
nonzero by `decide`. Falls back to `0/1` if the denominator degenerates. -/
def gqc (num den : CPolyG ℚ) (h : CPolyG.cisZeroG den = false := by decide) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-- The ℚ(x) coefficient `x` as a `QFunNZG ℚ`. -/
def gcX : QFunNZG ℚ := gqc [0, 1] [1]
/-- The ℚ(x) coefficient `1/x` (a genuine denominator). -/
def gcInvX : QFunNZG ℚ := gqc [1] [0, 1]
/-- The ℚ(x) coefficient `x + 1`. -/
def gcXp1 : QFunNZG ℚ := gqc [1, 1] [1]
/-- The ℚ(x) coefficient `1/(x + 1)`. -/
def gcInvXp1 : QFunNZG ℚ := gqc [1] [1, 1]
/-- The ℚ(x) coefficient `x − 1`. -/
def gcXm1 : QFunNZG ℚ := gqc [-1, 1] [1]

/-- `(1 : QFunNZG ℚ)` shorthand for building monic cofactors. -/
def gOne : QFunNZG ℚ := qoneNZG
/-- Negate a `QFunNZG ℚ` coefficient (denominator unchanged). -/
def gNeg (z : QFunNZG ℚ) : QFunNZG ℚ := qnegNZG z

/-- A linear `t`-polynomial `a0 + a1·t` as a `CPolyG (QFunNZG ℚ)` (low→high in `t`). -/
def glin (a0 a1 : QFunNZG ℚ) : CPolyG (QFunNZG ℚ) := [a0, a1]

/-- The fixed gcd target `(t + x)·(t − 1/x)` over `QFunNZG ℚ` — degree 2 in `t`, ℚ(x) coefficients with
genuine denominators. -/
def gCommonFactor : CPolyG (QFunNZG ℚ) :=
  cmulG (glin gcX gOne) (glin (gNeg gcInvX) gOne)

/-- The cofactor-coefficient cycle for `p` (period 5: `x`, `1/x`, `x+1`, `1/(x+1)`, `x−1`). -/
def gcycCoefA : ℕ → QFunNZG ℚ
  | 0 => gcX | 1 => gcInvX | 2 => gcXp1 | 3 => gcInvXp1 | 4 => gcXm1 | n + 5 => gcycCoefA n

/-- The cofactor-coefficient cycle for `q` (phase-shifted, coprime to `gcycCoefA`). -/
def gcycCoefB : ℕ → QFunNZG ℚ
  | 0 => gcInvXp1 | 1 => gcXm1 | 2 => gcX | 3 => gcInvX | 4 => gcXp1 | n + 5 => gcycCoefB n

/-- The `p`-cofactor `∏_{i<k} (t + gcycCoefA i)`, a `t`-polynomial of degree `k`. -/
def glinProdA : ℕ → CPolyG (QFunNZG ℚ)
  | 0 => [gOne]
  | n + 1 => cmulG (glin (gcycCoefA n) gOne) (glinProdA n)

/-- The `q`-cofactor `∏_{i<k} (t − gcycCoefB i)`, a `t`-polynomial of degree `k` coprime to
`glinProdA k`. -/
def glinProdB : ℕ → CPolyG (QFunNZG ℚ)
  | 0 => [gOne]
  | n + 1 => cmulG (glin (gNeg (gcycCoefB n)) gOne) (glinProdB n)

/-- The benchmark dividend `p = gCommonFactor · glinProdA k` over `QFunNZG ℚ`, total `t`-degree `k + 2`. -/
def gBenchP (k : ℕ) : CPolyG (QFunNZG ℚ) := cmulG gCommonFactor (glinProdA k)

/-- The benchmark divisor `q = gCommonFactor · glinProdB k` over `QFunNZG ℚ`, total `t`-degree `k + 2`;
`gcd(gBenchP k, gBenchQ k) = gCommonFactor` (degree 2). -/
def gBenchQ (k : ℕ) : CPolyG (QFunNZG ℚ) := cmulG gCommonFactor (glinProdB k)

/-! #### The swell measure over `QFunNZG ℚ` (mirror of `Bench.gcdSizeRaw`) -/

/-- The raw stored size of one `QFunNZG ℚ` coefficient: total numerator/denominator list lengths plus the
sum of `|num| + den` of each ℚ entry. -/
def gCoeffSizeRaw (z : QFunNZG ℚ) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + c.num.natAbs + c.den) 0) +
    (z.1.2.foldl (fun a c => a + c.num.natAbs + c.den) 0)

/-- The raw stored size of a whole `CPolyG (QFunNZG ℚ)`: `gCoeffSizeRaw` summed over coefficients plus
the `t`-length. -/
def gGcdSizeRaw (g : CPolyG (QFunNZG ℚ)) : ℕ :=
  (g : List (QFunNZG ℚ)).foldl (fun a z => a + gCoeffSizeRaw z) g.length

end BenchG

end DeepWiki.SymbolicIntegration
