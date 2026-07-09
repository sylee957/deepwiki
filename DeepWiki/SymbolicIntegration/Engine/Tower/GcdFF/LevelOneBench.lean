import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFF.Denominators

/-! # A shared level-1 tower test coefficient `gcInvX = 1/x ∈ CFrac ℚ`

A ℚ(x)-coefficient with a genuine denominator, over `CFrac ℚ ≅ ℚ(x)`, used as `t`-polynomial coefficient
data by the LRT guarded-diff example. -/

namespace DeepWiki.SymbolicIntegration

namespace BenchG

/-- Build a `CFrac ℚ` ℚ(x)-coefficient `num/den` (coefficient lists low→high in `x`), denominator
nonzero by `decide`. -/
def gqc (num den : CPoly ℚ) (h : CPoly.cisZero den = false := by decide) : CFrac ℚ :=
  ⟨(num, den), h⟩

/-- The ℚ(x) coefficient `1/x` (a genuine denominator). -/
def gcInvX : CFrac ℚ := gqc [1] [0, 1]

end BenchG

end DeepWiki.SymbolicIntegration
