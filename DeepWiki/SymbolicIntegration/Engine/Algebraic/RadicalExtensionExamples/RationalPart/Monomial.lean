import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension

/-! # Monomial rational-part examples for simple radical extensions

Concrete `native_decide` checks for radical rational-part reductions over
`θ = log v` and `θ = exp v` monomial towers.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly

/-! #### `θ = log v` validates: degree-lowering `∫ C/y` over `ℚ(x)[log x]`, `y = √(log x)`

A 2-level tower: base `ℚ(x)`, monomial `θ = log x` (`θ' = 1/x`), radicand `y² = f = log x`, `g = 1/(2x)`.
For `C` with leading term `(5/(2x))θ²` the bracket `(j+1)·θ' + lcf(g) = 5/(2x)` gives the constant `b = 1`,
`B = θ²`, and residual `D = −θ`, dropping `deg_θ C` by one. -/

/-- `θ' = (log x)' = v'/v = 1/x ∈ ℚ(x)` (numerator `[1]`, denominator `[0,1] = x`), the derivative of
the monomial `θ = log x`. -/
def logDt : QFunNZG ℚ := qxOfFrac [1] [0, 1] (by decide)

/-- The ℚ(x) leading coefficient `lcf(g) = g = 1/(2x)` for `f = θ`, `g = (1/2)f'/f·f = 1/(2x)`
(numerator `[1]`, denominator `[0,2] = 2x`). -/
def logGlead : QFunNZG ℚ := qxOfFrac [1] [0, 2] (by decide)

/-- The radicand `f = θ = log x ∈ ℚ(x)[θ]` (`y² = log x`), the `θ`-polynomial `[0, 1]`. -/
def logF : CPoly (QFunNZG ℚ) := [CField.zero, CField.one]

/-- `g = 1/(2x)` as a degree-`0`-in-θ element of `ℚ(x)[θ]` (`(f/y)' = g/y`), `[1/(2x)]`. -/
def logG : CPoly (QFunNZG ℚ) := [logGlead]

/-- The numerator `C = (5/(2x))θ² + θ ∈ ℚ(x)[θ]` (`deg_θ C = 2 ≥ m`), with leading coefficient
`5/(2x) = (j+1)θ' + lcf(g)` chosen so the constant `b = 1` solves eq. 5. -/
def logC : CPoly (QFunNZG ℚ) := [CField.zero, CField.one, qxOfFrac [5] [0, 2] (by decide)]

/-- The `θ`-derivative as a polynomial `[θ'] = [1/x] ∈ ℚ(x)[θ]`, the `Dt` for `cmonomialDeriv`. -/
def logDtPoly : CPoly (QFunNZG ℚ) := [logDt]

/-- The solved `θ = log v` leading-coefficient cofactor `B = b·θ² = 1·θ²` (`b = lcf(C)/bracket =
(5/(2x))/(5/(2x)) = 1`, a constant). -/
def logB : CPoly (QFunNZG ℚ) := radCase3CofactorGen logDt logF logG logC

/-- The `θ = log v` residual `D = B'f + Bg − C`, with `B' = cmonomialDeriv [θ'] B` the full log-monomial
derivative — expected `−θ` (degree `1 < deg_θ C = 2`). -/
def logD : CPoly (QFunNZG ℚ) :=
  radCase3Residual logF logG logB logC (cmonomialDeriv logDtPoly logB)

/-- The `log` cofactor is the constant monomial `B = θ²`: `b = (5/(2x))/((2)(1/x) + 1/(2x)) = 1` at
degree `j+1 = 2`. -/
theorem logCase_cofactor_eq :
    cisZeroG (csubG logB [CField.zero, CField.zero, (CField.one : QFunNZG ℚ)]) = true := by
  native_decide

/-- The `θ = log v` cleared identity `B'f + Bg − C = D` in `ℚ(x)[log x]` (`B = θ²`, `B' = cmonomialDeriv
[1/x] B`, `D = −θ`). -/
theorem logCase_cleared_identity :
    cisZeroG (csubG
      (csubG (caddG (cmulG (cmonomialDeriv logDtPoly logB) logF) (cmulG logB logG)) logC)
      logD) = true := by native_decide

/-- The `log` residual `D = −θ` has `θ`-degree `1`, strictly below `deg_θ C = 2`. -/
theorem logCase_residual_eq :
    cisZeroG (csubG logD [CField.zero, (CField.neg CField.one : QFunNZG ℚ)]) = true := by native_decide

/-- The `θ = log v` step strictly lowers `deg_θ C`: `deg D = 1 < deg C = 2` over `ℚ(x)[log x]`. -/
theorem logCase_degree_drop : cdegG logD < cdegG logC := by native_decide

/-! #### `θ = exp v` validates: `∫ C/(θy)` over `ℚ(x)[eˣ]`, `y = √(eˣ+1)`

A 2-level exponential tower: base `ℚ(x)`, monomial `θ = exp x` (`θ' = θ`), radicand `y² = f = eˣ + 1`,
`g = (1/2)θ`. The `C/(θy)` step (`k = 1`, `C = θ + 1`): the constant-term match gives `b₀ = −1`,
`B = [−1]`, residual `D = −1/2`, dropping `k = 1 → 0`. -/

/-- The radicand `f = θ + 1 = eˣ + 1 ∈ ℚ(x)[θ]` (`y² = eˣ + 1`, `θ ∤ f`, `f₀ = 1`), `[1, 1]`. -/
def expF : CPoly (QFunNZG ℚ) := [CField.one, CField.one]

/-- `g = (1/2)θ ∈ ℚ(x)[θ]` for `f = θ+1`, `θ = exp x` (`(f/y)' = g/y`, `g₀ = 0`), `[0, 1/2]`. -/
def expG : CPoly (QFunNZG ℚ) := [CField.zero, qxOfNum [1/2]]

/-- The numerator `C = θ + 1 ∈ ℚ(x)[θ]` (`c₀ = 1`), `[1, 1]`. -/
def expC : CPoly (QFunNZG ℚ) := [CField.one, CField.one]

/-- `v' = (x)' = 1 ∈ ℚ(x)` for `θ = exp x` (`v = x`), the `CField.one` of `QFunNZG ℚ`. -/
def expVder : QFunNZG ℚ := CField.one

/-- `θ' = v'·θ = θ` as the `Dt` polynomial `[0, 1] ∈ ℚ(x)[θ]` for `cmonomialDeriv` (`θ = exp x` is a
factor of its own derivative). -/
def expDtPoly : CPoly (QFunNZG ℚ) := [CField.zero, CField.one]

/-- The solved `θ = exp v` `C/(θy)` cofactor `B = [b₀] = [−1]` (`b₀ = c₀/(g₀ − kv'f₀) = 1/(0−1) = −1`,
a constant). -/
def expB : CPoly (QFunNZG ℚ) := radExpCofactor 1 expVder expF expG expC

/-- The `θ = exp v` `C/(θy)` residual `D = ((B'f + Bg − kv'Bf) − C)/θ`, `B' = cmonomialDeriv [θ] B` —
expected `−1/2` (the multiplicity dropped `k = 1 → 0`). -/
def expD : CPoly (QFunNZG ℚ) :=
  radExpResidual 1 expVder expF expG expB expC (cmonomialDeriv expDtPoly expB)

/-- The `exp` cofactor is the constant `B = [−1]`: `b₀ = 1/(0 − 1·1·1) = −1` over `ℚ(x)[eˣ]`. -/
theorem expCase_cofactor_eq :
    cisZeroG (csubG expB [(CField.neg CField.one : QFunNZG ℚ)]) = true := by native_decide

/-- The `θ = exp v` constant-term congruence `(B'f + Bg − kv'Bf) − C ≡ 0 (mod θ)`: the numerator `(−1/2)θ`
is divisible by `θ`. -/
theorem expCase_congruence :
    cisZeroG (cmodWf
      (csubG (csubG (caddG (cmulG (cmonomialDeriv expDtPoly expB) expF) (cmulG expB expG))
          (cmulG [CField.mul (cnatCastG 1) expVder] (cmulG expB expF))) expC)
      [CField.zero, CField.one]) = true := by native_decide

/-- The `θ = exp v` cleared identity `(B'f + Bg − k·v'·B·f) − C = θ·D` in `ℚ(x)[eˣ]` (`B = [−1]`,
`D = [−1/2]`). -/
theorem expCase_cleared_identity :
    cisZeroG (csubG
      (csubG (csubG (caddG (cmulG (cmonomialDeriv expDtPoly expB) expF) (cmulG expB expG))
          (cmulG [CField.mul (cnatCastG 1) expVder] (cmulG expB expF))) expC)
      (cmulG [CField.zero, CField.one] expD)) = true := by native_decide

/-- The `exp` residual `D = −1/2` (a `θ`-constant): the `C/(θᵏy)` step lowered the `θ`-power multiplicity
`k = 1 → 0`. -/
theorem expCase_residual_eq :
    cisZeroG (csubG expD [qxOfNum [-1/2]]) = true := by native_decide

end DeepWiki.SymbolicIntegration
