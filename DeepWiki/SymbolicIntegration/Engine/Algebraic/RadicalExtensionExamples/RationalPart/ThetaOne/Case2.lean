import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension

/-! # Case 2 rational-part example with `θ' = 1`

Concrete `native_decide` checks for `∫ C/(W²y)` with `y = √(x³−x)`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-! #### Case 2 validates: `∫ C/(W²y)` with `y = √(x³−x)`, `W = x`

Radicand `y² = f = x³ − x`, squarefree factor `W = x`, `h = f/W = x² − 1`, `k = 2`, `C = 1` (integrand
`1/(x²√(x³−x))`): the congruence gives `B = 2/3` and residual `D = −x/3`, dropping the multiplicity
`k = 2 → 1`. -/

/-- Case-2 example radicand `f = x³ − x = x(x−1)(x+1)` (`y² = f`, squarefree), `ℚ[x]` `[0,−1,0,1]`. -/
def case2F : CPolyG ℚ := [0, -1, 0, 1]

/-- Case-2 example squarefree denominator factor `W = x` (a factor of `f`, a branch place), `[0, 1]`. -/
def case2W : CPolyG ℚ := [0, 1]

/-- Case-2 example cofactor `h = f/W = x² − 1`, `[−1, 0, 1]`. -/
def case2H : CPolyG ℚ := [-1, 0, 1]

/-- Case-2 example numerator `C = 1`, `[1]`. -/
def case2C : CPolyG ℚ := [1]

/-- `W' = x' = 1` over `ℚ[x]` (`cderivG`, `θ' = 1`). -/
def case2Wder : CPolyG ℚ := cderivG case2W

/-- The solved Case-2 cofactor `B` for `B·(½−2)·W'·h ≡ 1 (mod x)` — expected `B = 2/3`. -/
def case2B : CPolyG ℚ := radCase2Cofactor 2 case2W case2H case2C

/-- The Case-2 residual `D` — expected `−x/3` (multiplicity dropped `k = 2 → 1`). -/
def case2D : CPolyG ℚ :=
  radCase2Residual 2 case2W case2H case2C case2B

/-- The cofactor is `B = 2/3`: `B·(½−2)·W'·h ≡ 1 (mod x)` gives `B = 2/3`. -/
theorem case2_cofactor_eq :
    cisZeroG (csubG case2B [(2/3 : ℚ)]) = true := by native_decide

/-- The Case-2 congruence `B·(½−k)·W'·h − C ≡ 0 (mod W)` holds: `cmodWf (B·(½−k)W'h − C) W` vanishes. -/
theorem case2_congruence :
    cisZeroG (cmodWf
      (csubG (cmulG case2B
        (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
          (cmulG case2Wder case2H))) case2C)
      case2W) = true := by native_decide

/-- The Case-2 cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D` in `ℚ[x]` (`B = 2/3`, `D = −x/3`). -/
theorem case2_cleared_identity :
    cisZeroG (csubG
      (caddG
        (csubG (cmulG case2B
          (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
            (cmulG case2Wder case2H))) case2C)
        (cmulG case2W
          (caddG (cmulG (cderivG case2B) case2H)
            (cmulG [CField.div CField.one (cnatCastG 2)] (cmulG case2B (cderivG case2H))))))
      (cmulG case2W case2D)) = true := by native_decide

/-- The residual `D = −x/3`, so the Case-2 step lowered the multiplicity of `W = x` from `k = 2` to `1`. -/
theorem case2_residual_eq :
    cisZeroG (csubG case2D [(0 : ℚ), -1/3]) = true := by native_decide

end DeepWiki.SymbolicIntegration
