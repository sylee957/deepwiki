import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension

/-! # Case 2 rational-part example with `θ' = 1`

Concrete `native_decide` checks for `∫ C/(W²y)` with `y = √(x³−x)`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly

/-! #### Case 2 validates: `∫ C/(W²y)` with `y = √(x³−x)`, `W = x`

Radicand `y² = f = x³ − x`, squarefree factor `W = x`, `h = f/W = x² − 1`, `k = 2`, `C = 1` (integrand
`1/(x²√(x³−x))`): the congruence gives `B = 2/3` and residual `D = −x/3`, dropping the multiplicity
`k = 2 → 1`. -/

/-- Case-2 example radicand `f = x³ − x = x(x−1)(x+1)` (`y² = f`, squarefree), `ℚ[x]` `[0,−1,0,1]`. -/
def case2F : CPoly ℚ := [0, -1, 0, 1]

/-- Case-2 example squarefree denominator factor `W = x` (a factor of `f`, a branch place), `[0, 1]`. -/
def case2W : CPoly ℚ := [0, 1]

/-- Case-2 example cofactor `h = f/W = x² − 1`, `[−1, 0, 1]`. -/
def case2H : CPoly ℚ := [-1, 0, 1]

/-- Case-2 example numerator `C = 1`, `[1]`. -/
def case2C : CPoly ℚ := [1]

/-- `W' = x' = 1` over `ℚ[x]` (`cderiv`, `θ' = 1`). -/
def case2Wder : CPoly ℚ := cderiv case2W

/-- The solved Case-2 cofactor `B` for `B·(½−2)·W'·h ≡ 1 (mod x)` — expected `B = 2/3`. -/
def case2B : CPoly ℚ := radCase2Cofactor 2 case2W case2H case2C

/-- The Case-2 residual `D` — expected `−x/3` (multiplicity dropped `k = 2 → 1`). -/
def case2D : CPoly ℚ :=
  radCase2Residual 2 case2W case2H case2C case2B

/-- The cofactor is `B = 2/3`: `B·(½−2)·W'·h ≡ 1 (mod x)` gives `B = 2/3`. -/
theorem case2_cofactor_eq :
    cisZero (csub case2B [(2/3 : ℚ)]) = true := by native_decide

/-- The Case-2 congruence `B·(½−k)·W'·h − C ≡ 0 (mod W)` holds: `cmodWf (B·(½−k)W'h − C) W` vanishes. -/
theorem case2_congruence :
    cisZero (cmodWf
      (csub (cmul case2B
        (cmul (csub [CField.div CField.one (cnatCast 2)] [cnatCast 2])
          (cmul case2Wder case2H))) case2C)
      case2W) = true := by native_decide

/-- The Case-2 cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D` in `ℚ[x]` (`B = 2/3`, `D = −x/3`). -/
theorem case2_cleared_identity :
    cisZero (csub
      (cadd
        (csub (cmul case2B
          (cmul (csub [CField.div CField.one (cnatCast 2)] [cnatCast 2])
            (cmul case2Wder case2H))) case2C)
        (cmul case2W
          (cadd (cmul (cderiv case2B) case2H)
            (cmul [CField.div CField.one (cnatCast 2)] (cmul case2B (cderiv case2H))))))
      (cmul case2W case2D)) = true := by native_decide

/-- The residual `D = −x/3`, so the Case-2 step lowered the multiplicity of `W = x` from `k = 2` to `1`. -/
theorem case2_residual_eq :
    cisZero (csub case2D [(0 : ℚ), -1/3]) = true := by native_decide

end DeepWiki.SymbolicIntegration
