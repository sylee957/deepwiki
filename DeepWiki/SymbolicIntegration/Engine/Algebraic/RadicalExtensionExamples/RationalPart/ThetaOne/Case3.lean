import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension

/-! # Case 3 rational-part example with `θ' = 1`

Concrete `native_decide` checks for degree lowering in `∫ (x²+x)/√x`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-! #### Case 3 validates: degree-lowering `∫ (x²+x)/√x` with `y = √x`

Radicand `y² = f = x`, `g = 1/2`, `C = x² + x`: the leading-coefficient solve gives `B = (2/5)x²` and
residual `D = −x` of degree `1 < deg C = 2`, lowering `deg C` by one. -/

/-- Case-3 example radicand `f = x` (`y² = x`, `m = deg f = 1`), as a `ℚ[x]` polynomial `[0, 1]`. -/
def case3F : CPolyG ℚ := [0, 1]

/-- `g = ((n−1)/n)·f' = (1/2)·1 = 1/2` for `n = 2`, `f = x` (`(f/y)' = g/y`, `lcf(g) = 1/2`), `[1/2]`. -/
def case3G : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG case3F)

/-- Case-3 example numerator `C = x² + x` (`deg C = 2 ≥ m = 1`), `[0, 1, 1]`. -/
def case3C : CPolyG ℚ := [0, 1, 1]

/-- The solved Case-3 leading-coefficient cofactor `B = (2/5)x²` (`j+1 = 2`, `b = 1/(2+1/2) = 2/5`). -/
def case3B : CPolyG ℚ := radCase3Cofactor case3F case3G case3C

/-- The Case-3 residual `D = B'f + Bg − C` — expected `−x` (degree `1 < deg C = 2`). -/
def case3D : CPolyG ℚ := radCase3Residual case3F case3G case3B case3C (cderivG case3B)

/-- The cofactor is `B = (2/5)x²`: `b = lcf(C)/((j+1)+lcf(g)) = 1/(2+1/2) = 2/5` at degree `j+1 = 2`. -/
theorem case3_cofactor_eq :
    cisZeroG (csubG case3B [(0 : ℚ), 0, 2/5]) = true := by native_decide

/-- The Case-3 cleared identity `B'f + Bg − C = D` in `ℚ[x]` (`B = (2/5)x²`, `D = −x`). -/
theorem case3_cleared_identity :
    cisZeroG (csubG
      (csubG (caddG (cmulG (cderivG case3B) case3F) (cmulG case3B case3G)) case3C)
      case3D) = true := by native_decide

/-- The residual `D = −x` has degree `1`, strictly below `deg C = 2`. -/
theorem case3_residual_eq :
    cisZeroG (csubG case3D [(0 : ℚ), -1]) = true := by native_decide

/-- The Case-3 step strictly lowers `deg C`: `deg D = 1 < deg C = 2`. -/
theorem case3_degree_drop : cdegG case3D < cdegG case3C := by native_decide

end DeepWiki.SymbolicIntegration
