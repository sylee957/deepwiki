import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension

/-! # Case 1 rational-part example with `θ' = 1`

Concrete `native_decide` checks for `∫ C/(V²y)` with `y = √x`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! #### Case 1 validates: `∫ C/(V²y)` with `y = √x`, `V = x−1`

Radicand `y² = f = x`, `V = x − 1`, `k = 2`, `C = 1` (integrand `1/((x−1)²√x)`): the congruence gives
`B = −1` and residual `D = 1/2` (constant), dropping the multiplicity `2 → 1`; `g = f'/2 = 1/2`. -/

open DensePoly

/-- Case-1 example radicand `f = x` (`y² = x`, `y = √x`), as a `ℚ[x]` polynomial `[0, 1]`. -/
def case1F : DensePoly ℚ := [0, 1]

/-- Case-1 example squarefree denominator factor `V = x − 1` (coprime to `f = x`), `[−1, 1]`. -/
def case1V : DensePoly ℚ := [-1, 1]

/-- Case-1 example numerator `C = 1`, `[1]`. -/
def case1C : DensePoly ℚ := [1]

/-- `V' = (x−1)' = 1` over `ℚ[x]` (`cderiv`, `θ' = 1`, ℚ-constant coefficients). -/
def case1Vder : DensePoly ℚ := cderiv case1V

/-- `g = ((n−1)/n)·f' = (1/2)·1 = 1/2` for `n = 2`, `f = x` squarefree (`(f/y)' = g/y`), `[1/2]`. -/
def case1 : DensePoly ℚ := cscale (1/2 : ℚ) (cderiv case1F)

/-- The solved Case-1 cofactor `B` for `−x·B ≡ 1 (mod x−1)` — expected `B = −1`. -/
def case1B : DensePoly ℚ := CPoly.radCase1Cofactor 2 case1V case1Vder case1F case1C

/-- The Case-1 residual `D` — expected the constant `1/2`. -/
def case1D : DensePoly ℚ :=
  CPoly.radCase1Residual 2 case1V case1Vder case1F case1 case1B case1C (cderiv case1B)

/-- The cofactor is `B = −1`: `−x·B ≡ 1 (mod x−1)` gives `B = −1`. -/
theorem case1_cofactor_eq :
    cisZero (csub case1B [(-1 : ℚ)]) = true := by native_decide

/-- The Case-1 congruence `(1−k)V'fB − C ≡ 0 (mod V)` holds under the selected remainder. -/
theorem case1_congruence :
    cisZero (CPolyEuclidean.mod
      (csub (cmul (cneg [CField.natCast 1]) (cmul case1Vder (cmul case1F case1B))) case1C)
      case1V) = true := by native_decide

/-- The Case-1 cleared identity `(1−k)V'fB − C + V·(B'f + Bg) = V·D` in `ℚ[x]` (`B = −1`, `D = 1/2`). -/
theorem case1_cleared_identity :
    cisZero (csub
      (cadd
        (csub (cmul (cneg [CField.natCast 1]) (cmul case1Vder (cmul case1F case1B))) case1C)
        (cmul case1V (cadd (cmul (cderiv case1B) case1F) (cmul case1B case1))))
      (cmul case1V case1D)) = true := by native_decide

/-- The residual `D = 1/2` has degree `< deg V`, so the multiplicity dropped `k = 2 → 1`. -/
theorem case1_residual_eq :
    cisZero (csub case1D [(1/2 : ℚ)]) = true := by native_decide

end DeepWiki.SymbolicIntegration
