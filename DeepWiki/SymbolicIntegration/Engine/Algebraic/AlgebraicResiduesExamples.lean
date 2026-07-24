import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicResidues

/-! # Algebraic-residue examples

Executable checks for the `n = 2` residue resultant on `y² = x`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-! ### Validation: `∫ dx / ((x − 1)·y)` on `y² = x` -/

/-- Validation radicand `ρ = x` (curve `y² = x`). -/
def algResExX_rho : DensePoly ℚ := [0, 1]

/-- Validation denominator `D = x² − x = x(x − 1)`. -/
def algResExX_D : DensePoly ℚ := [0, -1, 1]

/-- Validation numerator low part `g₀ = 0`. -/
def algResExX_g0 : DensePoly ℚ := []

/-- Validation numerator `y`-coefficient `g₁ = 1`. -/
def algResExX_g1 : DensePoly ℚ := [1]

/-- The computed residue resultant `R(Z)` for `∫ dx/((x−1)√x)`. -/
def algResExX_R : DensePoly ℚ := cAlgResidueResultant algResExX_D algResExX_rho algResExX_g0 algResExX_g1

/-- The expected monic residue resultant `R(Z) = Z⁴ − Z²`. -/
def algResExX_expected : DensePoly ℚ := [0, 0, -1, 0, 1]

/-- `cAlgResidueResultant` on `∫ dx/((x − 1)·y)` over `y² = x` produces `Z⁴ − Z²`. -/
theorem algResExX_resultant_eq :
    cisZero (csub algResExX_R algResExX_expected) = true := by native_decide

/-- The residues `±1` and branch-place root `0` are roots of the computed resultant. -/
theorem algResExX_residues_pm_one :
    CPoly.isRoot algResExX_R (1 : ℚ) = true
    ∧ CPoly.isRoot algResExX_R (-1 : ℚ) = true
    ∧ CPoly.isRoot algResExX_R (0 : ℚ) = true := by native_decide

/-- `Z = 2` is not a residue of `∫ dx/((x − 1)·y)` on `y² = x`. -/
theorem algResExX_two_not_residue :
    CPoly.isRoot algResExX_R (2 : ℚ) = false := by native_decide

/-- All residues in the `y² = x` example are integers. -/
theorem algResExX_all_residues_integer :
    CPoly.matchesLinearFactors algResExX_R [0, 0, 1, -1] = true := by native_decide

#print axioms algResExX_resultant_eq
#print axioms algResExX_all_residues_integer

end DeepWiki.SymbolicIntegration
