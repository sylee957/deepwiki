import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalCase2
import DeepWiki.SymbolicIntegration.Computable.Integrate
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.FuelFreeResultant

/-! # Log-part residues of algebraic-function integrals

The residue resultant `R(Z) = res_X(res_Y(Z·D' − g, F), D)` for the simple radical `F = y² − ρ`:
with `g = g₀ + g₁·y` linear in `y`, the inner resultant collapses to the norm `(Z·D' − g₀)² − g₁²·ρ`,
computed by evaluation + interpolation over the constant field `K`. Includes the residue-membership
test and the integer-residue certificate. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The `n = 2` residue resultant `R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` -/

/-- Inner residue norm at a node: `cAlgResidueNorm Dprime rho g0 g1 c = (c·D' − g₀)² − g₁²·ρ ∈ K[X]`,
the `resultant_Y(Z·D' − g, y² − ρ)` for `g = g₀ + g₁·y`, evaluated at `Z = c`. -/
def cAlgResidueNorm (Dprime rho g0 g1 : CPolyG α) (c : α) : CPolyG α :=
  let zg0 := csubG (cscaleG c Dprime) g0                  -- `c·D' − g₀`
  csubG (cmulG zg0 zg0) (cmulG (cmulG g1 g1) rho)         -- `(c·D' − g₀)² − g₁²·ρ`

/-- The `n = 2` algebraic-residue resultant `cAlgResidueResultant D rho g0 g1 = R(Z) ∈ K[Z]`,
`R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` for `y² = ρ` and numerator `g = g₀ + g₁·y`. Computed by
evaluation at `2·deg D + 1` nodes plus Lagrange interpolation (`cinterpolateG`). -/
def cAlgResidueResultant (D rho g0 g1 : CPolyG α) : CPolyG α :=
  let Dprime := cderivG D
  let nNodes := 2 * cdegG D + 1                          -- `deg_Z R ≤ 2·deg_X D`
  let pts : List (α × α) := (List.range (nNodes + 1)).map (fun k =>
    let c : α := cnatCastG k
    (c, cresultantWf (cAlgResidueNorm Dprime rho g0 g1 c) D))
  cinterpolateG pts

/-! ### Residue membership and the integer-residue failure-test certificate -/

/-- Residue membership test `cIsResidue R c = ((Z − c) ∣ R)`: whether `c` is a root of `R(Z)`, via
`cmodWf R (Z − c) = 0`. -/
def cIsResidue (R : CPolyG α) (c : α) : Bool :=
  cisZeroG (cmodWf R [CField.neg c, CField.one])          -- `R mod (Z − c) = 0`

/-- Residue-factorization certificate `cResiduesMatch R factors`: whether `R(Z)` equals `∏ (Z − cᵢ)`
up to a `K`-scalar (repetition encoding multiplicity), via `cisZeroG` of the monic difference. -/
def cResiduesMatch (R : CPolyG α) (factors : List α) : Bool :=
  let prod := factors.foldl (fun acc c => cmulG acc [CField.neg c, CField.one]) [CField.one]
  cisZeroG (csubG (cmonicG R) (cmonicG prod))

end CPolyG

/-! ### Validation: `∫ dx / ((x − 1)·y)` on `y² = x`

The integrand rationalizes to `y/(x² − x)`: numerator `g(x,y) = y` (`g₀ = 0, g₁ = 1`), denominator
`D(x) = x² − x`. -/

open CPolyG

/-- Validation radicand `ρ = x` (curve `y² = x`), as a `ℚ[x]` polynomial `[0, 1]`. -/
def algResExX_rho : CPolyG ℚ := [0, 1]

/-- Validation denominator `D = x² − x = x(x − 1)` (its roots `x = 0, 1` carry the poles/branch place),
`ℚ[x]` `[0, -1, 1]`. -/
def algResExX_D : CPolyG ℚ := [0, -1, 1]

/-- Validation numerator low part `g₀ = 0` (`g(x,y) = y` has no `y⁰` part). -/
def algResExX_g0 : CPolyG ℚ := []

/-- Validation numerator `y`-coefficient `g₁ = 1` (`g(x,y) = y`), `ℚ[x]` `[1]`. -/
def algResExX_g1 : CPolyG ℚ := [1]

/-- The computed residue resultant `R(Z)` for `∫ dx/((x−1)√x)`. -/
def algResExX_R : CPolyG ℚ := cAlgResidueResultant algResExX_D algResExX_rho algResExX_g0 algResExX_g1

/-- The expected monic residue resultant `R(Z) = Z⁴ − Z² = Z²(Z − 1)(Z + 1)` (`[0, 0, -1, 0, 1]`):
residues `Z = ±1` and `Z = 0` of multiplicity `2`. -/
def algResExX_expected : CPolyG ℚ := [0, 0, -1, 0, 1]

/-- `cAlgResidueResultant` on `∫ dx/((x − 1)·y)` over `y² = x` produces
`R(Z) = Z⁴ − Z² = Z²(Z − 1)(Z + 1)`, checked by `cisZeroG` of the difference over `ℚ[Z]`. -/
theorem algResExX_resultant_eq :
    cisZeroG (csubG algResExX_R algResExX_expected) = true := by native_decide

/-- The residues `±1` (and the branch-place `0`) are roots of `R`: `cIsResidue R (1) = cIsResidue R
(-1) = cIsResidue R (0) = true`, so `Z = ±1, 0` divide `R(Z) = Z²(Z − 1)(Z + 1)`. -/
theorem algResExX_residues_pm_one :
    cIsResidue algResExX_R (1 : ℚ) = true
    ∧ cIsResidue algResExX_R (-1 : ℚ) = true
    ∧ cIsResidue algResExX_R (0 : ℚ) = true := by native_decide

/-- `Z = 2` is not a residue: `cIsResidue R 2 = false` (`R(2) = 12 ≠ 0`). -/
theorem algResExX_two_not_residue :
    cIsResidue algResExX_R (2 : ℚ) = false := by native_decide

/-- All residues are integers: `R(Z) = Z·Z·(Z − 1)·(Z + 1)` factors into integer linear factors, so
`cResiduesMatch R [0, 0, 1, -1] = true` — the integrand passes the "all residues are integers"
elementarity test. -/
theorem algResExX_all_residues_integer :
    cResiduesMatch algResExX_R [0, 0, 1, -1] = true := by native_decide

/-- Restatement: the `n = 2` residue resultant of `∫ dx/((x − 1)·y)` on `y² = x` is `Z⁴ − Z²`, whose
nonzero roots `±1` are the residues — computed over the constant field ℚ alone. -/
example : cisZeroG (csubG
    (cAlgResidueResultant algResExX_D algResExX_rho algResExX_g0 algResExX_g1)
    [0, 0, -1, 0, 1]) = true := by native_decide

#print axioms algResExX_resultant_eq
#print axioms algResExX_all_residues_integer

end DeepWiki.SymbolicIntegration
