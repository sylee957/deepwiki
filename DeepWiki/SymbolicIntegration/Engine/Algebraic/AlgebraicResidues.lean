import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalCase2
import DeepWiki.ComputableAlgebra.PolyGcdAlgorithms
import DeepWiki.ComputableAlgebra.PolyReprDense
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # Log-part residues of algebraic-function integrals

The residue resultant `R(Z) = res_X(res_Y(Z·D' − g, F), D)` for the simple radical `F = y² − ρ`:
with `g = g₀ + g₁·y` linear in `y`, the inner resultant collapses to the norm `(Z·D' − g₀)² − g₁²·ρ`,
computed by evaluation + interpolation over the constant field `K`. Includes the residue-membership
test and the integer-residue certificate. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### The `n = 2` residue resultant `R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` -/

/-- Inner residue norm at a node: `cAlgResidueNorm Dprime rho g0 g1 c = (c·D' − g₀)² − g₁²·ρ ∈ K[X]`,
the `resultant_Y(Z·D' − g, y² − ρ)` for `g = g₀ + g₁·y`, evaluated at `Z = c`. -/
def cAlgResidueNorm {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (Dprime rho g0 g1 : P α) (c : α) : P α :=
  let zg0 := CPolyEngine.sub (CPolyEngine.scale c Dprime) g0       -- `c·D' − g₀`
  CPolyEngine.sub (CPolyEngine.mul zg0 zg0)
    (CPolyEngine.mul (CPolyEngine.mul g1 g1) rho)                  -- `(c·D' − g₀)² − g₁²·ρ`

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let N := cAlgResidueNorm (ofList [1]) (ofList [0, 1]) (ofList [0]) (ofList [1]) 2
    CPoly.coeff N 0 = 4 ∧ CPoly.coeff N 1 = -1 := by
  native_decide

/-- The `n = 2` algebraic-residue resultant `cAlgResidueResultant D rho g0 g1 = R(Z) ∈ K[Z]`,
`R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` for `y² = ρ` and numerator `g = g₀ + g₁·y`. Computed by
evaluation at `2·deg D + 1` nodes plus Lagrange interpolation (`cinterpolate`). -/
def cAlgResidueResultant [CPolyResultant DensePoly]
    (D rho g0 g1 : DensePoly α) : DensePoly α :=
  let Dprime := cderiv D
  let nNodes := 2 * cdeg D + 1                          -- `deg_Z R ≤ 2·deg_X D`
  let pts : List (α × α) := (List.range (nNodes + 1)).map (fun k =>
    let c : α := CField.natCast k
    (c, CPolyResultant.compute (cAlgResidueNorm Dprime rho g0 g1 c) D))
  cinterpolate pts

/-! ### Residue membership and the integer-residue failure-test certificate -/

example :
    CPoly.isRoot (CPoly.SparsePoly.ofList [(0, -1), (1, 1)] : CPoly.SparsePoly ℚ) 1 = true := by
  ccompute

end DensePoly

end DeepWiki.SymbolicIntegration
