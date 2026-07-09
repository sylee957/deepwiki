import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalCase2
import DeepWiki.ComputableAlgebra.Polynomial
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # Log-part residues of algebraic-function integrals

The residue resultant `R(Z) = res_X(res_Y(Z·D' − g, F), D)` for the simple radical `F = y² − ρ`:
with `g = g₀ + g₁·y` linear in `y`, the inner resultant collapses to the norm `(Z·D' − g₀)² − g₁²·ρ`,
computed by evaluation + interpolation over the constant field `K`. Includes the residue-membership
test and the integer-residue certificate. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### The `n = 2` residue resultant `R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` -/

/-- Inner residue norm at a node: `cAlgResidueNorm Dprime rho g0 g1 c = (c·D' − g₀)² − g₁²·ρ ∈ K[X]`,
the `resultant_Y(Z·D' − g, y² − ρ)` for `g = g₀ + g₁·y`, evaluated at `Z = c`. -/
def cAlgResidueNorm (Dprime rho g0 g1 : DensePoly α) (c : α) : DensePoly α :=
  let zg0 := csub (cscale c Dprime) g0                  -- `c·D' − g₀`
  csub (cmul zg0 zg0) (cmul (cmul g1 g1) rho)         -- `(c·D' − g₀)² − g₁²·ρ`

/-- The `n = 2` algebraic-residue resultant `cAlgResidueResultant D rho g0 g1 = R(Z) ∈ K[Z]`,
`R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` for `y² = ρ` and numerator `g = g₀ + g₁·y`. Computed by
evaluation at `2·deg D + 1` nodes plus Lagrange interpolation (`cinterpolate`). -/
def cAlgResidueResultant (D rho g0 g1 : DensePoly α) : DensePoly α :=
  let Dprime := cderiv D
  let nNodes := 2 * cdeg D + 1                          -- `deg_Z R ≤ 2·deg_X D`
  let pts : List (α × α) := (List.range (nNodes + 1)).map (fun k =>
    let c : α := cnatCast k
    (c, cresultantWf (cAlgResidueNorm Dprime rho g0 g1 c) D))
  cinterpolate pts

/-! ### Residue membership and the integer-residue failure-test certificate -/

/-- Residue membership test `cIsResidue R c = ((Z − c) ∣ R)`: whether `c` is a root of `R(Z)`, via
`cmodWf R (Z − c) = 0`. -/
def cIsResidue (R : DensePoly α) (c : α) : Bool :=
  cisZero (cmodWf R [CCommRing.neg c, CCommRing.one])          -- `R mod (Z − c) = 0`

/-- Residue-factorization certificate `cResiduesMatch R factors`: whether `R(Z)` equals `∏ (Z − cᵢ)`
up to a `K`-scalar (repetition encoding multiplicity), via `cisZero` of the monic difference. -/
def cResiduesMatch (R : DensePoly α) (factors : List α) : Bool :=
  let prod := factors.foldl (fun acc c => cmul acc [CCommRing.neg c, CCommRing.one]) [CCommRing.one]
  cisZero (csub (cmonic R) (cmonic prod))

end DensePoly

end DeepWiki.SymbolicIntegration
