import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFF.Carrier

/-! # Denominator clearing for fraction-free tower gcd benchmarks

Conversion between `QFunNZ` coefficient polynomials and the bivariate `GBPoly`
carrier.
-/

namespace DeepWiki.SymbolicIntegration

/-! ### Clear denominators `CPoly (QFunNZ β) ↔ GBPoly β` (`β(s)[t] ↔ (β[s])[t]`) -/

namespace CPoly

variable {β : Type*} [CField β] [CFieldDomain β]

/-- The numerator `CPoly β` of a `QFunNZ β` coefficient. -/
def qnumCoeff (c : QFunNZ β) : CPoly β := c.1.1

/-- The denominator `CPoly β` of a `QFunNZ β` coefficient. -/
def qdenCoeff (c : QFunNZ β) : CPoly β := c.1.2

/-- Clear denominators `cclearDenoms p ∈ GBPoly β`: multiply `p` over `α = QFunNZ β` by the product of
its coefficient denominators, so coefficient `i` becomes `numᵢ · ∏_{j≠i} denⱼ ∈ CPoly β`. -/
def cclearDenoms (p : CPoly (QFunNZ β)) : GBPoly β :=
  let cs : List (QFunNZ β) := p
  let dens : List (CPoly β) := cs.map qdenCoeff
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => CPoly.cmul acc d) [CField.one]
    CPoly.cmul (qnumCoeff ci) prodOthers)

/-- Lift back `liftGBPoly p ∈ CPoly (QFunNZ β)`: read each `CPoly β` coefficient `c` as the fraction
`c/1`. Inverse of clearing denominators. -/
def liftGBPoly (p : GBPoly β) : CPoly (QFunNZ β) :=
  p.map (fun c => (⟨(c, [CField.one]), QFunNZ.cisZeroG_one_singleton⟩ : QFunNZ β))

end CPoly

end DeepWiki.SymbolicIntegration
