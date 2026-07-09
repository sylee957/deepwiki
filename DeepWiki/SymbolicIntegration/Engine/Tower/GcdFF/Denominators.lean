import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFF.Carrier

/-! # Denominator clearing for fraction-free tower gcd benchmarks

Conversion between `QFunNZG` coefficient polynomials and the bivariate `GBPoly`
carrier.
-/

namespace DeepWiki.SymbolicIntegration

/-! ### Clear denominators `CPoly (QFunNZG β) ↔ GBPoly β` (`β(s)[t] ↔ (β[s])[t]`) -/

namespace CPoly

variable {β : Type*} [CField β] [CFieldDomain β]

/-- The numerator `CPoly β` of a `QFunNZG β` coefficient. -/
def qnumCoeffG (c : QFunNZG β) : CPoly β := c.1.1

/-- The denominator `CPoly β` of a `QFunNZG β` coefficient. -/
def qdenCoeffG (c : QFunNZG β) : CPoly β := c.1.2

/-- Clear denominators `cclearDenomsG p ∈ GBPoly β`: multiply `p` over `α = QFunNZG β` by the product of
its coefficient denominators, so coefficient `i` becomes `numᵢ · ∏_{j≠i} denⱼ ∈ CPoly β`. -/
def cclearDenomsG (p : CPoly (QFunNZG β)) : GBPoly β :=
  let cs : List (QFunNZG β) := p
  let dens : List (CPoly β) := cs.map qdenCoeffG
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => CPoly.cmulG acc d) [CField.one]
    CPoly.cmulG (qnumCoeffG ci) prodOthers)

/-- Lift back `liftGBPolyG p ∈ CPoly (QFunNZG β)`: read each `CPoly β` coefficient `c` as the fraction
`c/1`. Inverse of clearing denominators. -/
def liftGBPolyG (p : GBPoly β) : CPoly (QFunNZG β) :=
  p.map (fun c => (⟨(c, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩ : QFunNZG β))

end CPoly

end DeepWiki.SymbolicIntegration
