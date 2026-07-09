import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFF.Carrier

/-! # Denominator clearing for fraction-free tower gcd benchmarks

Conversion between `QFunNZG` coefficient polynomials and the bivariate `GBPoly`
carrier.
-/

namespace DeepWiki.SymbolicIntegration

/-! ### Clear denominators `CPolyG (QFunNZG β) ↔ GBPoly β` (`β(s)[t] ↔ (β[s])[t]`) -/

namespace CPolyG

variable {β : Type*} [CField β] [CFieldDomain β]

/-- The numerator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qnumCoeffG (c : QFunNZG β) : CPolyG β := c.1.1

/-- The denominator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qdenCoeffG (c : QFunNZG β) : CPolyG β := c.1.2

/-- Clear denominators `cclearDenomsG p ∈ GBPoly β`: multiply `p` over `α = QFunNZG β` by the product of
its coefficient denominators, so coefficient `i` becomes `numᵢ · ∏_{j≠i} denⱼ ∈ CPolyG β`. -/
def cclearDenomsG (p : CPolyG (QFunNZG β)) : GBPoly β :=
  let cs : List (QFunNZG β) := p
  let dens : List (CPolyG β) := cs.map qdenCoeffG
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => CPolyG.cmulG acc d) [CField.one]
    CPolyG.cmulG (qnumCoeffG ci) prodOthers)

/-- Lift back `liftGBPolyG p ∈ CPolyG (QFunNZG β)`: read each `CPolyG β` coefficient `c` as the fraction
`c/1`. Inverse of clearing denominators. -/
def liftGBPolyG (p : GBPoly β) : CPolyG (QFunNZG β) :=
  p.map (fun c => (⟨(c, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩ : QFunNZG β))

end CPolyG

end DeepWiki.SymbolicIntegration
