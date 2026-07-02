import DeepWiki.SymbolicIntegration.ComputableHyperexpLaurentCore
import DeepWiki.SymbolicIntegration.ComputableHyperexpEta
import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded

/-! # Core hyperexponential normal-part drivers

The residual-feedback normal and full hyperexponential integration drivers
(`cIntegrateHyperexpNormalGWf` / `cIntegrateHyperexpFullGWf`), separated from the concrete examples.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

/-! ### The hyperexponential residual `R = η · ∑ᵢ cᵢ`

For a hyperexponential `t` (`Dt = η·t`), the Rothstein–Trager logarithmic construction
`∑ᵢ cᵢ·log(vᵢ)` of a normal part `fₙ` has derivative `fₙ + R` with the residual
`R = η · ∑ᵢ cᵢ ∈ α` — a constant in `t`, a base-field element. -/

variable {α : Type*} [CField α]

/-- Hyperexponential normal-part residual `cHyperexpResidualG η logs = η · ∑ᵢ cᵢ ∈ α`: the residual
`R` by which the Rothstein–Trager log part `∑ᵢ cᵢ·log(vᵢ)` overshoots the normal integrand on a
hyperexponential monomial (`η = Dt/t`, `cᵢ` the `logs` coefficients). A constant in `t`, hence a
base-field element. -/
def cHyperexpResidualG (η : α) (logs : List (α × CPolyG α)) : α :=
  CField.mul η (logs.foldl (fun acc cv => CField.add acc cv.1) CField.zero)

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-! ### The normal-part integrator `∫ fₙ = logPart − ∫R`

`cIntegrateHyperexpNormalGWf` integrates a normal part `fₙ = a/d` of a hyperexponential monomial by
running the reduced capstone, reading the residual `R = η·∑res`, integrating the base residual
`∫R` over `α` by `CRischField.crischDESolve 0 R`, and subtracting `∫R` from the rational part. -/

/-- Hyperexponential normal-part integral `cIntegrateHyperexpNormalGWf Dt a d cands`: run
`cIntegrateReducedGWf`, read the residual `R = η·∑ᵢ cᵢ`, integrate `∫R` over the base by
`crischDESolve 0 R`, and subtract `∫R` from the rational part (same logs); `none` if `∫R` is
non-elementary. -/
def cIntegrateHyperexpNormalGWf (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let red := cIntegrateReducedGWf Dt a d cands
  let η : α := cExpEtaG Dt
  let R : α := cHyperexpResidualG η red.logs
  match CRischField.crischDESolve (CField.zero : α) R with
  | none => none
  | some intR =>
    let (gnum, gden) := red.rational
    let newNum := csubG gnum (cmulG [intR] gden)
    some ⟨(newNum, gden), red.logs⟩

/-- Full hyperexponential integral with normal feedback `cIntegrateHyperexpFullGWf Dt a d cands`:
canonical-split `f = fₚ + (b/dₛ) + (cₙ/dₙ)`, integrate the Laurent part `fₚ + b/dₛ` by
`cIntegrateHyperexpLaurentG`, the normal part by `cIntegrateHyperexpNormalGWf`, and combine the
rational parts; `none` if either step is non-elementary. -/
def cIntegrateHyperexpFullGWf (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let η : α := cExpEtaG Dt
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d
  let neg : List α := cHyperexpSpecialNegG b ds
  match cIntegrateHyperexpLaurentG η fp neg with
  | none => none
  | some (lnum, lden) =>
    match cIntegrateHyperexpNormalGWf Dt cn dn cands with
    | none => none
    | some nrm =>
      let (gnum, gden) := nrm.rational
      let num := caddG (cmulG lnum gden) (cmulG gnum lden)
      let den := cmulG lden gden
      some ⟨(num, den), nrm.logs⟩

end CPolyG

end DeepWiki.SymbolicIntegration
