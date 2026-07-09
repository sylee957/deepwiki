import DeepWiki.SymbolicIntegration.Engine.Hyperexp.LaurentCore
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.Eta
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Core hyperexponential normal-part drivers

The residual-feedback normal and full hyperexponential integration drivers.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration


namespace CPoly

/-! ### The hyperexponential residual `R = η · ∑ᵢ cᵢ`

For a hyperexponential `t` (`Dt = η·t`), the log part `∑ᵢ cᵢ·log(vᵢ)` of a normal part `fₙ` overshoots by
`R = η · ∑ᵢ cᵢ ∈ α`. -/

variable {α : Type*} [CField α]

/-- Hyperexponential normal-part residual `cHyperexpResidualG η logs = η · ∑ᵢ cᵢ ∈ α`, the amount by which
the log part overshoots the normal integrand (`cᵢ` the `logs` coefficients). -/
def cHyperexpResidualG (η : α) (logs : List (α × CPoly α)) : α :=
  CField.mul η (logs.foldl (fun acc cv => CField.add acc cv.1) CField.zero)

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-! ### The normal-part integrator `∫ fₙ = logPart − ∫R`

`cIntegrateHyperexpNormalG` runs the reduced integrator, reads the residual `R`, integrates `∫R` over the
base, and subtracts it. -/

/-- Hyperexponential normal-part integral `cIntegrateHyperexpNormalG Dt a d cands`: run
`cIntegrateReducedG`, read `R = η·∑ᵢ cᵢ`, integrate `∫R` by `crischDESolve 0 R`, and subtract it from the
rational part (same logs); `none` if `∫R` is non-elementary. -/
def cIntegrateHyperexpNormalG (Dt : CPoly α) (a d : CPoly α) (cands : List α) :
    Option (IntegralResultG α) :=
  let red := cIntegrateReducedG Dt a d cands
  let η : α := cExpEtaG Dt
  let R : α := cHyperexpResidualG η red.logs
  match CRischField.crischDESolve (CField.zero : α) R with
  | none => none
  | some intR =>
    let (gnum, gden) := red.rational
    let newNum := csubG gnum (cmulG [intR] gden)
    some ⟨(newNum, gden), red.logs⟩

/-- Full hyperexponential integral `cIntegrateHyperexpFullG Dt a d cands`: canonical-split
`f = fₚ + (b/dₛ) + (cₙ/dₙ)`, integrate the Laurent part by `cIntegrateHyperexpLaurentG` and the normal part
by `cIntegrateHyperexpNormalG`, and combine the rational parts; `none` if either is non-elementary. -/
def cIntegrateHyperexpFullG (Dt : CPoly α) (a d : CPoly α) (cands : List α) :
    Option (IntegralResultG α) :=
  let η : α := cExpEtaG Dt
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastG Dt a d
  let neg : List α := cHyperexpSpecialNegG b ds
  match cIntegrateHyperexpLaurentG η fp neg with
  | none => none
  | some (lnum, lden) =>
    match cIntegrateHyperexpNormalG Dt cn dn cands with
    | none => none
    | some nrm =>
      let (gnum, gden) := nrm.rational
      let num := caddG (cmulG lnum gden) (cmulG gnum lden)
      let den := cmulG lden gden
      some ⟨(num, den), nrm.logs⟩

end CPoly

end DeepWiki.SymbolicIntegration
