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

/-- Hyperexponential normal-part residual `cHyperexpResidual η logs = η · ∑ᵢ cᵢ ∈ α`, the amount by which
the log part overshoots the normal integrand (`cᵢ` the `logs` coefficients). -/
def cHyperexpResidual (η : α) (logs : List (α × CPoly α)) : α :=
  CField.mul η (logs.foldl (fun acc cv => CField.add acc cv.1) CField.zero)

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-! ### The normal-part integrator `∫ fₙ = logPart − ∫R`

`cIntegrateHyperexpNormal` runs the reduced integrator, reads the residual `R`, integrates `∫R` over the
base, and subtracts it. -/

/-- Hyperexponential normal-part integral `cIntegrateHyperexpNormal Dt a d cands`: run
`cIntegrateReduced`, read `R = η·∑ᵢ cᵢ`, integrate `∫R` by `crischDESolve 0 R`, and subtract it from the
rational part (same logs); `none` if `∫R` is non-elementary. -/
def cIntegrateHyperexpNormal (Dt : CPoly α) (a d : CPoly α) (cands : List α) :
    Option (IntegralResultG α) :=
  let red := cIntegrateReduced Dt a d cands
  let η : α := cExpEta Dt
  let R : α := cHyperexpResidual η red.logs
  match CRischField.crischDESolve (CField.zero : α) R with
  | none => none
  | some intR =>
    let (gnum, gden) := red.rational
    let newNum := csub gnum (cmul [intR] gden)
    some ⟨(newNum, gden), red.logs⟩

/-- Full hyperexponential integral `cIntegrateHyperexpFull Dt a d cands`: canonical-split
`f = fₚ + (b/dₛ) + (cₙ/dₙ)`, integrate the Laurent part by `cIntegrateHyperexpLaurent` and the normal part
by `cIntegrateHyperexpNormal`, and combine the rational parts; `none` if either is non-elementary. -/
def cIntegrateHyperexpFull (Dt : CPoly α) (a d : CPoly α) (cands : List α) :
    Option (IntegralResultG α) :=
  let η : α := cExpEta Dt
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFast Dt a d
  let neg : List α := cHyperexpSpecialNeg b ds
  match cIntegrateHyperexpLaurent η fp neg with
  | none => none
  | some (lnum, lden) =>
    match cIntegrateHyperexpNormal Dt cn dn cands with
    | none => none
    | some nrm =>
      let (gnum, gden) := nrm.rational
      let num := cadd (cmul lnum gden) (cmul gnum lden)
      let den := cmul lden gden
      some ⟨(num, den), nrm.logs⟩

end CPoly

end DeepWiki.SymbolicIntegration
