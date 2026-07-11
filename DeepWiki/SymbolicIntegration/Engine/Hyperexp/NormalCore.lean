import DeepWiki.SymbolicIntegration.Engine.Hyperexp.LaurentCore
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.Eta
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Core hyperexponential normal-part drivers

The residual-feedback normal and full hyperexponential integration drivers.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

namespace DensePoly

/-! ### The hyperexponential residual `R = η · ∑ᵢ cᵢ`

For a hyperexponential `t` (`Dt = η·t`), the log part `∑ᵢ cᵢ·log(vᵢ)` of a normal part `fₙ` overshoots by
`R = η · ∑ᵢ cᵢ ∈ α`. -/

variable {α : Type*} [CCommRing α]

/-- Hyperexponential normal-part residual `cHyperexpResidual η logs = η · ∑ᵢ cᵢ ∈ α`, the amount by which
the log part overshoots the normal integrand (`cᵢ` the `logs` coefficients). -/
def cHyperexpResidual {γ : Type*} (η : α) (logs : List (α × γ)) : α :=
  CCommRing.mul η (logs.foldl (fun acc cv => CCommRing.add acc cv.1) CCommRing.zero)

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
  {α : Type u} [CField α] [CRischField α]

/-- Correct a hyperexponential reduced result by integrating and subtracting its scalar residual. -/
def cCorrectHyperexpNormal (η : α) (red : IntegralResult α P) : Option (IntegralResult α P) :=
  let R : α := cHyperexpResidual η red.logs
  match CRischField.crischDESolve (CCommRing.zero : α) R with
  | none => none
  | some intR =>
    let (gnum, gden) := red.rational
    let intRPoly : P α := CPolyEngine.ofCoeffList [intR]
    let newNum := CPolyEngine.sub gnum (CPolyEngine.mul intRPoly gden)
    some ⟨(newNum, gden), red.logs⟩

/-- Hyperexponential residual correction executes on sparse polynomial results. -/
example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let red : IntegralResult ℚ CPoly.SparsePoly := ⟨(ofList [1], ofList [1]), []⟩
    (cCorrectHyperexpNormal (0 : ℚ) red).isSome = true := by
  native_decide

variable {α : Type*} [CField α] [CDiffField α]
  [CPolyGcd DensePoly α] [CPolySquarefree DensePoly α]
  [CPolyResultant DensePoly] [CRischField α]

/-! ### The normal-part integrator `∫ fₙ = logPart − ∫R`

`cIntegrateHyperexpNormal` runs the reduced integrator, reads the residual `R`, integrates `∫R` over the
base, and subtracts it. -/

/-- Hyperexponential normal-part integral `cIntegrateHyperexpNormal Dt a d cands`: run
`cIntegrateReduced`, read `R = η·∑ᵢ cᵢ`, integrate `∫R` by `crischDESolve 0 R`, and subtract it from the
rational part (same logs); `none` if `∫R` is non-elementary. -/
def cIntegrateHyperexpNormal (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) :
    Option (IntegralResult α) :=
  let red := cIntegrateReduced Dt a d cands
  cCorrectHyperexpNormal (cExpEta Dt) red

variable [CPolySplitFactor DensePoly α]

/-- Full hyperexponential integral `cIntegrateHyperexpFull Dt a d cands`: canonical-split
`f = fₚ + (b/dₛ) + (cₙ/dₙ)`, integrate the Laurent part by `cIntegrateHyperexpLaurent` and the normal part
by `cIntegrateHyperexpNormal`, and combine the rational parts; `none` if either is non-elementary. -/
def cIntegrateHyperexpFull (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) :
    Option (IntegralResult α) :=
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

end DensePoly

end DeepWiki.SymbolicIntegration
