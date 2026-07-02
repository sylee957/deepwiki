import DeepWiki.SymbolicIntegration.ComputableHyperexpLaurentCore
import DeepWiki.SymbolicIntegration.ComputableHyperexpEta
import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded

/-! # Core fuel-free hyperexponential normal-part drivers

The §5.9 residual-feedback normal and full hyperexponential drivers, separated from the concrete
`native_decide` examples and from the fueled §5.10-only driver.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

/-! ### The hyperexponential residual `R = η · ∑ᵢ cᵢ` (Bronstein §5.9, the overshoot)

For a hyperexponential `t` (`Dt = η·t`), the §5.6 logarithmic construction `∑ᵢ cᵢ·log(vᵢ)` of a normal
part `fₙ` has derivative `fₙ + R` with `R = C(η·∑ res α) ∈ k` (the `extendDeriv_logPart_eq_div_add_residual`
residual). The residue coefficients `cᵢ` ARE the §5.6 residues `res α`, so `∑ res α = ∑ᵢ cᵢ` is the sum
of the `logs` coefficients and `R = η · ∑ᵢ cᵢ ∈ α` is a constant in `t` — a base-field element. -/

variable {α : Type*} [CField α]

/-- **The hyperexponential normal-part residual** `cHyperexpResidualG η logs = η · ∑ᵢ cᵢ ∈ α` (Bronstein
§5.9): the explicit residual `R = C(η·∑ res)` by which the §5.6 Rothstein–Trager log part `∑ᵢ cᵢ·log(vᵢ)`
overshoots the normal integrand on a hyperexponential monomial (`η = Dt/t`). The §5.6 residues `res α` are
the `logs` coefficients `cᵢ`, so `∑ res = ∑ᵢ cᵢ` (the fold of `logs.map .1`), and `R = η · ∑ᵢ cᵢ`. A
constant in `t`, hence a base-field (`k = α`-level) element — itself elementary-integrable as a function of
the previous tower variable. -/
def cHyperexpResidualG (η : α) (logs : List (α × CPolyG α)) : α :=
  CField.mul η (logs.foldl (fun acc cv => CField.add acc cv.1) CField.zero)

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-! ### The fuel-free §5.9 normal-part integrator `∫ fₙ = logPart − ∫R`

`cIntegrateHyperexpNormalGWf` integrates a **normal** part `fₙ = a/d` of a hyperexponential monomial by
running the fuel-free reduced capstone, reading the residual `R = η·∑res`, integrating the base residual
`∫R` over `α` by `CRischField.crischDESolve 0 R`, and subtracting `∫R` from the rational part. -/

/-- **The fuel-free §5.9 hyperexponential normal-part integral** `cIntegrateHyperexpNormalGWf Dt a d cands`:
the residual-feedback normal driver with the reduced capstone replaced by `cIntegrateReducedGWf`. -/
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

/-- **The fuel-free full hyperexponential integral with normal feedback** `cIntegrateHyperexpFullGWf Dt a d
cands`: use the fuel-free canonical split and fuel-free §5.9 normal-part driver. -/
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
