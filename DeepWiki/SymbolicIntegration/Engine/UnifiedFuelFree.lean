import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.IntegrationSpec

/-! # The fuel-free transcendental top entry `cIntegrateGFullWf`.
Fuel-free companion of `cIntegrateGFull`: a leaf substitution routing to `canonicalRepresentationFastG`,
`cIntegrateReducedG`, and `cPolyRischDEG`, plus the check-identity soundness bridge. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG RadElem

/-! ## `cIntegrateGFullWf` — the fuel-free transcendental top entry (flat leaf substitution) -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-- `cIntegrateGFullWf Dt a d cands`: the fuel-free full poly/special tower integral of `f = a/d ∈ α(t)`
over `D = cmonomialDeriv Dt`, returning `some ⟨(num, den), logs⟩` with `∫ f = num/den + ∑ᵢ cᵢ·log(vᵢ)`
or `none` (nonzero special part). A leaf substitution of `cIntegrateGFull`. -/
def cIntegrateGFullWf (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let (fp, (b, _ds), (cn, dn)) := canonicalRepresentationFastG Dt a d
  if cisZeroG b then
    -- normal part: rational `gₙ/gₙd` + logs.
    let nrm := cIntegrateReducedG Dt cn dn cands
    let (gnum, gden) := nrm.rational
    if cisZeroG fp then
      some nrm
    else
      -- polynomial part: solve `Dqₚ = fₚ` by the `b = 0` RDE oracle (primitive case).
      match cPolyRischDEG Dt [] fp ((cdegG fp : ℤ) + 1) with
      | none => none
      | some qp =>
        -- combine `qₚ + gₙ/gₙd = (qₚ·gₙd + gₙ)/gₙd`.
        let num := caddG (cmulG qp gden) gnum
        some ⟨(num, gden), nrm.logs⟩
  else none

end CPolyG

/-! ## Check-identity soundness bridge for the fuel-free top entry -/

/-- The fuel-free full driver field identity from its `checkIdentityG` certificate — if
`cIntegrateGFullWf Dt a d cands = some res` and the engine's own cleared antiderivative check passes, then
`res` satisfies the field-level identity `D(res) + logResidueSumG Dt res.logs = a/d`. -/
theorem field_identity_of_cIntegrateGFullWf_of_checkIdentityG {α : Type*}
    [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α] [CRischField α]
    (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) (res : IntegralResultG α)
    (hsome : CPolyG.cIntegrateGFullWf Dt a d cands = some res)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res a d = true) :
    towerFractionFieldDerivG Dt
        (QFunNZG.amG α (toPolyG res.rational.1) / QFunNZG.amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = QFunNZG.amG α (toPolyG a) / QFunNZG.amG α (toPolyG d) :=
by
  have _ := hsome
  exact field_identity_of_checkIdentityG Dt res a d hgden haden hlogs hcheck

/-- `cIntegrateGFullWf` satisfies the semantic `IsIntegralResultG` spec from its `checkIdentityG`
certificate. -/
theorem isIntegralResultG_of_cIntegrateGFullWf_of_checkIdentityG {α : Type*}
    [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α] [CRischField α]
    (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) (res : IntegralResultG α)
    (hsome : CPolyG.cIntegrateGFullWf Dt a d cands = some res)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res a d = true) :
    CPolyG.IsIntegralResultG Dt a d res := by
  have _ := hsome
  exact CPolyG.isIntegralResultG_of_checkIdentityG Dt res a d hgden haden hlogs hcheck

/-! ### Restatement against the intended wording -/

example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α] [CRischField α]
    (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) (res : IntegralResultG α)
    (hsome : CPolyG.cIntegrateGFullWf Dt a d cands = some res)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res a d = true) :
    towerFractionFieldDerivG Dt
        (QFunNZG.amG α (toPolyG res.rational.1) / QFunNZG.amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = QFunNZG.amG α (toPolyG a) / QFunNZG.amG α (toPolyG d) :=
  field_identity_of_cIntegrateGFullWf_of_checkIdentityG Dt a d cands res hsome hgden haden hlogs hcheck

/-! ## Level-2 validation for the fuel-free top entry

`cIntegrateGFullWf` computes `∫ t₂ = (1/2)t₂²` over `ℚ(x)(t₁)[t₂]` (`Dt₂ = 1`), with no logarithmic
part. -/

open CPolyG

/-- Level-2 monomial derivative `Dt₂ = 1` over `CPolyG Lvl2 = ℚ(x)(t₁)[t₂]`. -/
def towerFullLvl2Dt : CPolyG Lvl2 := [CField.one]

/-- The level-2 integrand numerator `f = t₂` over `CPolyG Lvl2`. -/
def towerFullLvl2A : CPolyG Lvl2 := [CField.zero, CField.one]

/-- The level-2 integrand denominator `d = 1` over `CPolyG Lvl2`. -/
def towerFullLvl2D : CPolyG Lvl2 := [CField.one]

/-- The level-2 residue candidate set for the no-log polynomial-part example. -/
def towerFullLvl2Cands : List Lvl2 := [CField.zero, CField.one]

/-- `cIntegrateGFullWf` lands `∫ t₂ = (1/2)t₂²` at level 2, with `checkIdentityG` verifying `D(∫f) = f`. -/
theorem towerFullLvl2_landsPolynomialPartWf :
    (match CPolyG.cIntegrateGFullWf towerFullLvl2Dt towerFullLvl2A towerFullLvl2D
        towerFullLvl2Cands with
      | some res => CPolyG.checkIdentityG towerFullLvl2Dt res towerFullLvl2A towerFullLvl2D
      | none => false) = true := by native_decide


end DeepWiki.SymbolicIntegration
