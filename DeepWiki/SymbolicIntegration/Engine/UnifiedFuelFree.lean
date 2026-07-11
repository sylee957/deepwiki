import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.IntegrationSpec

/-! # The fuel-free transcendental top entry `cIntegrateGFullWf`.
Fuel-free companion of `cIntegrateGFull`: a leaf substitution routing to `canonicalRepresentationFast`,
`cIntegrateReduced`, and `cPolyRischDE`, plus the check-identity soundness bridge. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly RadElem

/-! ## `cIntegrateGFullWf` — the fuel-free transcendental top entry (flat leaf substitution) -/

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α]
  [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
  [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CRischField α]

/-- `cIntegrateGFullWf Dt a d cands`: the fuel-free full poly/special tower integral of `f = a/d ∈ α(t)`
over `D = CPolyEngine.monomialDeriv Dt`, returning `some ⟨(num, den), logs⟩` with `∫ f = num/den + ∑ᵢ cᵢ·log(vᵢ)`
or `none` (nonzero special part). A leaf substitution of `cIntegrateGFull`. -/
def cIntegrateGFullWf (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) :
    Option (IntegralResult α) :=
  let (fp, (b, _ds), (cn, dn)) := canonicalRepresentationFast Dt a d
  if cisZero b then
    -- normal part: rational `gₙ/gₙd` + logs.
    let nrm := cIntegrateReduced Dt cn dn cands
    let (gnum, gden) := nrm.rational
    if cisZero fp then
      some nrm
    else
      -- polynomial part: solve `Dqₚ = fₚ` by the `b = 0` RDE oracle (primitive case).
      match cPolyRischDE Dt [] fp ((cdeg fp : ℤ) + 1) with
      | none => none
      | some qp =>
        -- combine `qₚ + gₙ/gₙd = (qₚ·gₙd + gₙ)/gₙd`.
        let num := cadd (cmul qp gden) gnum
        some ⟨(num, gden), nrm.logs⟩
  else none

end DensePoly

/-! ## Check-identity soundness bridge for the fuel-free top entry -/

/-- The fuel-free full driver field identity from its `checkIdentity` certificate — if
`cIntegrateGFullWf Dt a d cands = some res` and the engine's own cleared antiderivative check passes, then
`res` satisfies the field-level identity `D(res) + logResidueSum Dt res.logs = a/d`. -/
theorem field_identity_of_cIntegrateGFullWf_of_checkIdentityG {α : Type*}
    [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CPolyGcd DensePoly α]
    [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CRischField α]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) (res : IntegralResult α)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hgden : toPoly res.rational.2 ≠ 0) (haden : toPoly d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPoly cv.2 ≠ 0)
    (hcheck : DensePoly.checkIdentity Dt res a d = true) :
    towerFractionFieldDeriv Dt
        (CFrac.am α (toPoly res.rational.1) / CFrac.am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = CFrac.am α (toPoly a) / CFrac.am α (toPoly d) :=
by
  have _ := hsome
  exact field_identity_of_checkIdentityG Dt res a d hgden haden hlogs hcheck

/-- `cIntegrateGFullWf` satisfies the semantic `IsIntegralResult` spec from its `checkIdentity`
certificate. -/
theorem isIntegralResultG_of_cIntegrateGFullWf_of_checkIdentityG {α : Type*}
    [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CPolyGcd DensePoly α]
    [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CRischField α]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) (res : IntegralResult α)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hgden : toPoly res.rational.2 ≠ 0) (haden : toPoly d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPoly cv.2 ≠ 0)
    (hcheck : DensePoly.checkIdentity Dt res a d = true) :
    DensePoly.IsIntegralResult Dt a d res := by
  have _ := hsome
  exact DensePoly.isIntegralResultG_of_checkIdentityG Dt res a d hgden haden hlogs hcheck

/-! ### Restatement against the intended wording -/

example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CPolyGcd DensePoly α]
    [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CRischField α]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α) (res : IntegralResult α)
    (hsome : DensePoly.cIntegrateGFullWf Dt a d cands = some res)
    (hgden : toPoly res.rational.2 ≠ 0) (haden : toPoly d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPoly cv.2 ≠ 0)
    (hcheck : DensePoly.checkIdentity Dt res a d = true) :
    towerFractionFieldDeriv Dt
        (CFrac.am α (toPoly res.rational.1) / CFrac.am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = CFrac.am α (toPoly a) / CFrac.am α (toPoly d) :=
  field_identity_of_cIntegrateGFullWf_of_checkIdentityG Dt a d cands res hsome hgden haden hlogs hcheck

/-! ## Level-2 validation for the fuel-free top entry

`cIntegrateGFullWf` computes `∫ t₂ = (1/2)t₂²` over `ℚ(x)(t₁)[t₂]` (`Dt₂ = 1`), with no logarithmic
part. -/

open DensePoly

/-- Level-2 monomial derivative `Dt₂ = 1` over `DensePoly Lvl2 = ℚ(x)(t₁)[t₂]`. -/
def towerFullLvl2Dt : DensePoly Lvl2 := [CCommRing.one]

/-- The level-2 integrand numerator `f = t₂` over `DensePoly Lvl2`. -/
def towerFullLvl2A : DensePoly Lvl2 := [CCommRing.zero, CCommRing.one]

/-- The level-2 integrand denominator `d = 1` over `DensePoly Lvl2`. -/
def towerFullLvl2D : DensePoly Lvl2 := [CCommRing.one]

/-- The level-2 residue candidate set for the no-log polynomial-part example. -/
def towerFullLvl2Cands : List Lvl2 := [CCommRing.zero, CCommRing.one]

/-- `cIntegrateGFullWf` lands `∫ t₂ = (1/2)t₂²` at level 2, with `checkIdentity` verifying `D(∫f) = f`. -/
theorem towerFullLvl2_landsPolynomialPartWf :
    (match DensePoly.cIntegrateGFullWf towerFullLvl2Dt towerFullLvl2A towerFullLvl2D
        towerFullLvl2Cands with
      | some res => DensePoly.checkIdentity towerFullLvl2Dt res towerFullLvl2A towerFullLvl2D
      | none => false) = true := by native_decide


end DeepWiki.SymbolicIntegration
