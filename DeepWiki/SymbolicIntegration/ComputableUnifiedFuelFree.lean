import DeepWiki.SymbolicIntegration.ComputableRadicalWellFounded
import DeepWiki.SymbolicIntegration.ComputableTowerRischDEWellFounded

/-! # The FUEL-FREE transcendental top entry `cIntegrateGFullWf` — the fuel-free companion of the
transcendental driver `cIntegrateGFull`.

The transcendental engine is fuel-free end-to-end in its *core* — `cIntegrateReducedGWf` / `cIntegratePolyGWf` /
`cPolyRischDEGWf` (`ComputableTowerWellFounded` / `ComputableTowerRischDEWellFounded`). The one remaining gap
was the transcendental TOP entry `cIntegrateGFull` (`ComputableTowerRischDE`), which still routed to the fuel
versions. This file closes it — the transcendental top entry becomes fuel-free.

* **`cIntegrateGFullWf`** — the fuel-free companion of `cIntegrateGFull`. The original is a **FLAT wrapper**:
  canonical-rep split, then a `b = 0` test routing the normal part to `cIntegrateReducedG` and the polynomial
  part to the `b = 0` RDE oracle `cPolyRischDEG`. So the fuel-free version is a pure **leaf substitution** —
  `canonicalRepresentationFastG → canonicalRepresentationFastGWf`, `cIntegrateReducedG →
  cIntegrateReducedGWf`, `cPolyRischDEG → cPolyRischDEGWf` — with NO `termination_by` (all recursion lives in
  the already-fuel-free leaves). `[CFracGcdCoreWf α]` replaces `[CFracGcdCore α]`. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG RadElem

/-! ## `cIntegrateGFullWf` — the fuel-free transcendental top entry (flat leaf substitution) -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-- **The fuel-free full poly/special tower integral** `cIntegrateGFullWf Dt a d cands` — the generic,
fuel-free companion of `cIntegrateGFull`. Integrate `f = a/d ∈ α(t)` over `D = cmonomialDeriv Dt`, returning
`some ⟨(num, den), logs⟩` with `∫ f = num/den + ∑ᵢ cᵢ·log(vᵢ)`, or `none`. A pure **leaf substitution** of the
flat-wrapper `cIntegrateGFull`: (1) `canonicalRepresentationFastGWf` splits `f = fₚ + (b/dₛ) + (cₙ/dₙ)`;
(2) if the special part `b` vanishes, the normal part `cₙ/dₙ` is integrated by `cIntegrateReducedGWf` (Hermite
+ residue logs); (3) if `fₚ` also vanishes, return that; else solve the polynomial part by the `b = 0` RDE
oracle `cPolyRischDEGWf Dt [] fp (deg fp + 1)` (`Dqₚ = fₚ`, primitive case) and combine the rational parts
`qₚ + gₙ/gₙd = (qₚ·gₙd + gₙ)/gₙd`; (4) a nonzero special part returns `none` (the documented continuation).
Every sub-op is a WF leaf — **no fuel at runtime**; `native_decide`-able over the noncomputable tower.
`[CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]`-generic — runs at any tower level. -/
def cIntegrateGFullWf (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let (fp, (b, _ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d
  if cisZeroG b then
    -- normal part: rational `gₙ/gₙd` + logs.
    let nrm := cIntegrateReducedGWf Dt cn dn cands
    let (gnum, gden) := nrm.rational
    if cisZeroG fp then
      some nrm
    else
      -- polynomial part: solve `Dqₚ = fₚ` by the `b = 0` RDE oracle (primitive case).
      match cPolyRischDEGWf Dt [] fp ((cdegG fp : ℤ) + 1) with
      | none => none
      | some qp =>
        -- combine `qₚ + gₙ/gₙd = (qₚ·gₙd + gₙ)/gₙd`.
        let num := caddG (cmulG qp gden) gnum
        some ⟨(num, gden), nrm.logs⟩
  else none

end CPolyG

/-! ## Level-2 validation for the fuel-free top entry

The reduced-case capstone leaves the polynomial part `fₚ = t₂` of `f = t₂` over `ℚ(x)(t₁)[t₂]`
undisposed. The fuel-free full driver `cIntegrateGFullWf` lands it: `∫ t₂ = (1/2)t₂²` (the Wf RDE oracle
solves `Dqₚ = t₂` → `qₚ = (1/2)t₂²`, since `D(t₂) = Dt₂ = 1` for the independent monomial `Dt₂ = [1]`),
with no logarithmic part. -/

open CPolyG

/-- Level-2 monomial derivative `Dt₂ = 1` over `CPolyG Lvl2 = ℚ(x)(t₁)[t₂]`. -/
def towerFullLvl2Dt : CPolyG Lvl2 := [CField.one]

/-- The level-2 integrand numerator `f = t₂` over `CPolyG Lvl2`. -/
def towerFullLvl2A : CPolyG Lvl2 := [CField.zero, CField.one]

/-- The level-2 integrand denominator `d = 1` over `CPolyG Lvl2`. -/
def towerFullLvl2D : CPolyG Lvl2 := [CField.one]

/-- The level-2 residue candidate set for the no-log polynomial-part example. -/
def towerFullLvl2Cands : List Lvl2 := [CField.zero, CField.one]

/-- **The fuel-free full driver lands `∫ t₂ = (1/2)t₂²` at level 2** (`native_decide`): `cIntegrateGFullWf`
returns an antiderivative for the pure polynomial part `t₂`, and `checkIdentityG` verifies
`D(∫f) = f`. -/
theorem towerFullLvl2_landsPolynomialPartWf :
    (match CPolyG.cIntegrateGFullWf towerFullLvl2Dt towerFullLvl2A towerFullLvl2D
        towerFullLvl2Cands with
      | some res => CPolyG.checkIdentityG towerFullLvl2Dt res towerFullLvl2A towerFullLvl2D
      | none => false) = true := by native_decide

#print axioms towerFullLvl2_landsPolynomialPartWf

end DeepWiki.SymbolicIntegration
