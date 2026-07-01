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

end DeepWiki.SymbolicIntegration
