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
  the already-fuel-free leaves). `[CFracGcdCoreWf α]` replaces `[CFracGcdCore α]`.

* **`cIntegrateGFullWf_eq`** — the correspondence: `cIntegrateGFullWf = cIntegrateGFull fuel` at any
  sufficient fuel, the conjunction of the three leaf bridges (`canonicalRepresentationFastGWf_eq` /
  `cIntegrateReducedGWf_eq` / `cPolyRischDEGWf_eq`), taken as hypotheses (the fuel bounds live only there). -/

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

/-! ### Bridge — `cIntegrateGFullWf` equals `cIntegrateGFull` at any sufficient fuel

`cIntegrateGFull` is flat, so its fuel-free companion agrees with it once the three leaf bridges feed in
(`canonicalRepresentationFastGWf_eq` / `cIntegrateReducedGWf_eq` / `cPolyRischDEGWf_eq`). The fuel bounds live
only in those hypotheses; the runtime `cIntegrateGFullWf` carries none. A pure composition rewrite. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CFracGcdCoreWf α] [CRischField α]

/-- **★ Bridge — `cIntegrateGFullWf` equals `cIntegrateGFull` at any sufficient fuel.** From the canonical-rep
bridge (`hcanon : canonicalRepresentationFastGWf Dt a d = canonicalRepresentationFastG Dt fuel a d`), the
reduced-capstone bridge (`hred`) on the resulting normal part `(cn, dn)`, and the polynomial-part RDE bridge
(`hpoly`) on `fp` — `cIntegrateGFullWf Dt a d cands = cIntegrateGFull Dt fuel a d cands`. The fuel bounds live
only in the hypotheses; `cIntegrateGFullWf` carries none. A pure composition rewrite over the flat wrapper. -/
theorem cIntegrateGFullWf_eq (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (hcanon : canonicalRepresentationFastGWf Dt a d = canonicalRepresentationFastG Dt fuel a d)
    (hred : cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands
      = cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands)
    (hpoly : cPolyRischDEGWf Dt [] (canonicalRepresentationFastGWf Dt a d).1
        ((cdegG (canonicalRepresentationFastGWf Dt a d).1 : ℤ) + 1)
      = cPolyRischDEG Dt fuel [] (canonicalRepresentationFastG Dt fuel a d).1
          ((cdegG (canonicalRepresentationFastG Dt fuel a d).1 : ℤ) + 1)) :
    cIntegrateGFullWf Dt a d cands = cIntegrateGFull Dt fuel a d cands := by
  rw [cIntegrateGFullWf, cIntegrateGFull]
  -- both sides `match (canonical split) with | (fp,(b,_ds),cn,dn) => …`; align the split by `hcanon`, then
  -- the reduced capstone (on `(cn, dn)`) by `hred` and the polynomial-part RDE (on `fp`) by `hpoly`
  -- (their projections are exactly the match's `cn`/`dn`/`fp`). Same technique as `cIntegrateGWf_eq`.
  simp only [hcanon] at hred hpoly ⊢
  -- after `hcanon` both `match`es are on `canonicalRepresentationFastG fuel a d`; expand to projections
  rw [show (canonicalRepresentationFastG Dt fuel a d)
      = ((canonicalRepresentationFastG Dt fuel a d).1,
         ((canonicalRepresentationFastG Dt fuel a d).2.1.1,
          (canonicalRepresentationFastG Dt fuel a d).2.1.2),
         ((canonicalRepresentationFastG Dt fuel a d).2.2.1,
          (canonicalRepresentationFastG Dt fuel a d).2.2.2)) from rfl]
  simp only []
  rw [hred, hpoly]
  rfl

end CPolyG

end DeepWiki.SymbolicIntegration
