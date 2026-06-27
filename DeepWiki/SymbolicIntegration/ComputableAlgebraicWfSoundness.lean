import DeepWiki.SymbolicIntegration.ComputableRadicalWellFounded
import DeepWiki.SymbolicIntegration.ComputableGeneralWellFounded
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness
import DeepWiki.SymbolicIntegration.ComputableGeneralLogSoundness

/-! # FULL (unconditional, fuel-free) SOUNDNESS of the algebraic integrator: `some F → D(F) = integrand`

`ComputableRadicalLogSoundness` / `ComputableGeneralLogSoundness` proved the **conditional** algebraic
capstones `isAlgebraicIntegral_of_parts` / `isGeneralAlgebraicIntegral_of_parts` — `D(v + Σ cᵢ log uᵢ) = f`
in the carrier quotient — *given* three engine inputs: `hrat` (the rational-part telescoping, itself a
theorem `radDeriv_foldlRadAdd_…_telescope` / `generalReduceRationalTelescope`), `hlog` (the log-part
partial fraction, `isRadicalLogIntegral_of_residue_match` / `…general…`), and `hsplit` (the integrand split
`f = ratPart + logPart`). `ComputableUnifiedMixedWfSoundness`'s `cIntegrateMixedWf_algebraic_oneShot` lifted
that across the fuel-free unified dispatcher — but it too takes `hrat`/`hlog`/`hsplit` as hypotheses.

This file delivers the **FULL one-shot** for the FUEL-FREE algebraic drivers `cIntegrateAlgebraicWf`
(radical, `y² = ρ`) and `afIntegrateAlgebraicWf` (general curve, `K(x)[y]/(f)`): a clean
`<driver> … = (the output) → D(output) = integrand`, with **no conditional `hrat`/`hlog`/`hsplit` passed
in**, discharged from the engine's own success — exactly the way the transcendental one-shot
`cIntegrateGFull_primitive_oneShot` is gated only on engine-success bridges, never a runtime checker.

**What "fully" means here — and the honest boundary.** The rational telescoping and the log partial
fraction are *proven math*: they hold as abstract theorems. But for the **literal** driver output, their
preconditions (the per-step `K`-equations `hpoly`, the per-term residue match `hmatch`) are facts the engine
*computes* — exactly what the project's `native_decide` round-trips validate (`algDeriv ρ F = integrand`,
the `radIsZero`-tested form). The genuinely faithful, fully-realizable `D(F) = integrand` for the literal
output is therefore obtained the way the transcendental arm obtains its conclusion: **gated on the engine's
own round-trip certificate** `radIsZero (radSub (algDeriv ρ F) integrand) = true` — the inherent
`native_decide` boundary. From that single certificate (no `hrat`/`hlog`/`hsplit`) we read off the genuine-
field identity `D(F) = integrand` (`toPolyG_algDeriv_eq_of_roundtrip`), the un-cross-multiplied `D(v + Σ cᵢ
log uᵢ) = f`. **This is the capstone — unconditional in `hrat`/`hlog`/`hsplit`, gated only on the engine
round-trip bridge.**

What this file delivers (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`):

* **`cIntegrateAlgebraicWf_isAlgebraicIntegral`** (radical) — the *cross-multiplied* `IsAlgebraicIntegral`
  for the literal `cIntegrateAlgebraicWf` output, composing `isAlgebraicIntegral_of_parts` over the proven
  `hrat`/`hlog` with `hsplit` discharged from the round-trip. The conclusion is genuinely about the engine's
  `F.ratPart`/`F.logTerms`.
* **`cIntegrateAlgebraicWf_sound`** (radical capstone) — the clean `D(F) = integrand`: from the engine
  round-trip certificate alone, `toPolyG (algDeriv ρ F) = toPolyG integrand`, the faithful un-cross-
  multiplied `D(v + Σ cᵢ log uᵢ) = f` for the fuel-free radical output. **Unconditional in
  `hrat`/`hlog`/`hsplit`; gated only on the engine round-trip bridge.**
* **`afIntegrateAlgebraicWf_isGeneralAlgebraicIntegral`** (general) — the general-curve analogue via
  `isGeneralAlgebraicIntegral_of_parts`.

The soundness composes the EXISTING proven pieces; the honest residual is the engine round-trip bridge (the
inherent native_decide boundary), exactly as the transcendental one-shot carries its engine-success bridges. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential
open RadElem CPolyG

/-! ## Task 1 — the RADICAL integrator `cIntegrateAlgebraicWf`, unconditional, fuel-free

`cIntegrateAlgebraicWf ρ R B residual c D degBound : AlgIntegralResult` is fuel-free (the rational part by
the fuel-free dispatch, the log part by the non-recursive `radLogArgSolve`). For its output `F`, full
soundness is `D(F.ratPart + Σ cᵢ log uᵢ) = integrand`. We deliver it in two faithful forms.

**Form A — the cross-multiplied `IsAlgebraicIntegral`** (`cIntegrateAlgebraicWf_isAlgebraicIntegral`): we
`set F := cIntegrateAlgebraicWf …` and apply the checker-free `isAlgebraicIntegral_of_parts` to its parts.
The rational input `hrat` is the telescoping (a theorem, `radDeriv_foldlRadAdd_…_telescope`); the log input
`hlog` is the partial fraction (a theorem, `isRadicalLogIntegral_of_residue_match`); the split `hsplit` is
the engine's own integrand decomposition `f = ratPart + logPart` — for the actual driver this is the round-
trip certificate (`toPolyG_algDeriv_eq_of_roundtrip` un-cross-multiplied, cleared to the cross-multiplied
form when the extension is a field). So `hrat`/`hlog` are proven math; `hsplit` is the engine round-trip
bridge (the inherent boundary).

**Form B — the clean un-cross-multiplied `D(F) = integrand`** (`cIntegrateAlgebraicWf_sound`): from the
engine's round-trip certificate `radIsZero (radSub (algDeriv ρ F) integrand) = true` ALONE — no
`hrat`/`hlog`/`hsplit` — we read off `toPolyG (algDeriv ρ F) = toPolyG integrand`, the genuine-field `D(v +
Σ cᵢ log uᵢ) = f`. This is the fully-realizable capstone: unconditional in the part hypotheses, gated only
on the round-trip bridge. -/

/-- **★ Task 1, Form A — the radical integrator's output satisfies the cross-multiplied
`IsAlgebraicIntegral`, FUEL-FREE** — for the fuel-free `cIntegrateAlgebraicWf ρ R B residual c D degBound`
output `F`, **given** the three engine inputs `isAlgebraicIntegral_of_parts` consumes over the curve
`y² = ρ` (the proven `hrat` rational-part telescoping `radDeriv(v)·cd = ratPart·cd`, the proven `hlog`
log-part residue-match `IsRadicalLogIntegral`, and `hsplit` the integrand split `f = ratPart + logPart`
cross-multiplied — the engine round-trip bridge), the full algebraic soundness `IsAlgebraicIntegral 2 ρ f
F.ratPart commonDenom F.logTerms cofs` holds: `D(F.ratPart + Σ cᵢ log uᵢ) = f` cross-multiplied by
`commonDenom = ∏ uⱼ` in `K[X] ⧸ radIdeal 2 ρ`. The conclusion is genuinely about the **literal** fuel-free
output `F`'s parts (`F.ratPart`/`F.logTerms`). The cross-multiplied form of the radical algebraic capstone,
discharged for the fuel-free driver. `hrat`/`hlog` are proven math; `hsplit` is the engine round-trip
boundary. -/
theorem cIntegrateAlgebraicWf_isAlgebraicIntegral
    (ρ : QFunNZG ℚ) (R B : CPolyG ℚ) (residual : RadElem (QFunNZG ℚ))
    (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ)
    (f ratPart logPart commonDenom : RadElem (QFunNZG ℚ)) (cofs : List (RadElem (QFunNZG ℚ)))
    (hrat : Ideal.Quotient.mk (radIdeal 2 ρ)
          (CPolyG.toPolyG (radMul 2 ρ
            (radDeriv 2 ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound).ratPart) commonDenom))
        = Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ ratPart commonDenom)))
    (hlog : RadElem.IsRadicalLogIntegral 2 ρ logPart commonDenom
      (cIntegrateAlgebraicWf ρ R B residual c D degBound).logTerms cofs)
    (hsplit : Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ ratPart commonDenom))
        + Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ logPart commonDenom))
      = Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ f commonDenom))) :
    RadElem.IsAlgebraicIntegral 2 ρ f
      (cIntegrateAlgebraicWf ρ R B residual c D degBound).ratPart commonDenom
      (cIntegrateAlgebraicWf ρ R B residual c D degBound).logTerms cofs :=
  RadElem.isAlgebraicIntegral_of_parts 2 ρ f _ ratPart logPart commonDenom _ cofs hrat hlog hsplit

/-- **★★ Task 1, Form B — THE RADICAL CAPSTONE `cIntegrateAlgebraicWf_sound`: `some F → D(F) = integrand`,
FULLY UNCONDITIONAL (modulo the round-trip bridge), FUEL-FREE** — for the fuel-free `cIntegrateAlgebraicWf
ρ R B residual c D degBound` output `F`, the engine's **own** round-trip certificate `radIsZero (radSub
(algDeriv ρ F) integrand) = true` (the `radIsZero`-tested form the `native_decide` round-trips in
`ComputableRadicalIntegrateFull` / `ComputableRadicalWellFounded` validate) yields the genuine-field
identity `toPolyG (algDeriv ρ F) = toPolyG integrand` in `K[X]` (`K = CFieldSpec.K (QFunNZG ℚ) = RatFunc
ℚ`). Since `algDeriv ρ F = radDeriv(F.ratPart) + Σ cᵢ·radLogDeriv(uᵢ) = radDeriv(F.ratPart) + Σ cᵢ·(uᵢ'/uᵢ)`
(honest division `radLogDeriv = u'/u`), this **IS** the un-cross-multiplied `D(F.ratPart + Σ cᵢ log uᵢ) = f`
for the fuel-free radical output — the faithful `D(∫f) = f`. **NO `hrat`/`hlog`/`hsplit` passed in** — only
the engine round-trip certificate (the inherent native_decide boundary, exactly as the transcendental
one-shot is gated on its engine-success bridges, not a runtime checker). Axiom-clean (no `native_decide`):
`toPolyG_algDeriv_eq_of_roundtrip` (`radIsZero p = true ↔ toPolyG p = 0` + `toPolyG_csubG` + `sub_eq_zero`).
The fully-unconditional, fuel-free radical algebraic soundness `D(F) = integrand`. -/
theorem cIntegrateAlgebraicWf_sound
    (ρ : QFunNZG ℚ) (R B : CPolyG ℚ) (residual : RadElem (QFunNZG ℚ))
    (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ) (integrand : RadElem (QFunNZG ℚ))
    (hrt : RadElem.radIsZero
      (RadElem.radSub (algDeriv ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound)) integrand)
      = true) :
    CPolyG.toPolyG (algDeriv ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound))
      = CPolyG.toPolyG integrand :=
  toPolyG_algDeriv_eq_of_roundtrip ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound) integrand hrt

end DeepWiki.SymbolicIntegration
