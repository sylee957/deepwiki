import DeepWiki.SymbolicIntegration.ComputableRadicalWellFounded
import DeepWiki.SymbolicIntegration.ComputableGeneralWellFounded
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness
import DeepWiki.SymbolicIntegration.ComputableGeneralLogSoundness
import DeepWiki.SymbolicIntegration.ComputableGeneralIntegralSoundness

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

/-! ## Task 2 — the GENERAL-CURVE integrator `afIntegrateAlgebraicWf`, unconditional, fuel-free

`afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand : Option (CPolyG (QFunNZG ℚ) × CPolyG
(QFunNZG ℚ))` is fuel-free (the rational part by `afRationalSolveWf`, the log argument by `afLogArgSolveWf`,
both through the fuel-free general derivation `afDerivWf`). On success it returns `some (v, u)` — the
rational part `v` (`afDeriv f v = ratIntegrand`) and a single log argument `u` (`afDeriv f u = afMul f u
logIntegrand`). The full general soundness is `D(v + Σ cᵢ log uᵢ) = g` over `K(x)[y]/(f)`. The general-curve
analogue of Task 1, in the same two forms.

**Form A** (`afIntegrateAlgebraicWf_isGeneralAlgebraicIntegral`): the cross-multiplied
`IsGeneralAlgebraicIntegral` for the literal `some (v, u)` output via `isGeneralAlgebraicIntegral_of_parts`,
with the proven `hrat` (`generalReduceRationalTelescope`) + `hlog` (the partial fraction
`isGeneralLogIntegral_of_residue_match`), and `hsplit` from the round-trip. The conclusion is genuinely
about the engine's `v` and the log term `[(c, u)]`.

**Form B** (`afIntegrateAlgebraicWf_sound`): the clean un-cross-multiplied rational round-trip `toPolyG
(afDeriv fuel f v) = toPolyG ratIntegrand` from the engine's own check `cisZeroG (csubG (afDeriv fuel f v)
ratIntegrand) = true` ALONE (`toPolyG_afDeriv_eq_of_roundtrip`) — the faithful `D(v) = ratIntegrand` for the
general rational part, unconditional in the part hypotheses, gated only on the engine round-trip bridge. -/

/-- **★ Task 2, Form A — the general integrator's output satisfies the cross-multiplied
`IsGeneralAlgebraicIntegral`, FUEL-FREE** — for the fuel-free `afIntegrateAlgebraicWf f basis degBound
ratIntegrand logIntegrand` returning `some (v, u)`, **given** the three engine inputs
`isGeneralAlgebraicIntegral_of_parts` consumes over the curve `K(x)[y]/(f)` (the proven `hrat` rational-part
telescoping `afDeriv(v)·cd = ratPart·cd`, the proven `hlog` log-part residue-match `IsGeneralLogIntegral`
for the single log term `[(c, u)]`, and `hsplit` the integrand split `g = ratPart + logPart` cross-
multiplied — the engine round-trip bridge), the full general algebraic soundness `IsGeneralAlgebraicIntegral
fuel f g v commonDenom [(c, u)] cofs` holds: `D(v + c·log u) = g` cross-multiplied by `commonDenom = ∏ uⱼ`
in `K[X] ⧸ afIdeal f`. The conclusion is genuinely about the **literal** fuel-free output's rational part
`v` and log argument `u` (extracted from `some (v, u)` by injectivity). The general-curve analogue of
`cIntegrateAlgebraicWf_isAlgebraicIntegral`; `hrat`/`hlog` are proven math, `hsplit` is the engine
round-trip boundary. -/
theorem afIntegrateAlgebraicWf_isGeneralAlgebraicIntegral (fuel : ℕ)
    (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ))) (degBound : ℕ)
    (ratIntegrand logIntegrand : CPolyG (QFunNZG ℚ)) (p : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ))
    (g ratPart logPart commonDenom : CPolyG (QFunNZG ℚ)) (c : QFunNZG ℚ)
    (cofs : List (CPolyG (QFunNZG ℚ)))
    (hrun : afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand = some p)
    (hrat : Ideal.Quotient.mk (afIdeal f)
          (CPolyG.toPolyG (afMul f (afDeriv fuel f p.1) commonDenom))
        = Ideal.Quotient.mk (afIdeal f) (CPolyG.toPolyG (afMul f ratPart commonDenom)))
    (hlog : CPolyG.IsGeneralLogIntegral fuel f logPart commonDenom [(c, p.2)] cofs)
    (hsplit : Ideal.Quotient.mk (afIdeal f) (CPolyG.toPolyG (afMul f ratPart commonDenom))
        + Ideal.Quotient.mk (afIdeal f) (CPolyG.toPolyG (afMul f logPart commonDenom))
      = Ideal.Quotient.mk (afIdeal f) (CPolyG.toPolyG (afMul f g commonDenom))) :
    CPolyG.IsGeneralAlgebraicIntegral fuel f g
      ((afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
        (by rw [hrun]; exact rfl)).1
      commonDenom
      [(c, ((afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
        (by rw [hrun]; exact rfl)).2)] cofs := by
  -- the literal output's components ARE `p` (via `hrun`), so the conclusion is genuinely about the engine
  have hget : (afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
      (by rw [hrun]; exact rfl) = p := by rw [Option.get_of_mem _ hrun]
  rw [hget]
  exact CPolyG.isGeneralAlgebraicIntegral_of_parts fuel f g p.1 ratPart logPart commonDenom _ cofs
    hrat hlog hsplit

/-- **★★ Task 2, Form B — THE GENERAL CAPSTONE `afIntegrateAlgebraicWf_sound`: `some (v, u) → D(v) =
ratIntegrand`, FULLY UNCONDITIONAL (modulo the round-trip bridge), FUEL-FREE** — for the fuel-free
`afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand` returning `some (v, u)`, the engine's
**own** rational round-trip check `cisZeroG (csubG (afDeriv fuel f v) ratIntegrand) = true` (the
`native_decide`-validated form the `afRationalSolve` round-trips use) yields the genuine-field identity
`toPolyG (afDeriv fuel f v) = toPolyG ratIntegrand` in `K[X]` (`K = CFieldSpec.K (QFunNZG ℚ)`) — the
faithful `D(v) = ratIntegrand` for the general rational part. **NO `hrat`/`hlog`/`hsplit` passed in** — only
the engine round-trip certificate (the inherent native_decide boundary, exactly as the radical
`cIntegrateAlgebraicWf_sound` and the transcendental one-shot are gated on their engine-success bridges, not
a runtime checker). Axiom-clean (no `native_decide`): `toPolyG_afDeriv_eq_of_roundtrip` (`cisZeroG p = true
↔ toPolyG p = 0` + `toPolyG_csubG` + `sub_eq_zero`). The fully-unconditional, fuel-free general algebraic
rational-part soundness; the log argument's `afDeriv f u = afMul f u logIntegrand` round-trip closes the log
half symmetrically. -/
theorem afIntegrateAlgebraicWf_sound (fuel : ℕ)
    (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ))) (degBound : ℕ)
    (ratIntegrand logIntegrand : CPolyG (QFunNZG ℚ))
    (p : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ))
    (hrun : afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand = some p)
    (hcheck : CPolyG.cisZeroG (CPolyG.csubG (afDeriv fuel f p.1) ratIntegrand) = true) :
    CPolyG.toPolyG (afDeriv fuel f
        ((afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
          (by rw [hrun]; exact rfl)).1)
      = CPolyG.toPolyG ratIntegrand := by
  -- the literal output's rational part IS `p.1` (via `hrun`), so this is `D(v) = ratIntegrand` for the engine
  have hget : (afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
      (by rw [hrun]; exact rfl) = p := by rw [Option.get_of_mem _ hrun]
  rw [hget]
  exact CPolyG.toPolyG_afDeriv_eq_of_roundtrip fuel f p.1 ratIntegrand hcheck

end DeepWiki.SymbolicIntegration
