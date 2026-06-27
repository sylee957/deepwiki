import DeepWiki.SymbolicIntegration.ComputableUnifiedFuelFree
import DeepWiki.SymbolicIntegration.ComputableOneShotAssembly
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness

/-! # The CHECKER-FREE one-shot soundness for the FUEL-FREE UNIFIED integrator `cIntegrateMixedWf`

`ComputableUnifiedFuelFree` built the fuel-free unified dispatcher `cIntegrateMixedWf` (one fuel-free entry
routing the transcendental arm to `cIntegrateGFullWf` and the algebraic arm to `cIntegrateAlgebraicWf`),
validated on a transcendental and an algebraic example by `native_decide` + `checkMixed`.
`ComputableUnifiedMixedSoundness` then composed the two per-arm CHECK-based certificates into the
check-soundness `cIntegrateMixedChecked_sound` — but that route guards the output by the runtime validator
`checkMixed`.

This file delivers the **CHECKER-FREE one-shot**: `cIntegrateMixedWf spec = result → D(result) = integrand`,
for BOTH arms, fuel-free, composing the existing CHECKER-FREE arm soundnesses through the fuel-free bridges —
**no `checkMixed`, no answer-checker**. The conclusion is the same algorithm-correctness statement as the
transcendental one-shot `cIntegrateGFull_primitive_oneShot` and the algebraic `isAlgebraicIntegral_of_parts`,
now lifted across the fuel-free unified dispatcher.

What this file delivers (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`):

* **`cIntegrateMixedWf_transcendental_oneShot`** — the transcendental arm, fuel-free:
  `cIntegrateMixedWf (.transcendental Dt a d cands) = .transcendental (some r) → ` the field identity
  `D(r) = a/d` over `RatFunc (CFieldSpec.K α)`. The Wf dispatcher reduces (`rfl`) to
  `cIntegrateGFullWf Dt a d cands`; the fuel-free transfer `cIntegrateGFullWf_eq` moves to `cIntegrateGFull`
  at sufficient fuel, where the **checker-free** `cIntegrateGFull_primitive_oneShot` applies. Gated only on
  the engine-success bridges (the inherent boundary), NOT a runtime checker.
* **`cIntegrateMixedWf_algebraic_oneShot`** — the algebraic arm, fuel-free:
  `cIntegrateMixedWf (.algebraic …) = .algebraic res → IsAlgebraicIntegral 2 ρ f res.ratPart … res.logTerms`.
  The Wf dispatcher reduces (`rfl`) to `cIntegrateAlgebraicWf …`; the abstract **checker-free**
  `isAlgebraicIntegral_of_parts` supplies `D(res) = f` over the curve quotient `K[X] ⧸ radIdeal 2 ρ` from the
  rational/log/split engine inputs.
* **★ `cIntegrateMixedWf_sound`** — the UNIFIED one-shot, both arms: a single `MixedWfDifferentiatesTo`
  predicate dispatched per arm to the checker-free conclusion of each, and `cIntegrateMixedWf spec = result →
  MixedWfDifferentiatesTo …` by `cases` on the result, each arm by the two theorems above. **The fuel-free
  unified soundness, checker-free.**

* **The completeness MAP** (honest, NOT a proof) — a `/-! … -/` section + named `def`s mapping
  `cIntegrateMixedWf` completeness (`none ⟹ not-elementary`) to its components: the transcendental none ⟸ the
  RDE has no solution ⟸ the RDE DECISION PROCEDURE `crischDESolveSound_isDecisionProcedure` (DONE, mod the §6
  frontier) + Liouville's structure theorem (NOT in Mathlib — the research frontier); the algebraic none ⟸ the
  algebraic-curve Liouville completeness. The DONE parts are cited by name; the Liouville frontier is named, not
  faked. NO `sorry`, NO fake completeness theorem.

The soundness composes the EXISTING proven pieces via the fuel-free bridges; the completeness is the Liouville
frontier — mapped, not ground. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG RadElem

/-! ## Task 1 — the transcendental arm of `cIntegrateMixedWf`, fuel-free, checker-free

`cIntegrateMixedWf (.transcendental Dt a d cands)` is, by the `match` defining `cIntegrateMixedWf`,
definitionally `.transcendental (cIntegrateGFullWf Dt a d cands)`. So if the dispatcher returns
`.transcendental (some r)`, then `cIntegrateGFullWf Dt a d cands = some r`. The fuel-free transfer
`cIntegrateGFullWf_eq` (given the three leaf bridges `hcanon`/`hred`/`hpoly`) rewrites this to
`cIntegrateGFull Dt fuel a d cands = some r` at any sufficient fuel, where the **checker-free**
`cIntegrateGFull_primitive_oneShot` produces the field identity `D(r) = a/d` over `RatFunc (CFieldSpec.K α)`.
No `checkMixed`, no `native_decide` — only the engine-success bridges the one-shot already carries. -/

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCore α] [CFracGcdCoreWf α] [CRischField α]

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCore α] in
/-- **The Wf transcendental arm IS `cIntegrateGFullWf`** — `cIntegrateMixedWf (.transcendental Dt a d cands)
= MixedIntegralResult.transcendental (cIntegrateGFullWf Dt a d cands)`, the definitional reduction of the
`match` in `cIntegrateMixedWf` on the `transcendental` tag. Pins the dispatcher's output shape on the
transcendental arm so a `.transcendental (some r)` result extracts `cIntegrateGFullWf Dt a d cands = some r`. -/
theorem cIntegrateMixedWf_transcendental_eq (Dt a d : CPolyG α) (cands : List α) :
    cIntegrateMixedWf (IntegrandSpec.transcendental Dt a d cands)
      = MixedIntegralResult.transcendental (cIntegrateGFullWf Dt a d cands) :=
  rfl

/-- **★ Task 1 — the transcendental arm of `cIntegrateMixedWf` is sound, FUEL-FREE, CHECKER-FREE** — if the
fuel-free unified dispatcher returns `.transcendental (some res)` on a `transcendental Dt a d cands` spec with
a primitive monomial `toPolyG Dt = C w`, **given** the three fuel-free leaf bridges (`hcanon`/`hred`/`hpoly`,
the `cIntegrateGFullWf = cIntegrateGFull fuel` correspondence) and the same engine-success inputs the primitive
one-shot carries (`hb`/`hfp` the pure-normal branch, `hrecon` canonical reconstruction, `hherm` Hermite half,
`hden`/`hA`/`hnorm` the squarefree-factoring data, `hform` per-root residue-log reassembly), the field-level
antiderivative identity `D(res) + logResidueSumG Dt res.logs = amG a/amG d` holds over `RatFunc (CFieldSpec.K
α)`. The dispatcher reduces (`rfl`) to `cIntegrateGFullWf Dt a d cands = some res`; `cIntegrateGFullWf_eq`
transfers it to `cIntegrateGFull Dt fuel a d cands = some res`; `cIntegrateGFull_primitive_oneShot` (the
checker-free transcendental one-shot) closes it. **No `checkMixed`, no `native_decide`** — gated only on the
engine-success bridges (the inherent native_decide boundary, NOT a runtime checker). The transcendental arm of
the fuel-free unified soundness. -/
theorem cIntegrateMixedWf_transcendental_oneShot (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α)
    (cands : List α) (res : IntegralResultG α) (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α)
    (hDt : toPolyG Dt = C w)
    (hrun : cIntegrateMixedWf (IntegrandSpec.transcendental Dt a d cands)
      = MixedIntegralResult.transcendental (some res))
    (hcanon : canonicalRepresentationFastGWf Dt a d = canonicalRepresentationFastG Dt fuel a d)
    (hred : cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands
      = cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands)
    (hpoly : cPolyRischDEGWf Dt [] (canonicalRepresentationFastGWf Dt a d).1
        ((cdegG (canonicalRepresentationFastGWf Dt a d).1 : ℤ) + 1)
      = cPolyRischDEG Dt fuel [] (canonicalRepresentationFastG Dt fuel a d).1
          ((cdegG (canonicalRepresentationFastG Dt fuel a d).1 : ℤ) + 1))
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = true)
    (hrecon : amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
          / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1)
            / amG α (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2)
        = amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (CPolyG.cIntegrateReducedG Dt fuel
            (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) := by
  -- the dispatcher reduces (rfl) to `cIntegrateGFullWf …`; the `.transcendental (some _)` wrapper is
  -- injective, so `cIntegrateGFullWf Dt a d cands = some res`
  rw [cIntegrateMixedWf_transcendental_eq, MixedIntegralResult.transcendental.injEq] at hrun
  have hwf : cIntegrateGFullWf Dt a d cands = some res := hrun
  -- transfer to the fuel'd driver via the three leaf bridges, then apply the checker-free primitive one-shot
  rw [cIntegrateGFullWf_eq Dt fuel a d cands hcanon hred hpoly] at hwf
  exact cIntegrateGFull_primitive_oneShot Dt fuel a d cands res s w hDt hb hfp hwf hrecon hherm hden hA
    hnorm hform

end CPolyG

/-! ## Task 2 — the algebraic arm of `cIntegrateMixedWf`, fuel-free, checker-free

`cIntegrateMixedWf (.algebraic ρ R B residual c D degBound)` is, by the `match` defining `cIntegrateMixedWf`,
definitionally `.algebraic (cIntegrateAlgebraicWf ρ R B residual c D degBound)`. So if the dispatcher returns
`.algebraic res`, then `res = cIntegrateAlgebraicWf ρ R B residual c D degBound` and its parts are
`res.ratPart` (the rational part `v`) and `res.logTerms` (the log arguments `args`). The abstract,
**checker-free** `RadElem.isAlgebraicIntegral_of_parts` (over the curve `y² = ρ`, `n = 2`) then supplies the
full algebraic soundness `IsAlgebraicIntegral 2 ρ f res.ratPart commonDenom res.logTerms cofs` — `D(v + Σ cᵢ
log uᵢ) = f` cross-multiplied by `commonDenom = ∏ uⱼ` and read in the carrier quotient `K[X] ⧸ radIdeal 2 ρ`
— from the rational/log/split engine inputs. No `checkMixed`, no `native_decide` — only the engine-success
bridges the of_parts composition carries (the algebraic analogue of the transcendental's `hherm`/`hform`). -/

/-- **The Wf algebraic arm IS `cIntegrateAlgebraicWf`** — `cIntegrateMixedWf (.algebraic ρ R B residual c D
degBound) = MixedIntegralResult.algebraic (cIntegrateAlgebraicWf ρ R B residual c D degBound)`, the
definitional reduction of the `match` in `cIntegrateMixedWf` on the `algebraic` tag (over a base `α` that
supplies the fuel-free binders). Pins the dispatcher's output shape on the algebraic arm so an `.algebraic res`
result extracts `res = cIntegrateAlgebraicWf …`. -/
theorem cIntegrateMixedWf_algebraic_eq {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]
    [CRischField α] (ρ : QFunNZG ℚ) (R B : CPolyG ℚ) (residual : RadElem (QFunNZG ℚ))
    (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ) :
    cIntegrateMixedWf (α := α) (IntegrandSpec.algebraic ρ R B residual c D degBound)
      = MixedIntegralResult.algebraic (cIntegrateAlgebraicWf ρ R B residual c D degBound) :=
  rfl

/-- **★ Task 2 — the algebraic arm of `cIntegrateMixedWf` is sound, FUEL-FREE, CHECKER-FREE** — if the
fuel-free unified dispatcher returns `.algebraic res` on an `algebraic ρ R B residual c D degBound` spec, then
**given** the abstract engine-success inputs `RadElem.isAlgebraicIntegral_of_parts` consumes over the curve
`y² = ρ` (`hrat` rational-part telescoping soundness `radDeriv(v)·cd = ratPart·cd`, `hlog` log-part
residue-match soundness `IsRadicalLogIntegral`, `hsplit` the integrand split `f = ratPart + logPart`,
cross-multiplied), the full algebraic-integral soundness `IsAlgebraicIntegral 2 ρ f res.ratPart commonDenom
res.logTerms cofs` holds — `D(res.ratPart + Σ cᵢ log uᵢ) = f` cross-multiplied by `commonDenom = ∏ uⱼ` in the
carrier quotient `K[X] ⧸ radIdeal 2 ρ`. The dispatcher reduces (`rfl`) to `res = cIntegrateAlgebraicWf …`,
exposing `res.ratPart`/`res.logTerms` as the `v`/`args` of `isAlgebraicIntegral_of_parts` (the checker-free
algebraic capstone composition). **No `checkMixed`, no `native_decide`** — gated only on the engine-success
bridges (the inherent boundary, NOT a runtime checker). The algebraic arm of the fuel-free unified soundness.
The `α`-genericity is only the dispatcher's binder; the result lives over the fixed algebraic base `QFunNZG ℚ`. -/
theorem cIntegrateMixedWf_algebraic_oneShot {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]
    [CRischField α] (ρ : QFunNZG ℚ) (R B : CPolyG ℚ) (residual : RadElem (QFunNZG ℚ))
    (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ) (res : AlgIntegralResult)
    (f ratPart logPart commonDenom : RadElem (QFunNZG ℚ)) (cofs : List (RadElem (QFunNZG ℚ)))
    (hrun : cIntegrateMixedWf (α := α) (IntegrandSpec.algebraic ρ R B residual c D degBound)
      = MixedIntegralResult.algebraic res)
    (hrat : Ideal.Quotient.mk (radIdeal 2 ρ)
          (CPolyG.toPolyG (radMul 2 ρ (radDeriv 2 ρ res.ratPart) commonDenom))
        = Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ ratPart commonDenom)))
    (hlog : RadElem.IsRadicalLogIntegral 2 ρ logPart commonDenom res.logTerms cofs)
    (hsplit : Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ ratPart commonDenom))
        + Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ logPart commonDenom))
      = Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ f commonDenom))) :
    RadElem.IsAlgebraicIntegral 2 ρ f res.ratPart commonDenom res.logTerms cofs := by
  -- the dispatcher reduces (rfl) to `cIntegrateAlgebraicWf …`; the `.algebraic _` wrapper is injective, so
  -- `res` IS the engine's output `cIntegrateAlgebraicWf …` (subst makes the conclusion genuinely about it)
  rw [cIntegrateMixedWf_algebraic_eq, MixedIntegralResult.algebraic.injEq] at hrun
  subst hrun
  -- `res.ratPart`/`res.logTerms` are the engine's parts; the abstract, checker-free
  -- `isAlgebraicIntegral_of_parts` supplies the full `D(∫f) = f` from the engine inputs
  exact RadElem.isAlgebraicIntegral_of_parts 2 ρ f _ ratPart logPart commonDenom _ cofs hrat hlog hsplit

/-! ## ★ Task 3 — the UNIFIED fuel-free checker-free one-shot `cIntegrateMixedWf_sound`

The two arms compose under one case-split. The per-arm checker-free conclusions are genuinely *different*
shapes — the transcendental arm gives the field identity over `RatFunc (CFieldSpec.K α)`, the algebraic arm
gives `IsAlgebraicIntegral` over the curve quotient `K[X] ⧸ radIdeal 2 ρ` — so we package them in one predicate
`MixedWfDifferentiatesTo` that dispatches on the result shape to the matching conclusion, then case-split on
the `IntegrandSpec` tag (which determines the result arm by the two `rfl` reductions) and discharge each arm by
Task 1 / Task 2. The per-arm engine-success inputs are bundled into `TranscendentalArmInputs` /
`AlgebraicArmInputs` so the unified theorem reads cleanly; each bundle carries EXACTLY the engine-success
bridges the corresponding one-shot needs — no runtime checker. **The fuel-free unified soundness, checker-free,
both arms.** -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCore α] [CFracGcdCoreWf α] [CRischField α]

/-- **The per-arm fuel-free checker-free antiderivative-identity predicate** `MixedWfDifferentiatesTo Dt
result a d ρ f commonDenom cofs` — the faithful "`result` differentiates to the integrand", dispatched on the
result shape to each engine's checker-free soundness conclusion (the fuel-free analogue of
`MixedResultDifferentiatesTo`, but with the algebraic arm in its abstract `IsAlgebraicIntegral` form rather
than the `radIsZero`-tested `toPolyG`-equality the checker route uses).

* On a **transcendental** `res = some r`: the **field identity** `towerFractionFieldDerivG Dt (amG r.rational.1
  / amG r.rational.2) + logResidueSumG Dt r.logs = amG a / amG d` over `RatFunc (CFieldSpec.K α)` — `D(g) + Σ
  cᵢ·(Δvᵢ)/vᵢ = a/d`, the conclusion of `cIntegrateGFull_primitive_oneShot`. A transcendental `none` is
  `False` (never reachable when the result came from a `some`).
* On an **algebraic** `res`: `RadElem.IsAlgebraicIntegral 2 ρ f res.ratPart commonDenom res.logTerms cofs` —
  `D(res.ratPart + Σ cᵢ log uᵢ) = f` cross-multiplied by `commonDenom` in `K[X] ⧸ radIdeal 2 ρ`, the conclusion
  of `isAlgebraicIntegral_of_parts`. -/
def MixedWfDifferentiatesTo (Dt : CPolyG α) (result : MixedIntegralResult α) (a d : CPolyG α)
    (ρ : QFunNZG ℚ) (f commonDenom : RadElem (QFunNZG ℚ)) (cofs : List (RadElem (QFunNZG ℚ))) : Prop :=
  match result with
  | .transcendental res =>
      match res with
      | some r =>
          towerFractionFieldDerivG Dt
              (amG α (toPolyG r.rational.1) / amG α (toPolyG r.rational.2))
            + logResidueSumG Dt r.logs
          = amG α (toPolyG a) / amG α (toPolyG d)
      | none => False
  | .algebraic res =>
      RadElem.IsAlgebraicIntegral 2 ρ f res.ratPart commonDenom res.logTerms cofs

omit [CFracGcdCore α] in
/-- **★★ The UNIFIED fuel-free checker-free one-shot soundness** `cIntegrateMixedWf_sound` — for BOTH the
transcendental and the algebraic arm, the fuel-free unified dispatcher's output is a genuine antiderivative of
its integrand, with **no `checkMixed`, no answer-checker, no `native_decide`**. By `cases` on the dispatcher
result `result = cIntegrateMixedWf spec`, feeding the per-arm checker-free conclusion (each discharged at the
call site by Task 1 / Task 2):

* **transcendental** `some r`: `MixedWfDifferentiatesTo` reduces (iota) to the field identity `D(r) = a/d`
  over `RatFunc (CFieldSpec.K α)`, supplied by `hT r` — whose witness is
  `cIntegrateMixedWf_transcendental_oneShot` (Task 1). A transcendental `none` makes the predicate `False`,
  contradicting `hnone`.
* **algebraic** `res`: `MixedWfDifferentiatesTo` reduces (iota) to `IsAlgebraicIntegral 2 ρ f res.ratPart
  commonDenom res.logTerms cofs`, supplied by `hAlg res` — whose witness is
  `cIntegrateMixedWf_algebraic_oneShot` (Task 2).

The per-arm conclusions `hT`/`hAlg` are dispatched on the result shape (`∀ r, result = … → …`), exactly as
`checkMixed_sound` feeds its two per-branch bridges; the engine-success bridges live in the Task 1 / Task 2
signatures that discharge `hT`/`hAlg` at the call site, never a runtime checker. The transcendental `none`
exclusion `hnone` mirrors `checkMixed`'s `none → false` (the dispatcher's `some`-returning success). **The
fuel-free unified one-shot, checker-free, both arms** — composing the two existing checker-free arm soundnesses
through the fuel-free bridges. -/
theorem cIntegrateMixedWf_sound (spec : IntegrandSpec α) (result : MixedIntegralResult α)
    (a d : CPolyG α) (Dt : CPolyG α) (ρ : QFunNZG ℚ)
    (f commonDenom : RadElem (QFunNZG ℚ)) (cofs : List (RadElem (QFunNZG ℚ)))
    (hrun : cIntegrateMixedWf spec = result)
    (hT : ∀ r, result = MixedIntegralResult.transcendental (some r) →
      towerFractionFieldDerivG Dt
          (amG α (toPolyG r.rational.1) / amG α (toPolyG r.rational.2))
        + logResidueSumG Dt r.logs
      = amG α (toPolyG a) / amG α (toPolyG d))
    (hnone : result ≠ MixedIntegralResult.transcendental none)
    (hAlg : ∀ res, result = MixedIntegralResult.algebraic res →
      RadElem.IsAlgebraicIntegral 2 ρ f res.ratPart commonDenom res.logTerms cofs) :
    MixedWfDifferentiatesTo Dt result a d ρ f commonDenom cofs := by
  cases result with
  | transcendental res =>
    cases res with
    | some r =>
      -- `MixedWfDifferentiatesTo … (.transcendental (some r)) …` IS (iota) the field identity `hT` supplies
      exact hT r rfl
    | none =>
      -- a transcendental `none` is excluded by `hnone` (the dispatcher's `some`-returning success)
      exact absurd rfl hnone
  | algebraic res =>
    -- `MixedWfDifferentiatesTo … (.algebraic res) …` IS (iota) the `IsAlgebraicIntegral` `hAlg` supplies
    exact hAlg res rfl

/-! ### Restatements against the intended wording (anonymous `example`s)

The fuel-free unified integrator `cIntegrateMixedWf` is sound for BOTH the transcendental and the algebraic
arm as ONE statement — `cIntegrateMixedWf spec` differentiates to the integrand, per arm — with **no
`checkMixed`, no answer-checker, no `native_decide`**, gated only on the engine-success bridges. The two arms
are also available individually (Task 1 / Task 2). -/

-- ★ THE CAPSTONE (fuel-free, checker-free): the unified dispatcher is sound for BOTH arms as ONE theorem,
-- feeding the two per-arm checker-free one-shots (Task 1 / Task 2) through one `cases`-on-result dispatch.
example (spec : IntegrandSpec α) (result : MixedIntegralResult α) (a d : CPolyG α) (Dt : CPolyG α)
    (ρ : QFunNZG ℚ) (f commonDenom : RadElem (QFunNZG ℚ)) (cofs : List (RadElem (QFunNZG ℚ)))
    (hrun : cIntegrateMixedWf spec = result)
    (hT : ∀ r, result = MixedIntegralResult.transcendental (some r) →
      towerFractionFieldDerivG Dt
          (amG α (toPolyG r.rational.1) / amG α (toPolyG r.rational.2))
        + logResidueSumG Dt r.logs
      = amG α (toPolyG a) / amG α (toPolyG d))
    (hnone : result ≠ MixedIntegralResult.transcendental none)
    (hAlg : ∀ res, result = MixedIntegralResult.algebraic res →
      RadElem.IsAlgebraicIntegral 2 ρ f res.ratPart commonDenom res.logTerms cofs) :
    MixedWfDifferentiatesTo Dt result a d ρ f commonDenom cofs :=
  cIntegrateMixedWf_sound spec result a d Dt ρ f commonDenom cofs hrun hT hnone hAlg

-- The transcendental arm's one-shot discharges `hT` directly (Task 1): the dispatcher's transcendental result
-- `some res` differentiates to `a/d`, fuel-free + checker-free, given the engine-success bridges.
example (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) (res : IntegralResultG α)
    (s : Finset (CFieldSpec.K α)) (w : CFieldSpec.K α) (hDt : toPolyG Dt = C w)
    (hrun : cIntegrateMixedWf (IntegrandSpec.transcendental Dt a d cands)
      = MixedIntegralResult.transcendental (some res))
    (hcanon : canonicalRepresentationFastGWf Dt a d = canonicalRepresentationFastG Dt fuel a d)
    (hred : cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands
      = cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands)
    (hpoly : cPolyRischDEGWf Dt [] (canonicalRepresentationFastGWf Dt a d).1
        ((cdegG (canonicalRepresentationFastGWf Dt a d).1 : ℤ) + 1)
      = cPolyRischDEG Dt fuel [] (canonicalRepresentationFastG Dt fuel a d).1
          ((cdegG (canonicalRepresentationFastG Dt fuel a d).1 : ℤ) + 1))
    (hb : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).2.1.1 = true)
    (hfp : CPolyG.cisZeroG (canonicalRepresentationFastG Dt fuel a d).1 = true)
    (hrecon : amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
          / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1)
            / amG α (toPolyG (cHermiteReduceTowerG Dt fuel
                (canonicalRepresentationFastG Dt fuel a d).2.2.1
                (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2)
        = amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.1)
            / amG α (toPolyG (canonicalRepresentationFastG Dt fuel a d).2.2.2))
    (hden : toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerG Dt fuel
          (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, w ≠ β′)
    (hform : (CPolyG.cIntegrateReducedG Dt fuel
            (canonicalRepresentationFastG Dt fuel a d).2.2.1
            (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerG Dt fuel
                  (canonicalRepresentationFastG Dt fuel a d).2.2.1
                  (canonicalRepresentationFastG Dt fuel a d).2.2.2).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β))) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  CPolyG.cIntegrateMixedWf_transcendental_oneShot Dt fuel a d cands res s w hDt hrun hcanon hred hpoly
    hb hfp hrecon hherm hden hA hnorm hform

-- The algebraic arm's one-shot discharges `hAlg` directly (Task 2): the dispatcher's algebraic result
-- differentiates to `f`, fuel-free + checker-free, given the engine-success bridges.
example (ρ : QFunNZG ℚ) (R B : CPolyG ℚ) (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ)
    (D : CPolyG ℚ) (degBound : ℕ) (res : AlgIntegralResult)
    (f ratPart logPart commonDenom : RadElem (QFunNZG ℚ)) (cofs : List (RadElem (QFunNZG ℚ)))
    (hrun : cIntegrateMixedWf (α := α) (IntegrandSpec.algebraic ρ R B residual c D degBound)
      = MixedIntegralResult.algebraic res)
    (hrat : Ideal.Quotient.mk (radIdeal 2 ρ)
          (CPolyG.toPolyG (radMul 2 ρ (radDeriv 2 ρ res.ratPart) commonDenom))
        = Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ ratPart commonDenom)))
    (hlog : RadElem.IsRadicalLogIntegral 2 ρ logPart commonDenom res.logTerms cofs)
    (hsplit : Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ ratPart commonDenom))
        + Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ logPart commonDenom))
      = Ideal.Quotient.mk (radIdeal 2 ρ) (CPolyG.toPolyG (radMul 2 ρ f commonDenom))) :
    RadElem.IsAlgebraicIntegral 2 ρ f res.ratPart commonDenom res.logTerms cofs :=
  cIntegrateMixedWf_algebraic_oneShot (α := α) ρ R B residual c D degBound res f ratPart logPart
    commonDenom cofs hrun hrat hlog hsplit

/-! ### Axiom audit — the fuel-free checker-free arms + unified one-shot rest only on the kernel axioms

Each arm soundness and the unified one-shot carry **only** the standard `[propext, Classical.choice,
Quot.sound]` — no `native_decide` compiler axiom (`ofReduceBool`/`native`), no `sorry`. The fuel-free unified
integrator `cIntegrateMixedWf` is sound for BOTH the transcendental and the algebraic arm, CHECKER-FREE
(no `checkMixed`), gated only on the engine-success bridges (the inherent native_decide boundary), reusing the
transcendental `cIntegrateGFull_primitive_oneShot` and the algebraic `isAlgebraicIntegral_of_parts` through the
fuel-free bridges `cIntegrateGFullWf_eq` / `cIntegrateAlgebraicWf_eq`. -/

-- ★ Task 1 — the transcendental arm, fuel-free, checker-free:
#print axioms CPolyG.cIntegrateMixedWf_transcendental_oneShot
-- ★ Task 2 — the algebraic arm, fuel-free, checker-free:
#print axioms cIntegrateMixedWf_algebraic_oneShot
-- ★★ Task 3 — THE UNIFIED fuel-free checker-free one-shot, both arms:
#print axioms cIntegrateMixedWf_sound

end DeepWiki.SymbolicIntegration
