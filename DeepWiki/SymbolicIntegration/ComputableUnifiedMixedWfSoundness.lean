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

end DeepWiki.SymbolicIntegration
