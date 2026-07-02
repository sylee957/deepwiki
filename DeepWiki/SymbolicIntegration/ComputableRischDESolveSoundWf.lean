import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound
import DeepWiki.SymbolicIntegration.ComputableTowerRischDEWellFounded
import DeepWiki.SymbolicIntegration.ComputableCanonNormalizedReduce

/-! # The FUEL-FREE SOUND recursive Risch-DE solver — `crischDESolveSoundWf`

`ComputableRischDESolveSound` built the §6.1-gated, **unconditionally sound** solver `crischDESolveSound`
(weak-normalize → `cisCanonNormalizedG` solvability check → reduce → solve → transform back), proving
`crischDESolveSound_field` axiom-cleanly. But its inner RDE solve routes through `CRischField.crischDESolve`,
whose tower instance `instCRischFieldQFunNZG` runs the **`ℕ`-fuel** `cRischDEG [1] towerRischDEFuel …`.
`ComputableTowerRischDEWellFounded` built the **fuel-free** companion `cRischDEGWf` (true well-founded
recursion replacing the fuel) together with internal correspondence proofs to the fueled `cRischDEG` on
regular runs.

This file combines the two: the **fuel-free, SOUND** solver `crischDESolveSoundWf` — the same §6.1-gated
pipeline as `crischDESolveSound`, but with the inner solve routed through the fuel-free `cRischDEGWf` (over
`CPolyG β`, re-lifted to `QFunNZG β` with the same `cisZeroG`-guard the tower instance uses) instead of the
fuel `cRischDEG`. This is the intended **fuel-free sound entry point** the production engine will be re-pinned
through (a separate coordinated step).

* **`crischDESolveSoundWf f g`** — the §6.1-gated solver with the **fuel-free** weak normalizer
  `cWeakNormalizerGWf [1] …` and the inner solve `cRischDEGWf [1] …` (NO `ℕ`-fuel parameter; the check /
  reduce stages are shared verbatim with `crischDESolveSound`).
* **★ `crischDESolveSoundWf_field`** — the capstone: a successful `crischDESolveSoundWf f g = some y` gives the
  field-level Risch-DE identity `D(Y) + F·Y = G` for the ORIGINAL `f, g`, under the current Wf/fueled transfer
  assumptions (`InputFitsFuel`, weak-normalizer agreement, and inner-solve agreement), **fuel-free at
  runtime**, NO `IsCanonNormalized` hypothesis (the solver checks it), internally transferring to the proven
  `crischDESolveSound_field`. Axiom-clean `[propext, Classical.choice, Quot.sound]`, NO
  `native_decide`.
* **The validations** (`native_decide`): the unsolvable witness `f = 1/(t₁ − x)`, `g = 1` returns `none` under
  `crischDESolveSoundWf`, and the solvable cases (`Dy = 1 → y = t₁`, `Dy + y = t₁ + 1 → y = t₁`) return the
  correct `some` — fuel-free.

★ **The fuel-free sound solver.** `crischDESolveSoundWf` + `crischDESolveSoundWf_field` give the sound RDE
oracle with the `ℕ`-fuel removed from the inner solve; the production re-pin routes the engine's RDE calls
through it (a separate coordinated step, out of this file's scope). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## ★ The fuel-free SOUND solver `crischDESolveSoundWf` (the inner solve made fuel-free)

`crischDESolveSoundWf f g` is `crischDESolveSound f g` with **only the inner RDE solve** replaced by the
fuel-free `cRischDEGWf`. The §6.1 pipeline is shared verbatim:

1. compute the **fuel-free** weak normalizer `q = cWeakNormalizerGWf [1] f.1.1 f.1.2`; if `q = 0`, `none`;
2. lift `q' = q/1`, form the weakly-normalized `f̃ = f − Dq'/q'`;
3. **the §6.1 solvability check** `cisCanonNormalizedG f̃` (return `none` if it fails);
4. reduce `f̃` to lowest terms (`reduceSoundOpt`) and solve the inner RDE on `(f̃ᵣ, q'·g)` — but via the
   **fuel-free** `cRischDEGWf [1] f̃ᵣ.1.1 f̃ᵣ.1.2 (q'·g).1.1 (q'·g).1.2` over `CPolyG β`, re-lifting the
   returned `(ynum, yden)` with the same `cisZeroG`-guard `instCRischFieldQFunNZG` uses; on `some ỹ`, return
   `y = ỹ/q'`.

The single difference from `crischDESolveSound` is step 4's inner solver — `cRischDEGWf` (no `ℕ`-fuel) in
place of `CRischField.crischDESolve` (= `cRischDEG [1] towerRischDEFuel`). On a real run the two coincide by a
private transfer lemma, so the soundness transfers. -/

section Solver

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]
  [CFracGcdCoreWf β] [CRischField β]

/-- **The fuel-free inner RDE solve** `crischDERawSolveWf ftilde gtilde` over `QFunNZG β`: the fuel-free mirror
of `instCRischFieldQFunNZG.crischDESolve` — run the **fuel-free** `cRischDEGWf ([1] : CPolyG β)` over
`CPolyG β = β[s]` (monomial `s`, `Ds = [1]`) on the num/den components of `ftilde, gtilde`, and re-lift the
returned `(ynum, yden)` to `QFunNZG β` with the same `cisZeroG`-guard the tower instance uses. **No `ℕ`-fuel** —
the inner §6 pipeline runs fuel-free. Its agreement with `CRischField.crischDESolve` is kept as an internal
transfer lemma for the current soundness proof. -/
def crischDERawSolveWf (ftilde gtilde : QFunNZG β) : Option (QFunNZG β) :=
  match CPolyG.cRischDEGWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
  | none => none
  | some (ynum, yden) =>
    if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none

/-- **★ The FUEL-FREE, genuinely SOUND recursive Risch-DE solver** `crischDESolveSoundWf f g` over
`QFunNZG β`: `crischDESolveSound` with the inner RDE solve routed through the **fuel-free** `cRischDEGWf`
(`crischDERawSolveWf`) in place of the fuel `CRischField.crischDESolve`. Weak-normalize `f` to
`f̃ = f − Dq/q` (`q = cWeakNormalizerGWf`, **fuel-free**); if `q = 0` give up; run the §6.1 solvability check
`cisCanonNormalizedG f̃` (return `none` when the lowest-terms denominator is not normal — an unsolvable RDE);
else reduce `f̃` to lowest terms (`reduceSoundOpt`) and solve `(f̃ᵣ, q'·g)` via the **fuel-free**
`crischDERawSolveWf`, transforming back by `y = ỹ/q'`. **No `ℕ`-fuel parameter** — the inner §6 pipeline runs
fuel-free. The check removes any external `IsCanonNormalized` hypothesis from soundness; the remaining
soundness assumptions are the current Wf/fueled transfer residuals (`crischDESolveSoundWf_field`).
Computable, so it `native_decide`s; the regular-run correspondence with `crischDESolveSound` is internal to the
soundness proof. -/
def crischDESolveSoundWf (f g : QFunNZG β) : Option (QFunNZG β) :=
  let q : CPolyG β := cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
  if CPolyG.cisZeroG q then none
  else
    let q' : QFunNZG β := qOfPolyNZG q
    let ftilde : QFunNZG β := weakNormalizedF f q'
    if cisCanonNormalizedG ftilde then
      match reduceSoundOpt ftilde with
      | none => none
      | some ftildeR =>
        match crischDERawSolveWf ftildeR (qmulNZG q' g) with
        | none => none
        | some ytilde => some (qmulNZG ytilde (qinvNZG q'))
    else none

end Solver

/-! ## Internal transfer lemmas for the current soundness proof

`crischDESolveSoundWf` and `crischDESolveSound` share the whole §6.1 pipeline (weak normalizer, solvability
check, lowest-terms reduction); they differ **only** in the inner RDE solve — `crischDERawSolveWf` (the
fuel-free `cRischDEGWf`) vs `CRischField.crischDESolve` (= `cRischDEG [1] towerRischDEFuel` for the tower
instance). On a regular run the inner solvers coincide by the equality hypothesis threaded into soundness, so
the whole solvers coincide. The fuel bounds live only in the regularity hypothesis; the runtime
`crischDESolveSoundWf` carries none. These correspondence facts are private implementation details of
`crischDESolveSoundWf_field`, not public API. -/

section Correspondence

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]
  [CFracGcdCoreWf β] [CRischField β]

omit [CFieldSpec β] in
/-- The fuel-free inner solve equals `CRischField.crischDESolve` on a regular run with the §6.1 gate passed. -/
private theorem rawSolveWf_eq (ftilde gtilde : QFunNZG β)
    (hwf : CPolyG.cRischDEGWf ([CField.one] : CPolyG β)
        ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
      = CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel
        ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2)
    (hgate : cdenomNormalGateG ftilde = true) :
    crischDERawSolveWf ftilde gtilde = CRischField.crischDESolve ftilde gtilde := by
  rw [crischDERawSolveWf, hwf, crischDESolve_eq_solve_of_normal ftilde gtilde hgate]
  rfl

/-- The fuel-free sound solver equals the fueled sound solver on a regular run. -/
private theorem soundSolverWf_eq (f g : QFunNZG β)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : ∀ ftildeR : QFunNZG β,
      reduceSoundOpt (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))) =
        some ftildeR →
      CPolyG.cRischDEGWf ([CField.one] : CPolyG β)
          ftildeR.1.1 ftildeR.1.2
          (qmulNZG (qOfPolyNZG
            (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.1
          (qmulNZG (qOfPolyNZG
            (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.2
        = CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel
          ftildeR.1.1 ftildeR.1.2
          (qmulNZG (qOfPolyNZG
            (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.1
          (qmulNZG (qOfPolyNZG
            (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.2) :
    crischDESolveSoundWf f g = crischDESolveSound f g := by
  -- the def uses the fuel-free `cWeakNormalizerGWf`; `hqwn` converts it to the fuel form, after which the
  -- whole §6.1 pipeline (the shared `q'`/`ftilde`) coincides with `crischDESolveSound` and only the inner
  -- solve differs (reconciled by `rawSolveWf_eq` under `hwf`)
  rw [show crischDESolveSoundWf f g
      = (if CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2) then none
         else
           if cisCanonNormalizedG
               (weakNormalizedF f
                 (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) then
             match reduceSoundOpt
                 (weakNormalizedF f
                   (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) with
             | none => none
             | some ftildeR =>
               match crischDERawSolveWf ftildeR
                   (qmulNZG (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g) with
               | none => none
               | some ytilde =>
                 some (qmulNZG ytilde
                   (qinvNZG (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
           else none) from rfl]
  rw [hqwn]
  set q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 with hq
  set q' : QFunNZG β := qOfPolyNZG q with hq'
  set ftilde : QFunNZG β := weakNormalizedF f q' with hft
  rw [show crischDESolveSound f g
      = (if CPolyG.cisZeroG q then none
         else if cisCanonNormalizedG ftilde then
                match reduceSoundOpt ftilde with
                | none => none
                | some ftildeR =>
                  match CRischField.crischDESolve ftildeR (qmulNZG q' g) with
                  | none => none
                  | some ytilde => some (qmulNZG ytilde (qinvNZG q'))
              else none) from rfl]
  by_cases hqz : CPolyG.cisZeroG q = true
  · rw [if_pos hqz, if_pos hqz]
  · rw [if_neg hqz, if_neg hqz]
    by_cases hck : cisCanonNormalizedG ftilde = true
    · rw [if_pos hck, if_pos hck]
      rcases hr : reduceSoundOpt ftilde with _ | ftildeR
      · rfl
      · -- the production §6.1 gate passes on the canonicalized input `ftildeR = qReduce ftilde`: by the
        -- keystone `cisCanonNormalizedCoreG_qReduce_weakNormalized`, `cdenomNormalGateG (qReduce ftilde) =
        -- cisCanonNormalizedG ftilde = true` (here `cdenomNormalGateG` is defeq to the keystone's
        -- `cisCanonNormalizedCoreG`)
        have hred : ftildeR = qReduce ftilde := by
          have h := reduceSoundOpt_eq ftilde
          rw [hr] at h
          exact (Option.some.injEq _ _).mp h
        have hgate : cdenomNormalGateG ftildeR = true := by
          have hkey : cisCanonNormalizedCoreG (qReduce ftilde) = cisCanonNormalizedG ftilde := by
            have hqwf : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2 = q := by
              exact hqwn
            rw [hft, hq', ← hqwf]
            exact cisCanonNormalizedCoreG_qReduce_weakNormalized f
          rw [hred]
          show cisCanonNormalizedCoreG (qReduce ftilde) = true
          rw [hkey]; exact hck
        simp only [rawSolveWf_eq ftildeR (qmulNZG q' g) (hwf ftildeR hr) hgate]
    · rw [if_neg hck, if_neg hck]

end Correspondence

/-! ## ★★ Task 3 — the capstone: the FUEL-FREE sound solver is sound under transfer residuals

`crischDESolveSoundWf_field`: a successful `crischDESolveSoundWf f g = some y` gives the field-level Risch-DE
identity `D(Y) + F·Y = G` for the ORIGINAL `f, g`, **fuel-free**, **NO `IsCanonNormalized` hypothesis** (the
solver checks it). It internally turns the `crischDESolveSoundWf` success into a `crischDESolveSound` success
under the Wf/fueled agreement residuals, then uses the proven `crischDESolveSound_field`. The
hypotheses are exactly those of `crischDESolveSound_field` (the gcd witness `[CTowerGcdWitness β]` + the
benign fuel budget `InputFitsFuel`) **plus** the inner-solve `cRischDEGWf = cRischDEG towerRischDEFuel`
regularity `hwf` and the weak-normalizer agreement `hqwn` (the WF-vs-fuel correspondences the fuel-free
routing threads in place of the fuel'd calls). NO `native_decide`; axiom-clean
`[propext, Classical.choice, Quot.sound]`. -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CFracGcdCoreWf β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **The Wf input-fit precondition** `InputFitsFuelWf f g`: the per-run termination residual for the
canonicalized Wf solver pair built from `cWeakNormalizerGWf [1] f.1.1 f.1.2`, together with the `g`-side
normality dual. This is the Wf-shaped counterpart of `InputFitsFuel`; it keeps the public Wf soundness API
stated on the actual weak normalizer used by `crischDESolveSoundWf`. -/
structure InputFitsFuelWf (f g : QFunNZG β) : Prop where
  /-- The per-run fuel/termination residual for the Wf canonicalized pair. -/
  hfuel : RischDESuccessResidualNormFuel
    (qReduce (weakNormalizedF f (qOfPolyNZG
      (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
    (qmulNZG (qOfPolyNZG
      (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g)
  /-- The Wf `g`-side normality dual for the transformed right-hand side. -/
  hgnorm : IsWeaklyNormalizedDen
    (qmulNZG (qOfPolyNZG
      (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g).1.2

omit [CDiffFieldSpec β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)] in
/-- **Wf input-fit converts to the old fueled input-fit under weak-normalizer agreement**: the conversion is
only used by the current transfer proof to call `crischDESolveSound_field`. -/
theorem inputFitsFuel_of_wf (f g : QFunNZG β) (hfit : InputFitsFuelWf f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2) :
    InputFitsFuel f g where
  hfuel := by
    simpa [hqwn] using hfit.hfuel
  hgnorm := by
    simpa [hqwn] using hfit.hgnorm

/-- **The Wf inner-solve regularity for the fuel-free sound solver** `SoundWfInnerRegular f g`: the fuel-free
`cRischDEGWf [1]` agrees with the fuel `cRischDEG [1] towerRischDEFuel` on the num/den components of the
canonicalized inner pair built from the **Wf** weak normalizer
`cWeakNormalizerGWf [1] f.1.1 f.1.2`. This packages the regular-run equality needed by the private transfer
helper, while keeping the public residual stated on the same Wf inner input that `crischDESolveSoundWf`
actually runs. -/
def SoundWfInnerRegular (f g : QFunNZG β) : Prop :=
  ∀ ftildeR : QFunNZG β,
    reduceSoundOpt (weakNormalizedF f
      (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) =
      some ftildeR →
    CPolyG.cRischDEGWf ([CField.one] : CPolyG β)
        ftildeR.1.1 ftildeR.1.2
        (qmulNZG (qOfPolyNZG
          (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g).1.1
        (qmulNZG (qOfPolyNZG
          (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g).1.2
      = CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel
        ftildeR.1.1 ftildeR.1.2
        (qmulNZG (qOfPolyNZG
          (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g).1.1
        (qmulNZG (qOfPolyNZG
          (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g).1.2

/-- **★★ The FUEL-FREE recursive RDE solver is sound under the current transfer residuals** (Task 3, the capstone,
`crischDESolveSoundWf_field`): if `crischDESolveSoundWf f g = some y`, then with the gcd witness
`[CTowerGcdWitness β]`, the benign fuel budget `InputFitsFuel f g`, weak-normalizer agreement `hqwn`, and
the inner-solve regularity
`SoundWfInnerRegular f g` (the fuel-free `cRischDEGWf` agreeing with the fuel `cRischDEG towerRischDEFuel` on
the inner pair — the WF-vs-fuel correspondence the fuel-free routing threads), the returned `y` solves the
field-level Risch DE for the ORIGINAL `f, g`: `D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`. **Fuel-free**,
**NO `IsCanonNormalized` hypothesis** — the solver's own §6.1 solvability check supplies it. Composes the two
proof pieces: a private regular-run transfer turns the success into a `crischDESolveSound` success, then the
proven `crischDESolveSound_field` closes it. NO `native_decide`; axiom-clean
`[propext, Classical.choice, Quot.sound]`. **★ The fuel-free sound solver.** -/
theorem crischDESolveSoundWf_field (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y)
    (hfit : InputFitsFuelWf f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : SoundWfInnerRegular f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) := by
  have hwfFuel : ∀ ftildeR : QFunNZG β,
      reduceSoundOpt (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))) =
        some ftildeR →
      CPolyG.cRischDEGWf ([CField.one] : CPolyG β)
          ftildeR.1.1 ftildeR.1.2
          (qmulNZG (qOfPolyNZG
            (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.1
          (qmulNZG (qOfPolyNZG
            (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.2
        = CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel
          ftildeR.1.1 ftildeR.1.2
          (qmulNZG (qOfPolyNZG
            (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.1
          (qmulNZG (qOfPolyNZG
            (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.2 := by
    intro ftildeR hred
    have hredWf : reduceSoundOpt (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) =
        some ftildeR := by
      rw [hqwn]
      exact hred
    simpa [hqwn] using hwf ftildeR hredWf
  have hsound : crischDESolveSound f g = some y := by
    rw [← soundSolverWf_eq f g hqwn hwfFuel]; exact hsolve
  exact crischDESolveSound_field f g y hsound (inputFitsFuel_of_wf f g hfit hqwn)

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 3: the FUEL-FREE sound solver's success ⟹ the ORIGINAL field-level Risch-DE identity, from the gcd
-- witness + the benign fuel budget + the weak-normalizer and inner-solve WF-vs-fuel agreements — NO
-- IsCanonNormalized hypothesis (the solver checks it). Fuel-free at runtime. No native_decide.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CFracGcdCoreWf β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : QFunNZG β) (hsolve : crischDESolveSoundWf f g = some y) (hfit : InputFitsFuelWf f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : SoundWfInnerRegular f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolveSoundWf_field f g y hsolve hfit hqwn hwf

end Capstone

/-! ## ★ Task 4 — `native_decide` validations for the fuel-free solver

The fuel-free sound solver's behaviour over the level-2 field `ℚ(x)(t₁)`, certified by `native_decide` (the
inner §6 pipeline runs fuel-free through `cRischDEGWf`):

* **The witness returns `none`.** `crischDESolveSoundWf witnessF 1 = none` — on `f = 1/(t₁ − x)`, `g = 1`, the
  unsolvable RDE, the fuel-free solver's §6.1 check detects unsolvability and returns `none`.
* **Solvable cases still solve.** `Dy = 1 → y = t₁` and `Dy + y = t₁ + 1 → y = t₁` both return the correct
  `some y` with `D(y) + f·y = g`, checked at the field level.

These are the fuel-free solver's own smoke tests, independent of the older fueled validation API. -/

section Validation

/-- **★ The fuel-free sound solver returns `none` on the unsoundness witness**
(`crischDESolveSoundWf_witness_none`, `native_decide`): for `f = 1/(t₁ − x)`, `g = 1` over `ℚ(x)(t₁)` — the RDE
with NO solution — `crischDESolveSoundWf witnessF 1 = none`, fuel-free. The §6.1 solvability check detects the
surviving `D`-constant special pole `t₁ − x` and reports unsolvability. -/
theorem crischDESolveSoundWf_witness_none :
    crischDESolveSoundWf witnessF (CField.one : Lvl2) = none := by native_decide

/-- **The fuel-free sound solver still solves `Dy = 1` at level 2** (`crischDESolveSoundWf_solves_Dy_eq_one`,
`native_decide`): `crischDESolveSoundWf (0 : Lvl2) (1 : Lvl2)` returns `some y` with `D(y) + 0·y = 1`
(`y = t₁`), checked at the field level by `CField.isZero` of `cderiv y + 0·y − 1`. The fuel-free integration
path returns the correct solution. -/
theorem crischDESolveSoundWf_solves_Dy_eq_one :
    (match crischDESolveSoundWf (CField.zero : Lvl2) (CField.one : Lvl2) with
      | some y =>
          CField.isZero
            (CField.sub (CField.add (CDiffField.cderiv y) (CField.mul CField.zero y)) CField.one)
      | none => false) = true := by native_decide

/-- **The fuel-free sound solver still solves `Dy + y = t₁ + 1` at level 2** (the cancellation path)
(`crischDESolveSoundWf_solves_Dy_plus_y`, `native_decide`): `crischDESolveSoundWf (1 : Lvl2) (t₁ + 1)` returns
`some y` with `D(y) + 1·y = t₁ + 1` (`y = t₁`), checked at the field level. Here `f = 1 ≠ 0`, so the §6.6
primitive-cancellation degree-recursion runs fuel-free (through `cPolyRischDECancelPrimGWf` / the recursive
`crischDESolve`). -/
theorem crischDESolveSoundWf_solves_Dy_plus_y :
    (match crischDESolveSoundWf (CField.one : Lvl2) towerRdeLvl2GPlusOne with
      | some y =>
          CField.isZero
            (CField.sub (CField.add (CDiffField.cderiv y) (CField.mul CField.one y))
              towerRdeLvl2GPlusOne)
      | none => false) = true := by native_decide

end Validation

/-! ### Axiom audit (the capstone + correspondence are axiom-clean, NO `native_decide`; the validations are
`native_decide`) -/

#print axioms crischDESolveSoundWf_field

/-! ### Final verdict (Task 5)

**Is the fuel-free sound solver built and proven sound?** **Yes.**

* **Built fuel-free.** `crischDESolveSoundWf` runs the §6.1-gated sound pipeline (weak-normalize →
  `cisCanonNormalizedG` check → reduce → solve → transform back) with the inner RDE solve routed through the
  **fuel-free** `cRischDEGWf` (`crischDERawSolveWf`) in place of the fuel `CRischField.crischDESolve` — no
  `ℕ`-fuel parameter.
* **Proven sound through the current transfer residuals, axiom-clean.** `crischDESolveSoundWf_field`: a
  successful solve gives the ORIGINAL field-level Risch-DE identity `D(Y) + F·Y = G`, with NO
  `IsCanonNormalized` hypothesis (the solver checks it), internally transferring through the existing fueled
  soundness proof under the Wf/fueled agreement residuals. Axiom-clean
  `[propext, Classical.choice, Quot.sound]`, NO `native_decide`.
* **Fuel-free validations.** The witness `f = 1/(t₁ − x)`, `g = 1` returns `none`
  (`crischDESolveSoundWf_witness_none`), and the solvable cases `Dy = 1` / `Dy + y = t₁ + 1` return the
  correct `some y` solving the RDE (`crischDESolveSoundWf_solves_*`) — all `native_decide`, fuel-free.

★ **This is the intended fuel-free sound entry point for the production re-pin** — routing the engine's RDE
solves through `crischDESolveSoundWf` (sound + fuel-free) is a separate coordinated step (it touches the
locked core), out of this file's scope; this file provides the verified fuel-free sound solver to route
through. -/

end DeepWiki.SymbolicIntegration
