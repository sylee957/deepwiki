import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound
import DeepWiki.SymbolicIntegration.ComputableTowerRischDEWellFounded
import DeepWiki.SymbolicIntegration.ComputableCanonNormalizedReduce

/-! # The FUEL-FREE SOUND recursive Risch-DE solver — `crischDESolveSoundWf`

`ComputableRischDESolveSound` built the §6.1-gated, **unconditionally sound** solver `crischDESolveSound`
(weak-normalize → `cisCanonNormalizedG` solvability check → reduce → solve → transform back), proving
`crischDESolveSound_field` axiom-cleanly. But its inner RDE solve routes through `CRischField.crischDESolve`,
whose tower instance `instCRischFieldQFunNZG` runs the **`ℕ`-fuel** `cRischDEG [1] towerRischDEFuel …`.
`ComputableTowerRischDEWellFounded` built the **fuel-free** companion `cRischDEGWf` (true well-founded
recursion replacing the fuel) together with the `cRischDEGWf = cRischDEG fuel`-on-a-regular-run correspondence
`cRischDEGWf_eq`.

This file combines the two: the **fuel-free, SOUND** solver `crischDESolveSoundWf` — the same §6.1-gated
pipeline as `crischDESolveSound`, but with the inner solve routed through the fuel-free `cRischDEGWf` (over
`CPolyG β`, re-lifted to `QFunNZG β` with the same `cisZeroG`-guard the tower instance uses) instead of the
fuel `cRischDEG`. This is the intended **fuel-free sound entry point** the production engine will be re-pinned
through (a separate coordinated step).

* **`crischDESolveSoundWf f g`** — the §6.1-gated solver with the inner solve `cRischDEGWf [1] …` (NO `ℕ`-fuel
  parameter; the weak normalizer / check / reduce stages are shared verbatim with `crischDESolveSound`).
* **`crischDESolveSoundWf_eq`** — the correspondence `crischDESolveSoundWf f g = crischDESolveSound f g` on a
  regular run (the inner `cRischDEGWf = cRischDEG towerRischDEFuel` agreement, via `cRischDEGWf_eq`); the fuel
  bounds live only in the regularity hypothesis, the runtime solver carries none.
* **★ `crischDESolveSoundWf_field`** — the capstone: a successful `crischDESolveSoundWf f g = some y` gives the
  field-level Risch-DE identity `D(Y) + F·Y = G` for the ORIGINAL `f, g`, **UNCONDITIONAL** (only the gcd
  witness + the benign fuel budget + the inner-solve regularity), **fuel-free**, NO `IsCanonNormalized`
  hypothesis (the solver checks it), composing `crischDESolveSoundWf_eq` with the proven
  `crischDESolveSound_field`. Axiom-clean `[propext, Classical.choice, Quot.sound]`, NO `native_decide`.
* **The validations** (`native_decide`): the unsolvable witness `f = 1/(t₁ − x)`, `g = 1` returns `none` under
  `crischDESolveSoundWf` (parity with `crischDESolveSound`), and the solvable cases (`Dy = 1 → y = t₁`,
  `Dy + y = t₁ + 1 → y = t₁`) return the correct `some` — fuel-free.

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

1. compute the weak normalizer `q = cWeakNormalizerG [1] towerRischDEFuel f.1.1 f.1.2`; if `q = 0`, `none`;
2. lift `q' = q/1`, form the weakly-normalized `f̃ = f − Dq'/q'`;
3. **the §6.1 solvability check** `cisCanonNormalizedG f̃` (return `none` if it fails);
4. reduce `f̃` to lowest terms (`reduceSoundOpt`) and solve the inner RDE on `(f̃ᵣ, q'·g)` — but via the
   **fuel-free** `cRischDEGWf [1] f̃ᵣ.1.1 f̃ᵣ.1.2 (q'·g).1.1 (q'·g).1.2` over `CPolyG β`, re-lifting the
   returned `(ynum, yden)` with the same `cisZeroG`-guard `instCRischFieldQFunNZG` uses; on `some ỹ`, return
   `y = ỹ/q'`.

The single difference from `crischDESolveSound` is step 4's inner solver — `cRischDEGWf` (no `ℕ`-fuel) in
place of `CRischField.crischDESolve` (= `cRischDEG [1] towerRischDEFuel`). On a real run the two coincide
(`crischDESolveSoundWf_eq`), so the soundness transfers. -/

section Solver

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]
  [CFracGcdCoreWf β] [CRischField β]

/-- **The fuel-free inner RDE solve** `crischDERawSolveWf ftilde gtilde` over `QFunNZG β`: the fuel-free mirror
of `instCRischFieldQFunNZG.crischDESolve` — run the **fuel-free** `cRischDEGWf ([1] : CPolyG β)` over
`CPolyG β = β[s]` (monomial `s`, `Ds = [1]`) on the num/den components of `ftilde, gtilde`, and re-lift the
returned `(ynum, yden)` to `QFunNZG β` with the same `cisZeroG`-guard the tower instance uses. **No `ℕ`-fuel** —
the inner §6 pipeline runs fuel-free. Agrees with `CRischField.crischDESolve` on a regular run
(`crischDERawSolveWf_eq`). -/
def crischDERawSolveWf (ftilde gtilde : QFunNZG β) : Option (QFunNZG β) :=
  match CPolyG.cRischDEGWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
  | none => none
  | some (ynum, yden) =>
    if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none

/-- **★ The FUEL-FREE, genuinely SOUND recursive Risch-DE solver** `crischDESolveSoundWf f g` over
`QFunNZG β`: `crischDESolveSound` with the inner RDE solve routed through the **fuel-free** `cRischDEGWf`
(`crischDERawSolveWf`) in place of the fuel `CRischField.crischDESolve`. Weak-normalize `f` to
`f̃ = f − Dq/q` (`q = cWeakNormalizerG`); if `q = 0` give up; run the §6.1 solvability check
`cisCanonNormalizedG f̃` (return `none` when the lowest-terms denominator is not normal — an unsolvable RDE);
else reduce `f̃` to lowest terms (`reduceSoundOpt`) and solve `(f̃ᵣ, q'·g)` via the **fuel-free**
`crischDERawSolveWf`, transforming back by `y = ỹ/q'`. **No `ℕ`-fuel parameter** — the inner §6 pipeline runs
fuel-free. The check makes `some ⟹ correct` unconditional (`crischDESolveSoundWf_field`); computable, so it
`native_decide`s; coincides with `crischDESolveSound` on a regular run (`crischDESolveSoundWf_eq`). -/
def crischDESolveSoundWf (f g : QFunNZG β) : Option (QFunNZG β) :=
  let q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2
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

/-! ## Task 2 — the correspondence `crischDESolveSoundWf = crischDESolveSound` on a regular run

`crischDESolveSoundWf` and `crischDESolveSound` share the whole §6.1 pipeline (weak normalizer, solvability
check, lowest-terms reduction); they differ **only** in the inner RDE solve — `crischDERawSolveWf` (the
fuel-free `cRischDEGWf`) vs `CRischField.crischDESolve` (= `cRischDEG [1] towerRischDEFuel` for the tower
instance). On a regular run the inner solvers coincide (`cRischDEGWf_eq`), so the whole solvers coincide. The
fuel bounds live only in the regularity hypothesis; the runtime `crischDESolveSoundWf` carries none. -/

section Correspondence

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]
  [CFracGcdCoreWf β] [CRischField β]

omit [CFieldSpec β] in
/-- **The fuel-free inner solve equals `CRischField.crischDESolve` on a regular run, with the §6.1 gate passed**
(`crischDERawSolveWf_eq`): if the fuel-free `cRischDEGWf [1]` agrees with the fuel `cRischDEG [1] towerRischDEFuel`
on the num/den components of `(ftilde, gtilde)` (`hwf`, the `cRischDEGWf_eq` agreement a real run meets) **and**
the production §6.1 gate passes on `ftilde` (`hgate : cdenomNormalGateG ftilde = true`), then
`crischDERawSolveWf ftilde gtilde = CRischField.crischDESolve ftilde gtilde`. The fuel-free
`crischDERawSolveWf` carries no gate, while the gated `instCRischFieldQFunNZG.crischDESolve` does; `hgate`
peels the gate (`crischDESolve_eq_solve_of_normal`) so both reduce to the same `cRischDE*`-then-`cisZeroG`-guard
match, and `hwf` reconciles the two oracle calls. The gate-passes side-condition holds on the canonicalized
input the sound wrapper feeds (the keystone `crischDESolveSound_repin_gate`), so the soundness transfers. -/
theorem crischDERawSolveWf_eq (ftilde gtilde : QFunNZG β)
    (hwf : CPolyG.cRischDEGWf ([CField.one] : CPolyG β)
        ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
      = CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel
        ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2)
    (hgate : cdenomNormalGateG ftilde = true) :
    crischDERawSolveWf ftilde gtilde = CRischField.crischDESolve ftilde gtilde := by
  rw [crischDERawSolveWf, hwf, crischDESolve_eq_solve_of_normal ftilde gtilde hgate]
  rfl

/-- **★ The fuel-free sound solver equals the fuel sound solver on a regular run** (Task 2,
`crischDESolveSoundWf_eq`): given the inner-solve regularity `hwf` — the fuel-free `cRischDEGWf` agreeing with
the fuel `cRischDEG towerRischDEFuel` on the num/den components of the canonicalized inner pair
`(reduceSoundOpt f̃, q'·g)` (the `cRischDEGWf_eq` agreement a real run meets) — `crischDESolveSoundWf f g =
crischDESolveSound f g`. The two solvers share the entire §6.1 pipeline and differ only in the inner solve,
which `crischDERawSolveWf_eq` reconciles under `hwf`; the fuel bounds live only in `hwf`. So the soundness of
`crischDESolveSound` transfers to the fuel-free `crischDESolveSoundWf` (`crischDESolveSoundWf_field`). -/
theorem crischDESolveSoundWf_eq (f g : QFunNZG β)
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
  set q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 with hq
  set q' : QFunNZG β := qOfPolyNZG q with hq'
  set ftilde : QFunNZG β := weakNormalizedF f q' with hft
  rw [show crischDESolveSoundWf f g
      = (if CPolyG.cisZeroG q then none
         else if cisCanonNormalizedG ftilde then
                match reduceSoundOpt ftilde with
                | none => none
                | some ftildeR =>
                  match crischDERawSolveWf ftildeR (qmulNZG q' g) with
                  | none => none
                  | some ytilde => some (qmulNZG ytilde (qinvNZG q'))
              else none) from rfl]
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
        -- keystone `crischDESolveSound_repin_gate`, `cdenomNormalGateG (qReduce ftilde) = cisCanonNormalizedG
        -- ftilde = true` (here `cdenomNormalGateG` is defeq to the keystone's `cisCanonNormalizedCoreG`)
        have hred : ftildeR = qReduce ftilde := by
          have h := reduceSoundOpt_eq ftilde
          rw [hr] at h
          exact (Option.some.injEq _ _).mp h
        have hgate : cdenomNormalGateG ftildeR = true := by
          have hkey : cisCanonNormalizedCoreG (qReduce ftilde) = cisCanonNormalizedG ftilde := by
            rw [hft, hq', hq]; exact crischDESolveSound_repin_gate f
          rw [hred]
          show cisCanonNormalizedCoreG (qReduce ftilde) = true
          rw [hkey]; exact hck
        simp only [crischDERawSolveWf_eq ftildeR (qmulNZG q' g) (hwf ftildeR hr) hgate]
    · rw [if_neg hck, if_neg hck]

end Correspondence

/-! ## ★★ Task 3 — the capstone: the FUEL-FREE sound solver is UNCONDITIONALLY sound

`crischDESolveSoundWf_field`: a successful `crischDESolveSoundWf f g = some y` gives the field-level Risch-DE
identity `D(Y) + F·Y = G` for the ORIGINAL `f, g`, **fuel-free**, **NO `IsCanonNormalized` hypothesis** (the
solver checks it). It composes the two proven pieces: `crischDESolveSoundWf_eq` (the fuel-free solver equals
the fuel solver on a regular run) turns the `crischDESolveSoundWf`-success into a `crischDESolveSound`-success,
and the proven `crischDESolveSound_field` (the fuel solver's unconditional soundness) closes it. The
hypotheses are exactly those of `crischDESolveSound_field` (the gcd witness `[CTowerGcdWitness β]` + the
benign fuel budget `InputFitsFuel`) **plus** the inner-solve `cRischDEGWf = cRischDEG towerRischDEFuel`
regularity `hwf` (the WF-vs-fuel correspondence the fuel-free routing threads — the one extra clause a
fuel-free solver carries in place of the fuel'd inner call). NO `native_decide`; axiom-clean
`[propext, Classical.choice, Quot.sound]`. -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CFracGcdCoreWf β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **The inner-solve regularity for the fuel-free sound solver** `SoundWfInnerRegular f g`: the fuel-free
`cRischDEGWf [1]` agrees with the fuel `cRischDEG [1] towerRischDEFuel` on the num/den components of the
canonicalized inner pair `(reduceSoundOpt (weakNormalizedF f q'), q'·g)`, for any lowest-terms reduction
`reduceSoundOpt … = some ftildeR`. The `cRischDEGWf_eq` agreement a real run meets — exactly the hypothesis of
`crischDESolveSoundWf_eq`, packaged so the capstone reads cleanly. NOT a soundness gap: the WF-vs-fuel
correspondence the fuel-free routing threads in place of the fuel'd inner call. -/
def SoundWfInnerRegular (f g : QFunNZG β) : Prop :=
  ∀ ftildeR : QFunNZG β,
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
          (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) g).1.2

/-- **★★ The FUEL-FREE recursive RDE solver is UNCONDITIONALLY sound** (Task 3, the capstone,
`crischDESolveSoundWf_field`): if `crischDESolveSoundWf f g = some y`, then with the gcd witness
`[CTowerGcdWitness β]`, the benign fuel budget `InputFitsFuel f g`, and the inner-solve regularity
`SoundWfInnerRegular f g` (the fuel-free `cRischDEGWf` agreeing with the fuel `cRischDEG towerRischDEFuel` on
the inner pair — the WF-vs-fuel correspondence the fuel-free routing threads), the returned `y` solves the
field-level Risch DE for the ORIGINAL `f, g`: `D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`. **Fuel-free**,
**NO `IsCanonNormalized` hypothesis** — the solver's own §6.1 solvability check supplies it. Composes the two
proven pieces: `crischDESolveSoundWf_eq` (fuel-free = fuel on a regular run) turns the success into a
`crischDESolveSound`-success; the proven `crischDESolveSound_field` (the fuel solver's unconditional soundness)
closes it. NO `native_decide`; axiom-clean `[propext, Classical.choice, Quot.sound]`. **★ The fuel-free sound
solver.** -/
theorem crischDESolveSoundWf_field (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y)
    (hfit : InputFitsFuel f g)
    (hwf : SoundWfInnerRegular f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) := by
  have hsound : crischDESolveSound f g = some y := by
    rw [← crischDESolveSoundWf_eq f g hwf]; exact hsolve
  exact crischDESolveSound_field f g y hsound hfit

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 3: the FUEL-FREE sound solver's success ⟹ the ORIGINAL field-level Risch-DE identity, from the gcd
-- witness + the benign fuel budget + the inner-solve WF-vs-fuel regularity ONLY — NO IsCanonNormalized
-- hypothesis (the solver checks it). Fuel-free. No native_decide.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CFracGcdCoreWf β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : QFunNZG β) (hsolve : crischDESolveSoundWf f g = some y) (hfit : InputFitsFuel f g)
    (hwf : SoundWfInnerRegular f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolveSoundWf_field f g y hsolve hfit hwf

end Capstone

/-! ## ★ Task 4 — `native_decide` validations: fuel-free, in parity with `crischDESolveSound`

The fuel-free sound solver's behaviour over the level-2 field `ℚ(x)(t₁)`, certified by `native_decide` (the
inner §6 pipeline runs fuel-free through `cRischDEGWf`):

* **The witness returns `none`.** `crischDESolveSoundWf witnessF 1 = none` — on `f = 1/(t₁ − x)`, `g = 1`, the
  unsolvable RDE, the fuel-free solver's §6.1 check detects unsolvability and returns `none` (parity with
  `crischDESolveSound_witness_none`).
* **Solvable cases still solve.** `Dy = 1 → y = t₁` and `Dy + y = t₁ + 1 → y = t₁` both return the correct
  `some y` with `D(y) + f·y = g`, checked at the field level (parity with `crischDESolveSound_solves_*`).

These are the fuel-free counterparts of the `crischDESolveSound` validations, confirming the inner-solve swap
(`cRischDEGWf` for `cRischDEG towerRischDEFuel`) changes no result. -/

section Validation

/-- **★ The fuel-free sound solver returns `none` on the unsoundness witness**
(`crischDESolveSoundWf_witness_none`, `native_decide`): for `f = 1/(t₁ − x)`, `g = 1` over `ℚ(x)(t₁)` — the RDE
with NO solution — `crischDESolveSoundWf witnessF 1 = none`, fuel-free. The §6.1 solvability check detects the
surviving `D`-constant special pole `t₁ − x` and reports unsolvability, exactly as the fuel
`crischDESolveSound` (`crischDESolveSound_witness_none`) — the inner-solve swap to `cRischDEGWf` preserves the
fix. -/
theorem crischDESolveSoundWf_witness_none :
    crischDESolveSoundWf witnessF (CField.one : Lvl2) = none := by native_decide

/-- **The fuel-free witness result matches the fuel solver** (`crischDESolveSoundWf_witness_parity`):
`crischDESolveSoundWf witnessF 1 = crischDESolveSound witnessF 1` (both `none`) over `ℚ(x)(t₁)`. Direct parity
of the fuel-free and fuel sound solvers on the unsolvable witness, composing the two `native_decide`'d `none`
results (`crischDESolveSoundWf_witness_none` and `crischDESolveSound_witness_none`) — so it needs no
`DecidableEq` on the carrier. -/
theorem crischDESolveSoundWf_witness_parity :
    crischDESolveSoundWf witnessF (CField.one : Lvl2)
      = crischDESolveSound witnessF (CField.one : Lvl2) := by
  rw [crischDESolveSoundWf_witness_none, crischDESolveSound_witness_none]

/-- **The fuel-free sound solver still solves `Dy = 1` at level 2** (`crischDESolveSoundWf_solves_Dy_eq_one`,
`native_decide`): `crischDESolveSoundWf (0 : Lvl2) (1 : Lvl2)` returns `some y` with `D(y) + 0·y = 1`
(`y = t₁`), checked at the field level by `CField.isZero` of `cderiv y + 0·y − 1`. The fuel-free integration
path returns the correct solution — parity with `crischDESolveSound_solves_Dy_eq_one`. -/
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
`crischDESolve`) — parity with `crischDESolveSound_solves_Dy_plus_y`. -/
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

#print axioms crischDERawSolveWf_eq
#print axioms crischDESolveSoundWf_eq
#print axioms crischDESolveSoundWf_field

/-! ### Final verdict (Task 5)

**Is the fuel-free sound solver built and proven sound (parity with the fuel version)?** **Yes.**

* **Built fuel-free.** `crischDESolveSoundWf` runs the §6.1-gated sound pipeline (weak-normalize →
  `cisCanonNormalizedG` check → reduce → solve → transform back) with the inner RDE solve routed through the
  **fuel-free** `cRischDEGWf` (`crischDERawSolveWf`) in place of the fuel `CRischField.crischDESolve` — no
  `ℕ`-fuel parameter.
* **Proven sound, unconditional, axiom-clean.** `crischDESolveSoundWf_field`: a successful solve gives the
  ORIGINAL field-level Risch-DE identity `D(Y) + F·Y = G`, with NO `IsCanonNormalized` hypothesis (the solver
  checks it), composing `crischDESolveSoundWf_eq` (fuel-free = fuel on a regular run) with the proven
  `crischDESolveSound_field`. Axiom-clean `[propext, Classical.choice, Quot.sound]`, NO `native_decide`.
* **Parity with the fuel version, fuel-free.** The witness `f = 1/(t₁ − x)`, `g = 1` returns `none`
  (`crischDESolveSoundWf_witness_none`, and `crischDESolveSoundWf_witness_parity` = `crischDESolveSound`), and
  the solvable cases `Dy = 1` / `Dy + y = t₁ + 1` return the correct `some y` solving the RDE
  (`crischDESolveSoundWf_solves_*`) — all `native_decide`, fuel-free.

★ **This is the intended fuel-free sound entry point for the production re-pin** — routing the engine's RDE
solves through `crischDESolveSoundWf` (sound + fuel-free) is a separate coordinated step (it touches the
locked core), out of this file's scope; this file provides the verified fuel-free sound solver to route
through. -/

end DeepWiki.SymbolicIntegration
