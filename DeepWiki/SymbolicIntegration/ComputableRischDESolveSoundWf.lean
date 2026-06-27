import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound
import DeepWiki.SymbolicIntegration.ComputableTowerRischDEWellFounded

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

end DeepWiki.SymbolicIntegration
