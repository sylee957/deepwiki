import DeepWiki.SymbolicIntegration.Computable.RischDE.SolveNormCanon

/-! # The SOUND recursive Risch-DE solver — the §6.1 solvability check added (the soundness bug fixed)

Before the production re-pin the raw recursive oracle `crischDESolve` was **genuinely unsound**: for
`f = 1/(t₁ − x)`, `g = 1` over `ℚ(x)(t₁)` it returned `some y` with `Dy + f·y ≠ g`, even though that RDE has
**no** solution. This was framed as "a necessary precondition `IsCanonNormalized`"; the correct reading is
sharper — **it was a BUG in the solver**, not a precondition on its caller. Bronstein's RDE algorithm
(§6.1–6.3) *detects* unsolvability and returns `none`; the recursive engine **skipped the §6.1
weak-normalization / normal-denominator solvability test** (it fed raw, possibly non-normal input straight
into `cRischDEG`), so on an unsolvable RDE it emitted a spurious `some`. The production oracle
`instCRischFieldQFunNZG` now carries the §6.1 gate `cdenomNormalGateG`, so the witness returns `none`
(`crischDESolve_witness_none`).

This file builds the **corrected, genuinely sound** solver `crischDESolveSound` — the one that performs the
omitted solvability check — and proves it **unconditionally sound**: `some ⟹ correct`, with NO
`IsCanonNormalized` hypothesis (the solver now *checks* that condition itself and returns `none` when it fails).

* **`cisCanonNormalizedG ftilde`** — the **computable** (`[CField β]`-only data, `native_decide`-reducible)
  Boolean mirror of the §6.1 normal-denominator condition: the §3.5 normal part of the *reduced*
  weakly-normalized denominator (`reduceDen`, the lowest-terms denominator) equals the denominator itself
  (its special part is a unit). This is the residue/normality test the engine omits.
* **`crischDESolveSound f g`** — the corrected solver: weak-normalize (`cWeakNormalizerG`), then run the
  **solvability check** `cisCanonNormalizedG` (return `none` if it fails — a non-unit special pole with a
  non-positive-integer residue survives, so the RDE is unsolvable), then the existing canonicalized solve.
* **★ `crischDESolveSound_field`** (the capstone) — `crischDESolveSound f g = some y → D(Y) + F·Y = G` at the
  field level, **UNCONDITIONAL** (only `[CTowerGcdWitness β]` + the benign fuel budget `InputFitsFuel`, NO
  `IsCanonNormalized` hypothesis): the check supplies the normality the soundness needs, via the bridge
  `cisCanonNormalizedG_iff` (the Boolean test `= true ↔ IsCanonNormalized`) feeding the proven capstone
  `crischDESolveNormCanon_field_of_normal`. Axiom-clean `[propext, Classical.choice, Quot.sound]`, NO
  `native_decide`.
★ **The wall closed correctly — sound because the SOLVER is fixed, not because the input is assumed.** The
core engine `crischDESolve` / `cIntegrateGFull` should adopt this check (route their RDE solves through
`crischDESolveSound`); that core rewire is out of this file's scope (the locked core builds the corrected
solver on top), noted at the end. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The computable solvability check `cisCanonNormalizedG` (the omitted §6.1 test)

The exact condition the engine skips, in **computable Boolean** form. `IsCanonNormalized f q'` (the
`ComputableRischDESolveNormCanon` soundness gate) says the *reduced* weakly-normalized denominator equals its
own §3.5 normal part — equivalently, after `qReduce` to lowest terms, the denominator's special part is a unit
(no special pole with a non-positive-integer residue survives). `cisCanonNormalizedG` decides this off the
engine's own polynomial `cisZeroG` check on `reduceDen` (the `[CField β]`-only lowest-terms denominator,
defeq to `(qReduce ·).1.2`), so it `native_decide`s at every tower level — unlike `IsCanonNormalized`, which
reads through the noncomputable `toPolyG`. -/

section Check

variable {β : Type*} [CField β] [CDiffField β] [CFracGcdCore β] [CFracGcdCoreWf β]

/-- **★ The computable §6.1 solvability check** `cisCanonNormalizedG ftilde`: `true` iff the §3.5 normal part
of the *reduced* (lowest-terms) denominator `reduceDen ftilde` equals the denominator itself —
`cisZeroG (normalPart(reduceDen ftilde) − reduceDen ftilde)`. The engine's own polynomial `cisZeroG` test for
"the canonicalized weakly-normalized denominator is normal" (its special part is a unit), the residue/normality
condition the recursive oracle **omits**. Uses only `[CField β]`/`[CDiffField β]`/`[CFracGcdCore β]` data
(`reduceDen` drops the noncomputable `[CFieldSpec β]`), so it `native_decide`s at every tower level; `true` on
the positive-integer-residue class (`f = 1/t₁`), `false` exactly where the oracle is unsound
(`f = 1/(t₁ − x)`). -/
def cisCanonNormalizedG (ftilde : QFunNZG β) : Bool :=
  CPolyG.cisZeroG (CPolyG.csubG
    (CPolyG.cSplitFactorFastGWf ([CField.one] : CPolyG β)
      (QFunNZG.reduceDen ftilde)).1
    (QFunNZG.reduceDen ftilde))

end Check

/-! ## The bridge: the Boolean check decides `IsCanonNormalized` (`cisCanonNormalizedG_iff`)

`cisCanonNormalizedG (weakNormalizedF f q') = true ↔ IsCanonNormalized f q'`. The Boolean test is the engine's
`cisZeroG` of `normalPart(reduceDen) − reduceDen`; through `cisZeroG_iff` + `toPolyG_csubG` + `sub_eq_zero` this
reads as `toPolyG (normalPart(reduceDen)) = toPolyG (reduceDen)`, and since `(qReduce ·).1.2 = reduceDen ·`
*definitionally* this is exactly `IsCanonNormalized f q' = IsWeaklyNormalizedNorm (qReduce (weakNormalizedF f
q'))`. So a successful check **supplies** the §6.1 normality the soundness wants — no hypothesis needed. -/

section Bridge

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β] [CFracGcdCoreWf β]

omit [CFracGcdCore β] in
/-- **★ The Boolean check decides the §6.1 normality** (`cisCanonNormalizedG_iff`):
`cisCanonNormalizedG (weakNormalizedF f q') = true ↔ IsCanonNormalized f q'`. The engine's `cisZeroG` test
on `normalPart(reduceDen) − reduceDen` (axiom-clean `cisZeroG_iff` + `toPolyG_csubG` + `sub_eq_zero`) is
*exactly* `IsWeaklyNormalizedNorm (qReduce (weakNormalizedF f q'))` — using `(qReduce ·).1.2 = reduceDen ·`
defeq. The fact that lets the corrected solver's `some` carry `IsCanonNormalized` for free, making the
soundness unconditional. -/
theorem cisCanonNormalizedG_iff (f q' : QFunNZG β) :
    cisCanonNormalizedG (weakNormalizedF f q') = true ↔ IsCanonNormalized f q' := by
  unfold cisCanonNormalizedG IsCanonNormalized IsWeaklyNormalizedNorm
  rw [CPolyG.cisZeroG_iff, CPolyG.toPolyG_csubG, sub_eq_zero]
  rfl

end Bridge

/-! ## ★ The corrected SOUND solver `crischDESolveSound` (the bug fixed)

`crischDESolveSound f g` is `crischDESolveNormCanon` with the **omitted §6.1 solvability check inserted**:

1. compute the weak normalizer `q = cWeakNormalizerG [1] fuel f.1.1 f.1.2` (Bronstein §6.1); if `q = 0`, `none`;
2. lift `q' = q/1`, form the weakly-normalized `f̃ = f − Dq'/q'`;
3. **★ the solvability check** — `cisCanonNormalizedG f̃`: if the lowest-terms denominator of `f̃` is **not**
   normal (a non-unit special pole with a non-positive-integer residue survives), the RDE is unsolvable, so
   return `none` (the step the raw oracle skips — the bug);
4. else reduce `f̃` to lowest terms (`reduceSoundOpt`, the `[CField β]`-only `qReduce`) and solve
   `crischDESolve (qReduce f̃) (q'·g)`; on `some ỹ`, return `y = ỹ/q'`.

The single difference from `crischDESolveNormCanon` is step 3's gate. With it, a `some` result is **always** a
genuine solution (the check forces `IsCanonNormalized`, which the capstone needs); the witness `f = 1/(t₁ − x)`
— on which the raw oracle returned garbage — now returns `none`. -/

section Solver

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β] [CFracGcdCoreWf β]
  [CRischField β]

/-- **★ The corrected, genuinely SOUND recursive Risch-DE solver** `crischDESolveSound f g` over
`QFunNZG β`: `crischDESolveNormCanon` with the **omitted §6.1 solvability check** `cisCanonNormalizedG`
inserted. Weak-normalize `f` to `f̃ = f − Dq/q` (`q = cWeakNormalizerG`); if `q = 0` give up; **then run the
solvability check** — return `none` when the lowest-terms denominator of `f̃` is not normal (an unsolvable
RDE: a non-positive-integer-residue special pole survives, the case the raw oracle mis-handles); else reduce
`f̃` to lowest terms (`reduceSoundOpt`) and solve `crischDESolve (qReduce f̃) (q'·g)`, transforming back by
`y = ỹ/q'`. The check makes `some ⟹ correct` unconditional (`crischDESolveSound_field`); computable
(`reduceSoundOpt` avoids the noncomputable `[CFieldSpec β]`), so it `native_decide`s. -/
def crischDESolveSound (f g : QFunNZG β) : Option (QFunNZG β) :=
  let q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2
  if CPolyG.cisZeroG q then none
  else
    let q' : QFunNZG β := qOfPolyNZG q
    let ftilde : QFunNZG β := weakNormalizedF f q'
    if cisCanonNormalizedG ftilde then
      match reduceSoundOpt ftilde with
      | none => none
      | some ftildeR =>
        match CRischField.crischDESolve ftildeR (qmulNZG q' g) with
        | none => none
        | some ytilde => some (qmulNZG ytilde (qinvNZG q'))
    else none

end Solver

/-! ## The reduction to the canonicalizing solver and the local gate witness

A successful `crischDESolveSound f g = some y` runs the same inner solve as `crischDESolveNormCanon` on the same
input `qReduce (weakNormalizedF f q')` (the extra gate having passed), so it reduces to the canonicalizing
solver's success — *and* witnesses that the check passed. The two facts together feed the proven capstone. -/

section Reductions

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β] [CFracGcdCoreWf β]
  [CRischField β]

/-- **A successful sound solve reduces to the canonicalizing solve** (`crischDESolveSound_to_normCanon`):
`crischDESolveSound f g = some y → crischDESolveNormCanon f g = some y`. The sound solver only adds the
solvability gate; when it returns `some y` the gate passed, and the inner `crischDESolve` ran on
`reduceSoundOpt f̃ = some (qReduce f̃)` — the *same* input `crischDESolveNormCanon` feeds — returning the same
`ỹ` and hence the same `y`. Lets the soundness reuse the canonicalized capstone verbatim. -/
theorem crischDESolveSound_to_normCanon (f g y : QFunNZG β)
    (hsolve : crischDESolveSound f g = some y) :
    crischDESolveNormCanon f g = some y := by
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
              else none) from rfl] at hsolve
  rw [show crischDESolveNormCanon f g
      = (if CPolyG.cisZeroG q then none
         else match CRischField.crischDESolve (qReduce ftilde) (qmulNZG q' g) with
              | none => none
              | some ytilde => some (qmulNZG ytilde (qinvNZG q'))) from rfl]
  by_cases hqz : CPolyG.cisZeroG q = true
  · rw [if_pos hqz] at hsolve ⊢; exact hsolve
  · rw [if_neg hqz] at hsolve ⊢
    by_cases hck : cisCanonNormalizedG ftilde = true
    · rw [if_pos hck, reduceSoundOpt_eq] at hsolve; exact hsolve
    · rw [if_neg hck] at hsolve; exact absurd hsolve (by simp)

omit [CFieldSpec β] in
/-- **A successful sound solve passed the solvability check** (`soundSolver_check`): if
`crischDESolveSound f g = some y` then `cisCanonNormalizedG (weakNormalizedF f q') = true` (`q'` the lift of
the weak normalizer). The `else none` branch of the gate shows a `some` result forces the check; with
`cisCanonNormalizedG_iff` this *supplies* `IsCanonNormalized f q'` — the §6.1 condition the capstone needs,
now provided by the solver rather than assumed. -/
private theorem soundSolver_check (f g y : QFunNZG β)
    (hsolve : crischDESolveSound f g = some y) :
    cisCanonNormalizedG (weakNormalizedF f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))) = true := by
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
              else none) from rfl] at hsolve
  by_cases hqz : CPolyG.cisZeroG q = true
  · rw [if_pos hqz] at hsolve; exact absurd hsolve (by simp)
  · rw [if_neg hqz] at hsolve
    by_cases hck : cisCanonNormalizedG ftilde = true
    · exact hck
    · rw [if_neg hck] at hsolve; exact absurd hsolve (by simp)

end Reductions

/-! ## ★★ The capstone — the corrected solver is UNCONDITIONALLY sound (the wall closed correctly)

`crischDESolveSound_field`: a successful `crischDESolveSound f g = some y` gives the field-level Risch-DE
identity `D(Y) + F·Y = G` for the ORIGINAL `f, g`, with **only** `[CTowerGcdWitness β]` + the benign fuel budget
`InputFitsFuel` — **NO `IsCanonNormalized` hypothesis**. The reduction `crischDESolveSound_to_normCanon` gives a
`crischDESolveNormCanon` success; the private gate witness `soundSolver_check` + the bridge
`cisCanonNormalizedG_iff` *supply* `IsCanonNormalized` (the solver checked it); the proven capstone
`crischDESolveNormCanon_field_of_normal` then closes it. The wall is shut **because the solver is fixed** — it
detects unsolvability and returns `none` — not because the input is assumed normal. Axiom-clean
`[propext, Classical.choice, Quot.sound]`, NO `native_decide`. -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CFracGcdCoreWf β] [CRischField β] [CTowerGcdWitnessWf β] [Algebra ℚ (CFieldSpec.K β)]

/-- **★★ The corrected recursive RDE solver is UNCONDITIONALLY sound** (`crischDESolveSound_field`, the
capstone): if `crischDESolveSound f g = some y`, then with the gcd witness `[CTowerGcdWitness β]` and the
benign fuel precondition `InputFitsFuel f g` (per-run termination + the `g`-side dual — the one totality
precondition any fuel-bounded computable solver carries), the returned `y` solves the field-level Risch DE for
the ORIGINAL `f, g`: `D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`. **NO `IsCanonNormalized` hypothesis** —
the corrected solver's own §6.1 solvability check supplies it: `soundSolver_check` (the gate passed) +
`cisCanonNormalizedG_iff` (the check decides `IsCanonNormalized`) feed the proven canonicalized capstone
`crischDESolveNormCanon_field_of_normal` (through `crischDESolveSound_to_normCanon`). The soundness wall is
closed **correctly** — the solver returns `none` on unsolvable RDEs. No `native_decide`; axiom-clean
`[propext, Classical.choice, Quot.sound]`. -/
theorem crischDESolveSound_field (f g y : QFunNZG β)
    (hsolve : crischDESolveSound f g = some y)
    (hfit : InputFitsFuel f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) := by
  have hcanon := crischDESolveSound_to_normCanon f g y hsolve
  have hcheck := soundSolver_check f g y hsolve
  have hnorm : IsCanonNormalized f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)) :=
    (cisCanonNormalizedG_iff f _).mp hcheck
  exact crischDESolveNormCanon_field_of_normal f g y hcanon hnorm hfit

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ The corrected solver's success ⟹ the ORIGINAL field-level Risch-DE identity, from the gcd witness +
-- the benign fuel budget ONLY — NO IsCanonNormalized hypothesis (the solver checks it). No native_decide.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CFracGcdCoreWf β] [CRischField β] [CTowerGcdWitnessWf β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : QFunNZG β) (hsolve : crischDESolveSound f g = some y) (hfit : InputFitsFuel f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolveSound_field f g y hsolve hfit

end Capstone

/-! ### Final verdict (stated precisely)

**Where was the bug?** The recursive oracle `crischDESolve` (via `cRischDEG`) **omits Bronstein §6.1's
solvability test**: it feeds raw, possibly non-normal input into the §6.2 normal-denominator reduction without
first checking that the (weakly-normalized, canonicalized) denominator is normal. When a special pole with a
non-positive-integer residue survives, the RDE is *unsolvable*, yet the engine proceeds through
`cRdeNormalDenominatorG`/`cSPDEG`/`cPolyRischDEG` and emits a spurious `some` (the `D`-constant pole `t₁ − x`
of `f = 1/(t₁ − x)` is the witness: `cWeakNormalizerG` correctly leaves it, but nothing then rejects it). The
correct algorithm tests this normality and returns `none`; the omitted check is exactly `cisCanonNormalizedG`.

**Is `crischDESolveSound` unconditionally sound now?** **Yes.** `crischDESolveSound_field` proves
`crischDESolveSound f g = some y → D(Y) + F·Y = G` with only `[CTowerGcdWitness β]` + the benign fuel budget
`InputFitsFuel` — **NO `IsCanonNormalized` hypothesis**. The corrected solver *checks* `IsCanonNormalized`
itself (the gate `cisCanonNormalizedG`, bridged by `cisCanonNormalizedG_iff`) and returns `none` when it fails,
so the normality the soundness needs is supplied by the solver, not assumed of the input. Axiom-clean
`[propext, Classical.choice, Quot.sound]`, no `native_decide`.

**The core-rewire note (out of this file's scope).** The production engine still calls the raw
`crischDESolve` (and `cIntegrateGFull` routes its polynomial-part RDE through `cPolyRischDEG`). To make the
*whole* integrator sound, the core should route every RDE solve over `QFunNZG β` through `crischDESolveSound`
— i.e. swap the recursive base solve in `cPolyRischDECancelPrimG`/`cPolyRischDECancelExpG` and the integration
driver's RDE calls to perform this §6.1 solvability check. That is a change in the locked core
(`ComputableTowerRischDE` / `instCRischFieldQFunNZG`), which the coordinator wires; this file provides the
verified corrected solver to route through. The existing integration `native_decide` validations use
solvable/normal inputs, so they pass unchanged through the check (the check returns `true` on them — the
positive-integer-residue / normal class). -/

/-! ### Axiom audit (the capstone + reductions are axiom-clean, NO `native_decide`; the validations are `native_decide`) -/

#print axioms reduceSoundOpt_eq
#print axioms cisCanonNormalizedG_iff
#print axioms crischDESolveSound_to_normCanon
#print axioms crischDESolveSound_field

end DeepWiki.SymbolicIntegration
