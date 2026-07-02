import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound
import DeepWiki.SymbolicIntegration.ComputableRischDESolveSoundWf

/-! # §6 RDE decision-procedure COMPLETENESS — `solvable ⟹ some` (the converse of soundness)

`ComputableRischDESolveSound` proved the corrected recursive Risch-DE solver `crischDESolveSound`
**sound**: `crischDESolveSound f g = some y → D(Y) + F·Y = G` at the field level, **unconditionally**
(`crischDESolveSound_field`; the §6.1 check `cisCanonNormalizedG` supplies the normality, so no
`IsCanonNormalized` hypothesis). That is the `some ⟹ correct` half. This file pursues the **converse**,
`solvable ⟹ some` — together making the solver a verified **DECISION PROCEDURE**
(`some ⟺ solvable`).

**The structure of completeness.** `crischDESolveSound f g` produces `none` on exactly four branches:

1. **§6.1 weak-normalizer vanishes** — `cWeakNormalizerG … = 0` (`cisZeroG q`);
2. **§6.1 normality check fails** — `cisCanonNormalizedG f̃ = false`;
3. **the lowest-terms reduction fails** — `reduceSoundOpt f̃ = none` (impossible: `reduceSoundOpt_eq`);
4. **the inner recursive solve fails** — `crischDESolve (qReduce f̃) (q'·g) = none`.

Equivalently, the solver succeeds (`crischDESolveSound_some_iff`) iff the weak normalizer is nonzero, the
§6.1 check passes, and the inner solve succeeds (branch (3) never blocks). Completeness —
`solvable ⟹ some` — is then **exactly** the conjunction of these stage-completeness facts: a solvable RDE
has (1) a non-vanishing weak normalizer, (2) a passing §6.1 check, (3) a successful reduction (free), and
(4) a successful inner solve. Branch (3) is closed unconditionally; branches (1), (2), (4) are the genuine
§6 completeness content.

**What is reachable here.**
* **The structural `some`-characterization** `crischDESolveSound_some_iff` — the exact reading of when the
  solver succeeds (the three stage tests passing); pure control flow, no §6 mathematics.
* **The base-field completeness** `rischDE_complete_base` — over the constant base `ℚ` (`D = 0`),
  `crischDESolve` is the direct division `g/b`, so it is **decidably complete**: an RDE `b·y = g`
  has a solution iff `crischDESolve b g = some _` (axiom-clean, no `native_decide`).
* **The reduction of completeness to the deep §6 stages** — `crischDESolveSound_complete_of_residual`:
  modulo the isolated residual `RischDECompletenessResidual` (the three deep stage-completeness facts),
  `solvable ⟹ some`. With soundness this gives `some ⟺ solvable` modulo the residual
  (`crischDESolveSound_decides_of_residual`).

**The deep §6 residual (precisely isolated, NEVER `sorry`).** The genuine content of completeness — that
a solvable RDE survives every §6 `none`-gate — is bundled in `RischDECompletenessResidual`. Its three
clauses are the converse directions the soundness layer never needed and the engine does **not**
self-certify: (a) the §6.1 weak-normalizer non-vanishing, (b) the §6.1 normality completeness
(`solvable ⟹ check passes` — the contrapositive of the unsoundness witness, i.e. a non-normalizable
denominator's RDE is genuinely unsolvable), and (c) the **§6.4 degree-bound + SPDE + poly-RDE
completeness** (any field solution has bounded degree and is found by the bounded polynomial solve). Clause
(c) is the research-grade core: it requires the §6.4 degree bound to be a *provable upper bound on any
solution's degree* and the SPDE/poly-RDE solve to be *exhaustive within the bound* — neither of which is
formalized anywhere in the engine (only the soundness cleared-identity is). This file states it precisely
and proves completeness *modulo* it; it is the honest §6 decision-procedure frontier. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The field-level RDE solvability predicate `FieldRDESolvable`

`FieldRDESolvable f g` is the existence of a `QFunNZG β` solution to the field-level Risch DE
`D(Y) + F·Y = G`, phrased through the *exact* expression of `crischDESolveSound_field`'s conclusion
(`towerFractionFieldDerivG` + `amG ∘ toPolyG` readings). This is the "solvable" side of the decision
procedure: soundness says `some ⟹ FieldRDESolvable`, completeness says `FieldRDESolvable ⟹ some`. -/

section Solvable

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **Field-level RDE solvability** `FieldRDESolvable f g`: there exists `y : QFunNZG β` solving the
field-level Risch differential equation `D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`, read through
`amG ∘ toPolyG` exactly as `crischDESolveSound_field`'s conclusion. The "solvable" side of the decision
procedure: soundness gives `crischDESolveSound f g = some _ → FieldRDESolvable f g`; completeness is the
converse `FieldRDESolvable f g → crischDESolveSound f g = some _`. -/
def FieldRDESolvable (f g : QFunNZG β) : Prop :=
  ∃ y : QFunNZG β,
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2)

/-- **Soundness, restated as `some ⟹ solvable`** (`crischDESolveSound_imp_solvable`): a successful sound
solve `crischDESolveSound f g = some y` witnesses `FieldRDESolvable f g` (take the returned `y`). The
forward half of the decision-procedure equivalence; the capstone `crischDESolveSound_field` supplies the
identity. -/
theorem crischDESolveSound_imp_solvable (f g y : QFunNZG β)
    (hsolve : crischDESolveSound f g = some y) (hfit : InputFitsFuel f g) :
    FieldRDESolvable f g :=
  ⟨y, crischDESolveSound_field f g y hsolve hfit⟩

end Solvable

/-! ## The structural `some`/`none`-characterization (the control-flow skeleton, no §6 mathematics)

`crischDESolveSound f g`'s body is a guarded `if/match` chain over three computable tests: the
weak-normalizer zero test `cisZeroG q`, the §6.1 check `cisCanonNormalizedG f̃`, and the inner solve
`crischDESolve (qReduce f̃) (q'·g)` (the `reduceSoundOpt` step is total, `reduceSoundOpt_eq`). We read off
**exactly** when the solver succeeds — `crischDESolveSound_some_iff` — and the converse-useful sufficient
form `crischDESolveSound_some_of_stages` (the three positive conditions force `some`), the skeleton
completeness reduces to. Pure control flow; no §6 algorithm correctness. -/

section Structural

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]
  [CRischField β]

/-- **The sound solver succeeds iff the three stage tests succeed** (`crischDESolveSound_some_iff`):
`crischDESolveSound f g = some y` **↔** the weak normalizer `q = cWeakNormalizerG …` is nonzero
(`cisZeroG q = false`), the §6.1 check passes (`cisCanonNormalizedG f̃ = true`), and the inner recursive
solve on the lowest-terms pair succeeds with the returned value transformed back — `∃ ỹ,
crischDESolve (qReduce f̃) (q'·g) = some ỹ ∧ y = ỹ/q'` (`f̃ = weakNormalizedF f q'`, `q' = q/1`). The exact
control-flow reading of `crischDESolveSound`; the `reduceSoundOpt` step never blocks (`reduceSoundOpt_eq`).
The skeleton on which completeness (`solvable ⟹ each test passes`) is assembled. -/
theorem crischDESolveSound_some_iff (f g y : QFunNZG β) :
    crischDESolveSound f g = some y ↔
      (CPolyG.cisZeroG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
          = false
        ∧ cisCanonNormalizedG (weakNormalizedF f
            (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)))
          = true
        ∧ ∃ ytilde : QFunNZG β,
            CRischField.crischDESolve
                (qReduce (weakNormalizedF f
                  (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel
                    f.1.1 f.1.2))))
                (qmulNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel
                  f.1.1 f.1.2)) g)
              = some ytilde
              ∧ y = qmulNZG ytilde (qinvNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β)
                  towerRischDEFuel f.1.1 f.1.2)))) := by
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
  · rw [if_pos hqz]
    simp only [hqz, Bool.true_eq_false, false_and, iff_false]
    intro h; exact absurd h (by simp)
  · rw [if_neg hqz]
    rw [Bool.not_eq_true] at hqz
    by_cases hck : cisCanonNormalizedG ftilde = true
    · rw [if_pos hck, reduceSoundOpt_eq]
      rcases hinner : CRischField.crischDESolve (qReduce ftilde) (qmulNZG q' g) with _ | ytilde
      · simp only [hinner, hqz, hck, true_and]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨yt, hyt, _⟩; exact absurd hyt (by simp)
      · simp only [hinner, hqz, hck, true_and, Option.some.injEq]
        constructor
        · intro h; exact ⟨ytilde, rfl, h.symm⟩
        · rintro ⟨yt, hyt, hy⟩; rw [hy, hyt]
    · rw [if_neg hck]
      rw [Bool.not_eq_true] at hck
      simp only [hck, Bool.false_eq_true, and_false, false_and, iff_false]
      intro h; exact absurd h (by simp)

/-- **The three stage tests succeed ⟹ the sound solver succeeds** (`crischDESolveSound_some_of_stages`):
the converse-useful sufficient direction of `crischDESolveSound_some_iff`. If the weak normalizer is
nonzero, the §6.1 check passes, and the inner recursive solve returns `some ỹ`, then
`crischDESolveSound f g = some (ỹ/q')`. This is the *positive* control-flow fact completeness builds on:
each of the three stage-completeness facts (a solvable RDE clears each gate) feeds the corresponding
hypothesis here, and the solver returns `some`. -/
theorem crischDESolveSound_some_of_stages (f g ytilde : QFunNZG β)
    (hq : CPolyG.cisZeroG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
        = false)
    (hck : cisCanonNormalizedG (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)))
        = true)
    (hinner : CRischField.crischDESolve
        (qReduce (weakNormalizedF f
          (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))))
        (qmulNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel
          f.1.1 f.1.2)) g)
        = some ytilde) :
    crischDESolveSound f g
      = some (qmulNZG ytilde (qinvNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β)
          towerRischDEFuel f.1.1 f.1.2)))) :=
  (crischDESolveSound_some_iff f g _).mpr ⟨hq, hck, ytilde, hinner, rfl⟩

end Structural

/-! ## Fuel-free structural `some`/`none`-characterization

The Wf solver has the same outer control flow as the fueled sound solver, but its two fuel-sensitive stage
calls are the fuel-free weak normalizer `cWeakNormalizerGWf` and the fuel-free inner solve
`crischDERawSolveWf`. These lemmas give the Wf entry point its own structural success API, so later
completeness refactors can target `crischDESolveSoundWf` directly instead of rewriting through the fueled
solver first. -/

section StructuralWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]
  [CFracGcdCoreWf β] [CRischField β]

/-- **The fuel-free sound solver succeeds iff its three Wf stage tests succeed**
(`crischDESolveSoundWf_some_iff`): `crischDESolveSoundWf f g = some y` iff the fuel-free weak normalizer
is nonzero, the §6.1 canon-normality gate passes on the weak-normalized input, and the fuel-free inner solve
`crischDERawSolveWf` succeeds on the reduced pair, with the returned value transformed back by `q⁻¹`. -/
theorem crischDESolveSoundWf_some_iff (f g y : QFunNZG β) :
    crischDESolveSoundWf f g = some y ↔
      (CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)
          = false
        ∧ cisCanonNormalizedG (weakNormalizedF f
            (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)))
          = true
        ∧ ∃ ytilde : QFunNZG β,
            crischDERawSolveWf
                (qReduce (weakNormalizedF f
                  (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
                (qmulNZG (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g)
              = some ytilde
              ∧ y = qmulNZG ytilde (qinvNZG (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β)
                  f.1.1 f.1.2)))) := by
  set q : CPolyG β := cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2 with hq
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
  by_cases hqz : CPolyG.cisZeroG q = true
  · rw [if_pos hqz]
    simp only [hqz, Bool.true_eq_false, false_and, iff_false]
    intro h; exact absurd h (by simp)
  · rw [if_neg hqz]
    rw [Bool.not_eq_true] at hqz
    by_cases hck : cisCanonNormalizedG ftilde = true
    · rw [if_pos hck, reduceSoundOpt_eq]
      rcases hinner : crischDERawSolveWf (qReduce ftilde) (qmulNZG q' g) with _ | ytilde
      · simp only [hinner, hqz, hck, true_and]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨yt, hyt, _⟩; exact absurd hyt (by simp)
      · simp only [hinner, hqz, hck, true_and, Option.some.injEq]
        constructor
        · intro h; exact ⟨ytilde, rfl, h.symm⟩
        · rintro ⟨yt, hyt, hy⟩; rw [hy, hyt]
    · rw [if_neg hck]
      rw [Bool.not_eq_true] at hck
      simp only [hck, Bool.false_eq_true, and_false, false_and, iff_false]
      intro h; exact absurd h (by simp)

/-- **The three Wf stage tests succeed ⟹ the fuel-free sound solver succeeds**
(`crischDESolveSoundWf_some_of_stages`): if the Wf weak normalizer is nonzero, the §6.1 gate passes, and
`crischDERawSolveWf` returns `some ỹ`, then `crischDESolveSoundWf f g = some (ỹ/q')`. -/
theorem crischDESolveSoundWf_some_of_stages (f g ytilde : QFunNZG β)
    (hq : CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)
        = false)
    (hck : cisCanonNormalizedG (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)))
        = true)
    (hinner : crischDERawSolveWf
        (qReduce (weakNormalizedF f
          (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
        (qmulNZG (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g)
        = some ytilde) :
    crischDESolveSoundWf f g
      = some (qmulNZG ytilde (qinvNZG (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β)
          f.1.1 f.1.2)))) :=
  (crischDESolveSoundWf_some_iff f g _).mpr ⟨hq, hck, ytilde, hinner, rfl⟩

/-! ### Restatement against the intended wording (anonymous `example`) -/

example (f g ytilde : QFunNZG β)
    (hq : CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)
        = false)
    (hck : cisCanonNormalizedG (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)))
        = true)
    (hinner : crischDERawSolveWf
        (qReduce (weakNormalizedF f
          (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
        (qmulNZG (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g)
        = some ytilde) :
    crischDESolveSoundWf f g
      = some (qmulNZG ytilde (qinvNZG (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β)
          f.1.1 f.1.2)))) :=
  crischDESolveSoundWf_some_of_stages f g ytilde hq hck hinner

end StructuralWf

/-! ## The base-field completeness over the constants `ℚ` (decidably complete, axiom-clean)

The tower recursion bottoms at `CRischField ℚ` (the constant field, `D = 0`), where `crischDESolve b g`
is the **direct division** `if b = 0 then (if g = 0 then some 0 else none) else some (g/b)`. There the
RDE `D(y) + b·y = g` collapses to `b·y = g`, which has a solution `y ∈ ℚ` **iff** `b ≠ 0 ∨ g = 0` — and
that is *exactly* the condition under which `crischDESolve` returns `some`. So the base oracle is a
genuine **decision procedure**: `b·y = g` solvable ↔ `crischDESolve b g = some _`. This is the
completeness counterpart of `CRischFieldSpec ℚ`'s soundness, fully reachable (no §6 pipeline), axiom-clean
— and the base case of any tower-completeness induction. -/

section BaseField

/-- **★ Base-field completeness over `ℚ`** (`rischDE_complete_base`): the constant-field RDE `b·y = g`
(`D = 0`) is solvable in `ℚ` **iff** the base oracle returns `some` —
`(∃ y : ℚ, b·y = g) ↔ ∃ y, CRischField.crischDESolve b g = some y`. The forward direction is completeness
(a solution forces a `some`): if `b ≠ 0` the division `g/b` is the witness; if `b = 0` then `b·y = g`
forces `g = 0`, and the oracle returns `some 0`. The reverse is soundness (`CRischFieldSpec ℚ`). The base
oracle is a decision procedure; axiom-clean, no `native_decide`. -/
theorem rischDE_complete_base (b g : ℚ) :
    (∃ y : ℚ, b * y = g) ↔ ∃ y, CRischField.crischDESolve b g = some y := by
  simp only [CRischField.crischDESolve]
  constructor
  · rintro ⟨y, hy⟩
    by_cases hb : b = 0
    · -- `b = 0` ⟹ `g = 0`, oracle is `some 0`
      have hg : g = 0 := by rw [← hy, hb, zero_mul]
      exact ⟨0, by rw [if_pos hb, if_pos hg]⟩
    · -- `b ≠ 0` ⟹ oracle is `some (g/b)`
      exact ⟨g / b, by rw [if_neg hb]⟩
  · rintro ⟨y, hy⟩
    by_cases hb : b = 0
    · -- `b = 0`: oracle `some` forces `g = 0`, then `b·0 = 0 = g`
      rw [if_pos hb] at hy
      by_cases hg : g = 0
      · exact ⟨0, by rw [hb, zero_mul, hg]⟩
      · rw [if_neg hg] at hy; exact absurd hy (by simp)
    · -- `b ≠ 0`: `y = g/b` solves `b·(g/b) = g`
      rw [if_neg hb, Option.some.injEq] at hy
      exact ⟨g / b, mul_div_cancel₀ g hb⟩

/-- **Base-field completeness, the `some`-direction** (`rischDE_complete_base_some`): a solvable
constant-field RDE `b·y = g` (`D = 0`) makes the base oracle return `some` —
`(∃ y : ℚ, b·y = g) → ∃ y, CRischField.crischDESolve b g = some y`. The forward half of
`rischDE_complete_base`; the §6.1-free base case of the recursive completeness. -/
theorem rischDE_complete_base_some (b g : ℚ) (hsol : ∃ y : ℚ, b * y = g) :
    ∃ y, CRischField.crischDESolve b g = some y :=
  (rischDE_complete_base b g).mp hsol

end BaseField

/-! ## ★ The deep §6 completeness residual, precisely isolated (NEVER `sorry`)

The structural skeleton `crischDESolveSound_some_of_stages` reduces completeness — `FieldRDESolvable ⟹
some` — to **three** stage-completeness facts, each saying a solvable RDE *clears* the corresponding §6
`none`-gate. These are the genuine §6 decision-procedure content (the converse directions the soundness
layer never needed, and which the engine does **not** self-certify); we bundle them as the explicit,
named residual `RischDECompletenessResidual`, with the precise reason each is deep:

* **`hwn`** — the §6.1 **weak-normalizer non-vanishing**: a solvable RDE has `cWeakNormalizerG … ≠ 0`.
  Bronstein §6.1's `WeakNormalizer` returns the product `∏ᵢ gcd(aᵢ, d₁)^{nᵢ}` over the positive-integer
  residue roots (`= 1`, never `0`, for an already-weakly-normalized denominator); that it never vanishes
  on a solvable input is a §6.1 fact the fuel-bounded computable mirror does not prove.
* **`hck`** — the §6.1 **normality completeness**: a solvable RDE passes the check
  (`cisCanonNormalizedG f̃ = true`), equivalently `IsCanonNormalized f q'` (via `cisCanonNormalizedG_iff`).
  This is the **converse** of the unsoundness witness (`crischDESolveSound_witness_none`): a non-normalizable
  denominator — a surviving special pole with a non-positive-integer residue — makes the RDE *unsolvable*.
  So `hck` is the contrapositive "`¬ check ⟹ ¬ solvable`", the §6.1 *completeness* of the residue test.
* **`hinner`** — the **§6.2–6.6 inner-solve completeness**: a solvable RDE makes the inner recursive solve
  on the lowest-terms pair return `some`. This is the **research-grade core**: it requires (i) the §6.4
  degree bound `cRdeBoundDegreeG` to be a *provable upper bound on any field solution's degree*, and (ii)
  the SPDE (§6.4) + poly-RDE (§6.5/6.6) solve to be *exhaustive within that bound* (it finds the solution
  if one of bounded degree exists). **Neither is formalized anywhere in the engine** — only the soundness
  cleared-identity (`cRischDEG_rdeCleared_gen`) is proved; there is no degree-upper-bound lemma and no
  SPDE/poly-RDE completeness lemma (confirmed: the §6 files state only `some ⟹ cleared-identity`). This is
  the deep §6 decision-procedure frontier.

This is a `Prop`-bundle of stated assumptions (NOT proved), making the completeness boundary citable with
NO `sorry`. Each clause is the *converse* of a fact the soundness layer used in the forward direction. -/

section Residual

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **★ The precise deep §6 completeness residual** `RischDECompletenessResidual f g`: the three
stage-completeness facts that a solvable RDE clears every §6 `none`-gate — the converse directions the
engine does not self-certify. `hwn`: the §6.1 weak normalizer is nonzero on a solvable input. `hck`: a
solvable RDE passes the §6.1 normality check (the contrapositive of the unsoundness witness — a
non-normalizable denominator is genuinely unsolvable). `hinner`: a solvable RDE makes the §6.2–6.6 inner
recursive solve on the lowest-terms pair succeed (the research-grade core — needs the §6.4 degree bound to
be a provable upper bound on any solution's degree, and the SPDE/poly-RDE solve to be exhaustive within it,
neither formalized). Bundles exactly the hypotheses `crischDESolveSound_some_of_stages` consumes, all in
their solvability-implies form; a `Prop`-bundle of stated assumptions, NO `sorry`. -/
structure RischDECompletenessResidual (f g : QFunNZG β) : Prop where
  /-- §6.1: a solvable RDE has a nonzero weak normalizer (`WeakNormalizer` never vanishes on a solution). -/
  hwn : FieldRDESolvable f g →
    CPolyG.cisZeroG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2) = false
  /-- §6.1: a solvable RDE passes the normality check (contrapositive of the unsoundness witness — a
  non-normalizable denominator's RDE is unsolvable). -/
  hck : FieldRDESolvable f g →
    cisCanonNormalizedG (weakNormalizedF f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))) = true
  /-- §6.2–6.6: a solvable RDE makes the inner recursive solve on the lowest-terms pair succeed (the deep
  degree-bound + SPDE + poly-RDE completeness, not formalized in the engine). -/
  hinner : FieldRDESolvable f g →
    ∃ ytilde : QFunNZG β,
      CRischField.crischDESolve
          (qReduce (weakNormalizedF f
            (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2))))
          (qmulNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel
            f.1.1 f.1.2)) g)
        = some ytilde

end Residual

/-! ## ★ The deep clause (c) decomposed: the three §6 inner-stage completeness sub-residuals

Clause (c) of `RischDECompletenessResidual` — the §6.2–6.6 inner-solve completeness — is itself the
composite of the three §6 pipeline stages a polynomial solution must clear (the converse of the soundness
decomposition `cRischDEG_some_imp_stages`). We pinpoint the frontier by naming each sub-stage precisely as
its own `Prop`, against `cRischDEG`'s actual stage functions, with the Bronstein theorem that would
discharge it:

* **`cRdeNormalDenominatorG_complete`** — §6.2 normal-denominator reduction completeness: a solvable RDE's
  §6.2 reduction returns `some` (Bronstein Thm 6.1.2 / §6.2 — the normal-denominator stage succeeds on a
  normalized input). The §6.1 normality (`hck`) is exactly its precondition.
* **`cRdeBoundDegree_isUpperBound`** — ★ the §6.4 degree-bound *upper-bound* property: **any** polynomial
  solution `q` of the reduced `a·Dq + b·q = c` has `deg q ≤ cRdeBoundDegreeG …` (Bronstein Thm 6.3.1, the
  degree bound). This is the **research-grade keystone**: the engine *computes* the bound `cRdeBoundDegreeG`
  by degree arithmetic but never proves it bounds solutions — there is no `deg_le` lemma anywhere.
* **`cSPDE_polyRischDE_complete`** — §6.4 SPDE + §6.5/6.6 poly-RDE *exhaustiveness within the bound*: given
  a solution of degree ≤ the bound, the SPDE peel and the bounded polynomial solve **find** it (Bronstein
  §6.4–6.6). Also unformalized — only the cleared-identity soundness of these stages is proved.

A `cRischDEG`-level polynomial solution clearing all three forces `cRischDEG = some` (the converse of
`cRischDEG_some_imp_stages`), which lifts to clause (c). Each sub-residual is a stated `Prop`, NO `sorry`;
together they are clause (c)'s exact content, with the §6.4 degree-upper-bound the single deepest gap. -/

section InnerSubResidual

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **A `cRischDEG`-level polynomial RDE solution** `IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden`:
the cleared polynomial identity `cRischDEG` certifies on success — `gden·fden·(D(ynum)·yden − ynum·D(yden))
+ gden·fnum·ynum·yden = gnum·fden·yden²` over `(CFieldSpec.K α)[X]` — read as "(`ynum`/`yden`) solves the
RDE for (`fnum`/`fden`, `gnum`/`gden`)". The "solvable" predicate at the `cRischDEG` polynomial layer, the
hypothesis the inner-stage completeness sub-residuals are stated against. -/
def IsCRischDEGPolySol (Dt fnum fden gnum gden ynum yden : CPolyG α) : Prop :=
  toPolyG gden * toPolyG fden
      * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
          - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
      + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
    = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2

/-- **A reduced-equation polynomial solution** `IsReducedRdeSol Dt a b c q`: `q ∈ α[t]` solves the §6.3
linear ODE `a·Dq + b·q = c` at the polynomial level — `a·D(q) + b·q = c` over `(CFieldSpec.K α)[X]`
(`D = implicitDeriv (toPolyG Dt)`). The genuine antecedent of the §6.4 degree-upper-bound (Bronstein
Thm 6.3.1): the bound `cRdeBoundDegreeG a b c` is asserted to bound `deg q` for every such `q`. -/
def IsReducedRdeSol (Dt a b c q : CPolyG α) : Prop :=
  toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q
    = toPolyG c

/-- **★ The three §6 inner-stage completeness sub-residuals** `RischDEInnerCompleteness Dt fnum fden gnum
gden`: clause (c) of `RischDECompletenessResidual`, decomposed into the precise §6.2/6.4/6.5-6.6 converse
facts. `hnorm`: the §6.2 normal-denominator reduction returns `some` whenever a polynomial solution exists
(Bronstein §6.2). `hbound`: ★ **any** polynomial solution `q` of the §6.3-reduced `a·Dq + b·q = c` has
`deg q ≤ cRdeBoundDegreeG` (Bronstein Thm 6.3.1 — the degree-upper-bound, the deepest unformalized gap: the
engine computes the bound but never proves it bounds solutions). `hsolve`: the §6.4 SPDE + §6.5/6.6
poly-RDE solve returns `some` whenever a polynomial solution exists (Bronstein §6.4–6.6 exhaustiveness).
Their conjunction is exactly clause (c)'s content — the converse of the soundness decomposition
`cRischDEG_some_imp_stages`. A `Prop`-bundle of stated assumptions, NO `sorry`; the finest isolation of
clause (c), with `hbound` the single deepest gap. -/
structure RischDEInnerCompleteness (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- §6.2: a polynomial-solvable RDE's normal-denominator reduction succeeds. -/
  hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true
  /-- ★ §6.4 degree-upper-bound (Bronstein Thm 6.3.1): any polynomial solution `q` of the §6.3-reduced
  `a·Dq + b·q = c` (on the special-cleared coefficients) has `deg q ≤ cRdeBoundDegreeG` — the engine
  computes the bound but never proves it bounds solutions (the deepest unformalized gap). -/
  hbound : ∀ a0 b0 c0 h0 : CPolyG α,
    cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
    ∀ q : CPolyG α,
      IsReducedRdeSol Dt (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 q →
      cdegG q ≤ cRdeBoundDegreeG Dt
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
  /-- §6.4 SPDE + §6.5/6.6 poly-RDE exhaustiveness: a polynomial-solvable RDE's bounded solve succeeds. -/
  hsolve : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRischDEG Dt towerRischDEFuel fnum fden gnum gden).isSome = true

/-- **Clause (c) follows from the inner sub-residuals** (`cRischDEG_isSome_of_innerCompleteness`): the
`hsolve` clause of `RischDEInnerCompleteness` is *exactly* "a `cRischDEG`-polynomial-solvable RDE makes
`cRischDEG` return `some`" — so a polynomial solution forces `cRischDEG … = some _`. (The `hnorm`/`hbound`
clauses are the §6.2/§6.4 sub-facts whose composition *justifies* `hsolve` in Bronstein's proof; here they
are recorded alongside to pinpoint the frontier, while `hsolve` is the conclusion clause (c) consumes.)
This is the bridge from the finest decomposition back to clause (c). -/
theorem cRischDEG_isSome_of_innerCompleteness (Dt fnum fden gnum gden : CPolyG α)
    (hinner : RischDEInnerCompleteness Dt fnum fden gnum gden)
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    (cRischDEG Dt towerRischDEFuel fnum fden gnum gden).isSome = true :=
  hinner.hsolve hsol

end InnerSubResidual

/-! ## ★ Completeness modulo the residual, and the decision-procedure equivalence

Assembling the structural skeleton with the residual: a solvable RDE clears all three §6 gates
(`hwn`/`hck`/`hinner` applied to the solvability hypothesis), so `crischDESolveSound_some_of_stages`
returns `some`. That is completeness *modulo the residual* (`crischDESolveSound_complete_of_residual`).
Composed with the proven soundness (`crischDESolveSound_imp_solvable`), this is the full decision-procedure
equivalence `some ⟺ solvable` modulo the residual (`crischDESolveSound_decides_of_residual`). -/

section Complete

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

omit [CTowerGcdWitness β] in
/-- **★ §6 RDE completeness modulo the deep residual** (`crischDESolveSound_complete_of_residual`,
`solvable ⟹ some`): if the field-level RDE is solvable (`FieldRDESolvable f g`) and the deep §6
stage-completeness residual `RischDECompletenessResidual f g` holds, then the sound solver returns `some`
— `∃ y, crischDESolveSound f g = some y`. The residual's three clauses (a solvable RDE clears the §6.1
weak-normalizer gate, the §6.1 normality check, and the §6.2–6.6 inner solve) feed the structural
`crischDESolveSound_some_of_stages`. This is the converse of soundness, *modulo* the precisely isolated
deep §6 content (the degree-bound + SPDE/poly-RDE completeness the engine does not formalize). -/
theorem crischDESolveSound_complete_of_residual (f g : QFunNZG β)
    (hsol : FieldRDESolvable f g) (hres : RischDECompletenessResidual f g) :
    ∃ y, crischDESolveSound f g = some y := by
  obtain ⟨ytilde, hinner⟩ := hres.hinner hsol
  exact ⟨_, crischDESolveSound_some_of_stages f g ytilde (hres.hwn hsol) (hres.hck hsol) hinner⟩

/-- **★ The §6 RDE solver DECIDES solvability modulo the deep residual**
(`crischDESolveSound_decides_of_residual`, `some ⟺ solvable`): under the deep §6 completeness residual
`RischDECompletenessResidual f g` and the benign fuel budget `InputFitsFuel f g`, the sound solver returns
`some` **iff** the field-level RDE is solvable —
`(∃ y, crischDESolveSound f g = some y) ↔ FieldRDESolvable f g`. The `→` is the proven (unconditional)
soundness `crischDESolveSound_imp_solvable`; the `←` is completeness modulo the residual
(`crischDESolveSound_complete_of_residual`). Together: `crischDESolveSound` is a **verified decision
procedure** for the field-level Risch DE, modulo the precisely isolated deep §6 degree-bound + SPDE/poly-RDE
completeness. -/
theorem crischDESolveSound_decides_of_residual (f g : QFunNZG β)
    (hres : RischDECompletenessResidual f g) (hfit : InputFitsFuel f g) :
    (∃ y, crischDESolveSound f g = some y) ↔ FieldRDESolvable f g := by
  constructor
  · rintro ⟨y, hy⟩; exact crischDESolveSound_imp_solvable f g y hy hfit
  · intro hsol; exact crischDESolveSound_complete_of_residual f g hsol hres

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ The decision-procedure equivalence: the sound solver returns `some` iff the RDE is solvable,
-- modulo the deep §6 completeness residual + the benign fuel budget.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]
    (f g : QFunNZG β) (hres : RischDECompletenessResidual f g) (hfit : InputFitsFuel f g) :
    (∃ y, crischDESolveSound f g = some y) ↔ FieldRDESolvable f g :=
  crischDESolveSound_decides_of_residual f g hres hfit

end Complete

/-! ## Fuel-free completeness wrapper

The Wf solver now has two completeness routes:

* `RischDECompletenessResidualWf` is the native fuel-free residual: its clauses are stated against
  `cWeakNormalizerGWf` and `crischDERawSolveWf`, so the completeness direction goes straight through
  `crischDESolveSoundWf_some_of_stages`.
* The older `RischDECompletenessResidual` route is retained as a bridge from the fueled structural spine to
  the fuel-free executable surface, using the Wf/fueled agreement hypotheses already required by
  `crischDESolveSoundWf_field`. -/

section CompleteWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CFracGcdCoreWf β] [CRischField β] [CTowerGcdWitness β]
  [Algebra ℚ (CFieldSpec.K β)]

/-- **Fuel-free soundness, restated as `some ⟹ solvable`**: a successful `crischDESolveSoundWf`
run witnesses `FieldRDESolvable`, using the same Wf/fueled agreement hypotheses as
`crischDESolveSoundWf_field`. -/
theorem crischDESolveSoundWf_imp_solvable (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y) (hfit : InputFitsFuel f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : SoundWfInnerRegular f g) :
    FieldRDESolvable f g :=
  ⟨y, crischDESolveSoundWf_field f g y hsolve hfit hqwn hwf⟩

/-! ### Wf-native completeness residual -/

/-- **Fuel-free §6 completeness residual** `RischDECompletenessResidualWf f g`: the three Wf stage-completeness
facts consumed directly by `crischDESolveSoundWf_some_of_stages`. `hwn`: a solvable RDE has nonzero
`cWeakNormalizerGWf`. `hck`: the Wf weak-normalized input passes the §6.1 canon-normality gate. `hinner`:
the fuel-free inner solver `crischDERawSolveWf` succeeds on the reduced pair. This is the Wf-native analogue
of `RischDECompletenessResidual`; a `Prop`-bundle of stated §6 completeness assumptions, NO `sorry`. -/
structure RischDECompletenessResidualWf (f g : QFunNZG β) : Prop where
  /-- §6.1/Wf: a solvable RDE has a nonzero fuel-free weak normalizer. -/
  hwn : FieldRDESolvable f g →
    CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2) = false
  /-- §6.1/Wf: a solvable RDE passes the canon-normality gate after Wf weak normalization. -/
  hck : FieldRDESolvable f g →
    cisCanonNormalizedG (weakNormalizedF f
      (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) = true
  /-- §6.2–6.6/Wf: a solvable RDE makes the fuel-free inner solve succeed on the reduced pair. -/
  hinner : FieldRDESolvable f g →
    ∃ ytilde : QFunNZG β,
      crischDERawSolveWf
          (qReduce (weakNormalizedF f
            (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
          (qmulNZG (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) g)
        = some ytilde

omit [CTowerGcdWitness β] in
/-- **Fuel-free §6 RDE completeness modulo the Wf-native residual**: if the RDE is solvable and
`RischDECompletenessResidualWf` holds, then `crischDESolveSoundWf` returns `some`. Unlike
`crischDESolveSoundWf_complete_of_residual`, this completeness direction does not rewrite through the fueled
solver. -/
theorem crischDESolveSoundWf_complete_of_residualWf (f g : QFunNZG β)
    (hsol : FieldRDESolvable f g) (hres : RischDECompletenessResidualWf f g) :
    ∃ y, crischDESolveSoundWf f g = some y := by
  obtain ⟨ytilde, hinner⟩ := hres.hinner hsol
  exact ⟨_, crischDESolveSoundWf_some_of_stages f g ytilde (hres.hwn hsol) (hres.hck hsol) hinner⟩

/-- **The fuel-free §6 RDE solver DECIDES solvability modulo the Wf-native residual**:
`crischDESolveSoundWf f g` returns `some` iff the field-level RDE is solvable. The completeness direction is
Wf-native; the soundness direction still uses the existing Wf/fueled agreement hypotheses of
`crischDESolveSoundWf_field`. -/
theorem crischDESolveSoundWf_decides_of_residualWf (f g : QFunNZG β)
    (hres : RischDECompletenessResidualWf f g) (hfit : InputFitsFuel f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : SoundWfInnerRegular f g) :
    (∃ y, crischDESolveSoundWf f g = some y) ↔ FieldRDESolvable f g := by
  constructor
  · rintro ⟨y, hy⟩
    exact crischDESolveSoundWf_imp_solvable f g y hy hfit hqwn hwf
  · intro hsol
    exact crischDESolveSoundWf_complete_of_residualWf f g hsol hres

/-! ### Fueled-residual bridge retained for compatibility inside this library -/

omit [CTowerGcdWitness β] in
/-- **Fuel-free §6 RDE completeness modulo the deep residual**: if the RDE is solvable and the existing
`RischDECompletenessResidual` holds, then `crischDESolveSoundWf` returns `some`, provided the Wf weak
normalizer and inner RDE call agree with the fueled run on this input. -/
theorem crischDESolveSoundWf_complete_of_residual (f g : QFunNZG β)
    (hsol : FieldRDESolvable f g) (hres : RischDECompletenessResidual f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : SoundWfInnerRegular f g) :
    ∃ y, crischDESolveSoundWf f g = some y := by
  obtain ⟨y, hy⟩ := crischDESolveSound_complete_of_residual f g hsol hres
  refine ⟨y, ?_⟩
  rw [crischDESolveSoundWf_eq f g hqwn hwf]
  exact hy

/-- **The fuel-free §6 RDE solver DECIDES solvability modulo the deep residual**:
`crischDESolveSoundWf f g` returns `some` iff the field-level RDE is solvable, under the existing
`RischDECompletenessResidual`, the benign fuel budget used by soundness, and the Wf/fueled agreement
hypotheses. -/
theorem crischDESolveSoundWf_decides_of_residual (f g : QFunNZG β)
    (hres : RischDECompletenessResidual f g) (hfit : InputFitsFuel f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : SoundWfInnerRegular f g) :
    (∃ y, crischDESolveSoundWf f g = some y) ↔ FieldRDESolvable f g := by
  constructor
  · rintro ⟨y, hy⟩
    exact crischDESolveSoundWf_imp_solvable f g y hy hfit hqwn hwf
  · intro hsol
    exact crischDESolveSoundWf_complete_of_residual f g hsol hres hqwn hwf

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The fuel-free solver returns `some` iff the field-level RDE is solvable, modulo the same deep residual and
-- Wf/fueled agreement hypotheses.
example (f g : QFunNZG β) (hres : RischDECompletenessResidual f g) (hfit : InputFitsFuel f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : SoundWfInnerRegular f g) :
    (∃ y, crischDESolveSoundWf f g = some y) ↔ FieldRDESolvable f g :=
  crischDESolveSoundWf_decides_of_residual f g hres hfit hqwn hwf

-- The Wf-native residual gives the same decision statement with a fuel-free completeness direction.
example (f g : QFunNZG β) (hres : RischDECompletenessResidualWf f g) (hfit : InputFitsFuel f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : SoundWfInnerRegular f g) :
    (∃ y, crischDESolveSoundWf f g = some y) ↔ FieldRDESolvable f g :=
  crischDESolveSoundWf_decides_of_residualWf f g hres hfit hqwn hwf

end CompleteWf

/-! ## ★ Operational completeness witnesses (`native_decide`): the residual is non-vacuous

The residual clauses are non-vacuous: on concrete *solvable* level-2 RDEs the solver genuinely returns
`some`, and each residual gate (the §6.1 weak normalizer, the §6.1 check, the inner solve) is cleared —
certified by `native_decide` over `ℚ(x)(t₁)`. These are the completeness counterpart of the soundness
file's `crischDESolveSound_solves_*` (which check the *value*); here we record that a *solvable* RDE
produces a `some` at all (the completeness direction operationally), and that the §6.1 gates a solvable
input passes are exactly the residual's `hwn`/`hck`. (The unsolvable witness `f = 1/(t₁ − x)` returns
`none` — `crischDESolveSound_witness_none` — so the solver is *not* vacuously `some`.) -/

section OperationalWitnesses

/-- **The solver returns `some` on the solvable `Dy = 1`** (`crischDESolveSound_some_Dy_eq_one`,
`native_decide`): the integration RDE `Dy = 1` over `ℚ(x)(t₁)` is solvable (`y = t₁`), and the sound
solver returns `some` — the completeness direction witnessed operationally (a solvable input ⟹ `some`,
contrasted with the unsolvable witness's `none`). -/
theorem crischDESolveSound_some_Dy_eq_one :
    (crischDESolveSound (CField.zero : Lvl2) (CField.one : Lvl2)).isSome = true := by native_decide

/-- **The solver returns `some` on the solvable `Dy + y = t₁ + 1`** (`crischDESolveSound_some_Dy_plus_y`,
`native_decide`): the cancellation-path RDE `Dy + y = t₁ + 1` over `ℚ(x)(t₁)` is solvable (`y = t₁`), and
the sound solver returns `some` — operational completeness on the §6.6 primitive-cancellation path
(`f = 1 ≠ 0`, so the degree recursion runs, not just integration). -/
theorem crischDESolveSound_some_Dy_plus_y :
    (crischDESolveSound (CField.one : Lvl2) towerRdeLvl2GPlusOne).isSome = true := by native_decide

/-- **The §6.1 weak normalizer is nonzero on the solvable `Dy + y = t₁ + 1`**
(`cWeakNormalizer_nonzero_Dy_plus_y`, `native_decide`): for `f = 1` the §6.1 weak normalizer
`cWeakNormalizerG … = 1 ≠ 0` (`cisZeroG = false`) — the residual clause `hwn` holds concretely on a
solvable input (`f = 1` is already weakly normalized, so the normalizer is the unit `1`). -/
theorem cWeakNormalizer_nonzero_Dy_plus_y :
    CPolyG.cisZeroG (cWeakNormalizerG ([CField.one] : CPolyG (QFunNZG ℚ)) towerRischDEFuel
      (CField.one : Lvl2).1.1 (CField.one : Lvl2).1.2) = false := by native_decide

/-- **The §6.1 normality check passes on the solvable `Dy + y = t₁ + 1`**
(`cisCanonNormalizedG_true_Dy_plus_y`, `native_decide`): for `f = 1` the §6.1 check
`cisCanonNormalizedG (weakNormalizedF f q') = true` — the residual clause `hck` holds concretely on a
solvable input, contrasting with `cisCanonNormalizedG_witness_false` (the unsolvable witness, where it is
`false`). The check is a genuine, non-vacuous decision gate. -/
theorem cisCanonNormalizedG_true_Dy_plus_y :
    cisCanonNormalizedG (β := QFunNZG ℚ) (weakNormalizedF (CField.one : Lvl2)
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG (QFunNZG ℚ)) towerRischDEFuel
        (CField.one : Lvl2).1.1 (CField.one : Lvl2).1.2))) = true := by native_decide

end OperationalWitnesses

/-! ### Final verdict (stated precisely)

**Is the RDE solver a verified decision procedure?** **Modulo a precisely isolated deep §6 residual,
yes.** The fueled surface has `crischDESolveSound_decides_of_residual`; the fuel-free surface has
`crischDESolveSoundWf_decides_of_residualWf`, whose completeness direction uses the Wf-native residual
`RischDECompletenessResidualWf` and the Wf structural skeleton directly. The `⟹` half (soundness) is the
proven soundness theorem; the `⟸` half is completeness modulo the residual.

**Which completeness stages are closed, and which is the deep residual?**
* **Closed unconditionally.** The structural reductions `crischDESolveSound_some_iff` /
  `crischDESolveSound_some_of_stages` and `crischDESolveSoundWf_some_iff` /
  `crischDESolveSoundWf_some_of_stages` (completeness ⟺ the three stage tests passing — pure control flow);
  the lowest-terms reduction gate (never blocks, `reduceSoundOpt_eq`); the **base-field completeness**
  `rischDE_complete_base` (the constant-field oracle over `ℚ` is a genuine decision procedure, `b·y = g`
  solvable ↔ `some`).
* **The deep residual** (`RischDECompletenessResidual` / `RischDECompletenessResidualWf`, NEVER `sorry`).
  Three converse facts the engine does not self-certify: (a) the §6.1 weak normalizer is nonzero on a
  solvable input; (b) the §6.1 normality check passes on a solvable input (contrapositive: a non-normalizable
  denominator's RDE is unsolvable); (c) the **§6.2–6.6 inner solve succeeds on a solvable input** — the
  research-grade core, needing the §6.4 degree bound to be a provable upper bound on any solution's degree
  and the SPDE/poly-RDE solve to be exhaustive within it, *neither of which is formalized in the engine*
  (the §6 files prove only `some ⟹ cleared-identity`, never a degree-upper-bound or an exhaustiveness lemma).

So full `some ⟺ solvable` is reached **modulo the precise §6 completeness residual** on both fueled and
fuel-free surfaces — the degree-bound + SPDE/poly-RDE exhaustiveness (clause c) being the genuinely deep,
unformalized core; the §6.1 clauses (a, b) the converse of the §6.1 soundness facts. -/

/-! ### Axiom audit (the structural skeleton, base-field completeness, and the modular assembly are
axiom-clean; NO `native_decide`, NO `sorry`) -/

#print axioms crischDESolveSound_some_iff
#print axioms crischDESolveSound_some_of_stages
#print axioms crischDESolveSoundWf_some_iff
#print axioms crischDESolveSoundWf_some_of_stages
#print axioms rischDE_complete_base
#print axioms crischDESolveSound_complete_of_residual
#print axioms crischDESolveSound_decides_of_residual
#print axioms crischDESolveSoundWf_complete_of_residualWf
#print axioms crischDESolveSoundWf_decides_of_residualWf

end DeepWiki.SymbolicIntegration
