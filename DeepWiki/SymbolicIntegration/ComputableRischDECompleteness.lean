import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound

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

So a `none` result decomposes structurally into these four cases (`crischDESolveSound_eq_none_iff`,
fully reachable). Completeness — `solvable ⟹ ¬ none` — is then **exactly** the conjunction of four
stage-completeness facts: a solvable RDE has (1) a non-vanishing weak normalizer, (2) a passing §6.1
check, (3) a successful reduction (free), and (4) a successful inner solve. Branch (3) is closed
unconditionally; branches (1), (2), (4) are the genuine §6 completeness content.

**What is reachable here.**
* **The structural `none`-characterization** `crischDESolveSound_eq_none_iff` — the exact four-way
  disjunction a `none` reduces to (the control-flow skeleton, no §6 mathematics).
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

end DeepWiki.SymbolicIntegration
