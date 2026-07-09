import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded
import DeepWiki.SymbolicIntegration.Engine.CanonNormalizedReduce

/-! # The sound recursive Risch-DE solver `crischDESolveSoundWf`

Weak-normalize, gate on `cisCanonNormalizedG`, and solve the inner RDE through `cRischDEG`.
`crischDESolveSoundWf_field` derives `D(Y) + F·Y = G` from the `RischDESoundnessWf` certificate. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPolyG QFunNZG

/-! ## The solver `crischDESolveSoundWf`

Pipeline: weak-normalize, run the solvability check `cisCanonNormalizedG`, reduce to lowest
terms, solve the inner RDE via `cRischDEG`, and transform back by `y = ỹ/q'`. -/

section Solver

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β]

/-- `crischDERawSolveWf ftilde gtilde`: run `cRischDEG [1]` on the num/den components, re-lifting
the returned `(ynum, yden)` to `QFunNZG β` under a `cisZeroG` denominator guard. -/
def crischDERawSolveWf (ftilde gtilde : QFunNZG β) : Option (QFunNZG β) :=
  match CPolyG.cRischDEG ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
  | none => none
  | some (ynum, yden) =>
    if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none

omit [CFieldSpec β] [CFieldDomain β] in
/-- `crischDERawSolveWf` returns `some y` exactly when `cRischDEG [1]` returns a pair with nonzero
denominator and `y` is its `QFunNZG` lift. -/
theorem crischDERawSolveWf_some_iff (ftilde gtilde y : QFunNZG β) :
    crischDERawSolveWf ftilde gtilde = some y ↔
      ∃ ynum yden, ∃ hden : CPolyG.cisZeroG yden = false,
        CPolyG.cRischDEG ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
            = some (ynum, yden) ∧
          ⟨(ynum, yden), hden⟩ = y := by
  cases h :
      CPolyG.cRischDEG ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
  | none =>
      simp [crischDERawSolveWf, h]
  | some ypair =>
      rcases ypair with ⟨ynum, yden⟩
      by_cases hden : CPolyG.cisZeroG yden = false
      · simp [crischDERawSolveWf, h, hden]
      · simp [crischDERawSolveWf, h, hden]

/-- `crischDESolveSoundWf f g`: weak-normalize `f`, gate on `cisCanonNormalizedG`, reduce to lowest
terms, solve via `crischDERawSolveWf`, and transform back by `y = ỹ/q'`. -/
def crischDESolveSoundWf (f g : QFunNZG β) : Option (QFunNZG β) :=
  let q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) f.1.1 f.1.2
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

/-! ## Structural facts about successful solves

Control-flow facts of a successful `crischDESolveSoundWf` run, letting downstream proofs consume the
solver without unfolding it. -/

section Reductions

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]
  [CRischField β]

omit [CFieldSpec β] in
/-- A successful Wf sound solve has a nonzero Wf weak normalizer. -/
theorem crischDESolveSoundWf_weakNormalizer_ne_zero (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    CPolyG.cisZeroG (cWeakNormalizerG ([CField.one] : CPolyG β) f.1.1 f.1.2) = false := by
  set q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) f.1.1 f.1.2 with hq
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
              else none) from rfl] at hsolve
  by_cases hqz : CPolyG.cisZeroG q = true
  · rw [if_pos hqz] at hsolve
    exact absurd hsolve (by simp)
  · exact by
      rw [Bool.not_eq_true] at hqz
      simpa [hq] using hqz

omit [CFieldSpec β] in
/-- A successful Wf sound solve passed the canonical-normality check. -/
theorem crischDESolveSoundWf_check (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    cisCanonNormalizedG (weakNormalizedF f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) f.1.1 f.1.2))) = true := by
  set q : CPolyG β := cWeakNormalizerG ([CField.one] : CPolyG β) f.1.1 f.1.2 with hq
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
              else none) from rfl] at hsolve
  by_cases hqz : CPolyG.cisZeroG q = true
  · rw [if_pos hqz] at hsolve
    exact absurd hsolve (by simp)
  · rw [if_neg hqz] at hsolve
    by_cases hck : cisCanonNormalizedG ftilde = true
    · simpa [hq, hq', hft] using hck
    · rw [if_neg hck] at hsolve
      exact absurd hsolve (by simp)

/-- A successful Wf sound solve supplies the Wf canonical-normality proposition. -/
theorem crischDESolveSoundWf_isCanonNormalized (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    IsCanonNormalizedWf f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG β) f.1.1 f.1.2)) :=
  (cisCanonNormalizedG_iff f _).mp (crischDESolveSoundWf_check f g y hsolve)

end Reductions

/-! ## Soundness under the `RischDESoundnessWf` certificate -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- `RischDESoundnessWf f g`: every successful `crischDESolveSoundWf` run satisfies the field-level Risch-DE identity. -/
structure RischDESoundnessWf (f g : QFunNZG β) : Prop where
  /-- Every successful Wf solve returns a genuine field-level Risch-DE solution. -/
  sound : ∀ y : QFunNZG β, crischDESolveSoundWf f g = some y →
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2)

/-- `crischDESolveSoundWf_field`: under `RischDESoundnessWf f g`, a successful `y` solves
`D(Y) + F·Y = G` for the original `f, g`. -/
theorem crischDESolveSoundWf_field (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y)
    (hsound : RischDESoundnessWf f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  hsound.sound y hsolve

/-! ### Restatement example -/

example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : QFunNZG β) (hsolve : crischDESolveSoundWf f g = some y)
    (hsound : RischDESoundnessWf f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolveSoundWf_field f g y hsolve hsound

end Capstone

/-! ## `native_decide` examples

The solver's behaviour over the level-2 field `ℚ(x)(t₁)`, checked by `native_decide`: the
unsolvable witness returns `none`, and the solvable cases `Dy = 1` and `Dy + y = t₁ + 1` solve. -/

section Examples

/-- `crischDESolveSoundWf_witness_none`: `crischDESolveSoundWf witnessF 1 = none` on the unsolvable
`f = 1/(t₁ − x)`, `g = 1`. -/
theorem crischDESolveSoundWf_witness_none :
    crischDESolveSoundWf witnessF (CField.one : Lvl2) = none := by native_decide

/-- `crischDESolveSoundWf_solves_Dy_eq_one`: `crischDESolveSoundWf 0 1` at level 2 returns `some y`
with `D(y) + 0·y = 1`. -/
theorem crischDESolveSoundWf_solves_Dy_eq_one :
    (match crischDESolveSoundWf (CField.zero : Lvl2) (CField.one : Lvl2) with
      | some y =>
          CField.isZero
            (CField.sub (CField.add (CDiffField.cderiv y) (CField.mul CField.zero y)) CField.one)
      | none => false) = true := by native_decide

/-- `crischDESolveSoundWf_solves_Dy_plus_y`: `crischDESolveSoundWf 1 (t₁ + 1)` at level 2 returns
`some y` with `D(y) + 1·y = t₁ + 1`. -/
theorem crischDESolveSoundWf_solves_Dy_plus_y :
    (match crischDESolveSoundWf (CField.one : Lvl2) towerRdeLvl2GPlusOne with
      | some y =>
          CField.isZero
            (CField.sub (CField.add (CDiffField.cderiv y) (CField.mul CField.one y))
              towerRdeLvl2GPlusOne)
      | none => false) = true := by native_decide

end Examples

end DeepWiki.SymbolicIntegration
