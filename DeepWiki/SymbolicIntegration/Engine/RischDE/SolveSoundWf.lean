import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded
import DeepWiki.SymbolicIntegration.Engine.CanonNormalizedReduce

/-! # The sound recursive Risch-DE solver `crischDESolveSoundWf`

Weak-normalize, gate on `cisCanonNormalized`, and solve the inner RDE through `cRischDE`.
`crischDESolveSoundWf_field` derives `D(Y) + F·Y = G` from the `RischDESoundnessWf` certificate. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-! ## The solver `crischDESolveSoundWf`

Pipeline: weak-normalize, run the solvability check `cisCanonNormalized`, reduce to lowest
terms, solve the inner RDE via `cRischDE`, and transform back by `y = ỹ/q'`. -/

section Solver

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β]

/-- `crischDERawSolveWf ftilde gtilde`: run `cRischDE [1]` on the num/den components, re-lifting
the returned `(ynum, yden)` to `CFrac β` under a `cisZero` denominator guard. -/
def crischDERawSolveWf (ftilde gtilde : CFrac β) : Option (CFrac β) :=
  match DensePoly.cRischDE ([CCommRing.one] : DensePoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
  | none => none
  | some (ynum, yden) =>
    if h : DensePoly.cisZero yden = false then some ⟨(ynum, yden), h⟩ else none

omit [CFieldSpec β] [CFieldDomain β] in
/-- `crischDERawSolveWf` returns `some y` exactly when `cRischDE [1]` returns a pair with nonzero
denominator and `y` is its `CFrac` lift. -/
theorem crischDERawSolveWf_some_iff (ftilde gtilde y : CFrac β) :
    crischDERawSolveWf ftilde gtilde = some y ↔
      ∃ ynum yden, ∃ hden : DensePoly.cisZero yden = false,
        DensePoly.cRischDE ([CCommRing.one] : DensePoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
            = some (ynum, yden) ∧
          ⟨(ynum, yden), hden⟩ = y := by
  cases h :
      DensePoly.cRischDE ([CCommRing.one] : DensePoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
  | none =>
      simp [crischDERawSolveWf, h]
  | some ypair =>
      rcases ypair with ⟨ynum, yden⟩
      by_cases hden : DensePoly.cisZero yden = false
      · simp [crischDERawSolveWf, h, hden]
      · simp [crischDERawSolveWf, h, hden]

/-- `crischDESolveSoundWf f g`: weak-normalize `f`, gate on `cisCanonNormalized`, reduce to lowest
terms, solve via `crischDERawSolveWf`, and transform back by `y = ỹ/q'`. -/
def crischDESolveSoundWf (f g : CFrac β) : Option (CFrac β) :=
  let q : DensePoly β := cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2
  if DensePoly.cisZero q then none
  else
    let q' : CFrac β := qOfPolyNZ q
    let ftilde : CFrac β := weakNormalizedF f q'
    if cisCanonNormalized ftilde then
      match reduceSoundOpt ftilde with
      | none => none
      | some ftildeR =>
        match crischDERawSolveWf ftildeR (qmulNZ q' g) with
        | none => none
        | some ytilde => some (qmulNZ ytilde (qinvNZ q'))
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
theorem crischDESolveSoundWf_weakNormalizer_ne_zero (f g y : CFrac β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    DensePoly.cisZero (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2) = false := by
  set q : DensePoly β := cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2 with hq
  set q' : CFrac β := qOfPolyNZ q with hq'
  set ftilde : CFrac β := weakNormalizedF f q' with hft
  rw [show crischDESolveSoundWf f g
      = (if DensePoly.cisZero q then none
         else if cisCanonNormalized ftilde then
                match reduceSoundOpt ftilde with
                | none => none
                | some ftildeR =>
                  match crischDERawSolveWf ftildeR (qmulNZ q' g) with
                  | none => none
                  | some ytilde => some (qmulNZ ytilde (qinvNZ q'))
              else none) from rfl] at hsolve
  by_cases hqz : DensePoly.cisZero q = true
  · rw [if_pos hqz] at hsolve
    exact absurd hsolve (by simp)
  · exact by
      rw [Bool.not_eq_true] at hqz
      simpa [hq] using hqz

omit [CFieldSpec β] in
/-- A successful Wf sound solve passed the canonical-normality check. -/
theorem crischDESolveSoundWf_check (f g y : CFrac β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    cisCanonNormalized (weakNormalizedF f
      (qOfPolyNZ (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2))) = true := by
  set q : DensePoly β := cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2 with hq
  set q' : CFrac β := qOfPolyNZ q with hq'
  set ftilde : CFrac β := weakNormalizedF f q' with hft
  rw [show crischDESolveSoundWf f g
      = (if DensePoly.cisZero q then none
         else if cisCanonNormalized ftilde then
                match reduceSoundOpt ftilde with
                | none => none
                | some ftildeR =>
                  match crischDERawSolveWf ftildeR (qmulNZ q' g) with
                  | none => none
                  | some ytilde => some (qmulNZ ytilde (qinvNZ q'))
              else none) from rfl] at hsolve
  by_cases hqz : DensePoly.cisZero q = true
  · rw [if_pos hqz] at hsolve
    exact absurd hsolve (by simp)
  · rw [if_neg hqz] at hsolve
    by_cases hck : cisCanonNormalized ftilde = true
    · simpa [hq, hq', hft] using hck
    · rw [if_neg hck] at hsolve
      exact absurd hsolve (by simp)

/-- A successful Wf sound solve supplies the Wf canonical-normality proposition. -/
theorem crischDESolveSoundWf_isCanonNormalized (f g y : CFrac β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    IsCanonNormalizedWf f
      (qOfPolyNZ (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.1.1 f.1.2)) :=
  (cisCanonNormalizedG_iff f _).mp (crischDESolveSoundWf_check f g y hsolve)

end Reductions

/-! ## Soundness under the `RischDESoundnessWf` certificate -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- `RischDESoundnessWf f g`: every successful `crischDESolveSoundWf` run satisfies the field-level Risch-DE identity. -/
structure RischDESoundnessWf (f g : CFrac β) : Prop where
  /-- Every successful Wf solve returns a genuine field-level Risch-DE solution. -/
  sound : ∀ y : CFrac β, crischDESolveSoundWf f g = some y →
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β)
          (am β (toPoly y.1.1) / am β (toPoly y.1.2))
        + am β (toPoly f.1.1) / am β (toPoly f.1.2)
          * (am β (toPoly y.1.1) / am β (toPoly y.1.2))
      = am β (toPoly g.1.1) / am β (toPoly g.1.2)

/-- `crischDESolveSoundWf_field`: under `RischDESoundnessWf f g`, a successful `y` solves
`D(Y) + F·Y = G` for the original `f, g`. -/
theorem crischDESolveSoundWf_field (f g y : CFrac β)
    (hsolve : crischDESolveSoundWf f g = some y)
    (hsound : RischDESoundnessWf f g) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β)
          (am β (toPoly y.1.1) / am β (toPoly y.1.2))
        + am β (toPoly f.1.1) / am β (toPoly f.1.2)
          * (am β (toPoly y.1.1) / am β (toPoly y.1.2))
      = am β (toPoly g.1.1) / am β (toPoly g.1.2) :=
  hsound.sound y hsolve

/-! ### Restatement example -/

example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : CFrac β) (hsolve : crischDESolveSoundWf f g = some y)
    (hsound : RischDESoundnessWf f g) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β)
          (am β (toPoly y.1.1) / am β (toPoly y.1.2))
        + am β (toPoly f.1.1) / am β (toPoly f.1.2)
          * (am β (toPoly y.1.1) / am β (toPoly y.1.2))
      = am β (toPoly g.1.1) / am β (toPoly g.1.2) :=
  crischDESolveSoundWf_field f g y hsolve hsound

end Capstone

/-! ## `native_decide` examples

The solver's behaviour over the level-2 field `ℚ(x)(t₁)`, checked by `native_decide`: the
unsolvable witness returns `none`, and the solvable cases `Dy = 1` and `Dy + y = t₁ + 1` solve. -/

section Examples

/-- `crischDESolveSoundWf_witness_none`: `crischDESolveSoundWf witnessF 1 = none` on the unsolvable
`f = 1/(t₁ − x)`, `g = 1`. -/
theorem crischDESolveSoundWf_witness_none :
    crischDESolveSoundWf witnessF (CCommRing.one : Lvl2) = none := by native_decide

/-- `crischDESolveSoundWf_solves_Dy_eq_one`: `crischDESolveSoundWf 0 1` at level 2 returns `some y`
with `D(y) + 0·y = 1`. -/
theorem crischDESolveSoundWf_solves_Dy_eq_one :
    (match crischDESolveSoundWf (CCommRing.zero : Lvl2) (CCommRing.one : Lvl2) with
      | some y =>
          CCommRing.isZero
            (CField.sub (CCommRing.add (CDiffField.cderiv y) (CCommRing.mul CCommRing.zero y)) CCommRing.one)
      | none => false) = true := by native_decide

/-- `crischDESolveSoundWf_solves_Dy_plus_y`: `crischDESolveSoundWf 1 (t₁ + 1)` at level 2 returns
`some y` with `D(y) + 1·y = t₁ + 1`. -/
theorem crischDESolveSoundWf_solves_Dy_plus_y :
    (match crischDESolveSoundWf (CCommRing.one : Lvl2) towerRdeLvl2GPlusOne with
      | some y =>
          CCommRing.isZero
            (CField.sub (CCommRing.add (CDiffField.cderiv y) (CCommRing.mul CCommRing.one y))
              towerRdeLvl2GPlusOne)
      | none => false) = true := by native_decide

end Examples

end DeepWiki.SymbolicIntegration
