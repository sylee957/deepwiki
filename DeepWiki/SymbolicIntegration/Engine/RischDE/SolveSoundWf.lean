import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded
import DeepWiki.SymbolicIntegration.Engine.CanonNormalizedReduce

/-! # The sound recursive Risch-DE solver `crischDESolveSoundWf`

Weak-normalize, gate on `CFrac.canonNormalizedGate`, and solve the inner RDE through `cRischDE`.
`crischDESolveSoundWf_field` derives `D(Y) + F·Y = G` from the `RischDESoundnessWf` certificate. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

universe u v

/-! ## The solver `crischDESolveSoundWf`

Pipeline: weak-normalize, run the solvability check `CFrac.canonNormalizedGate`, reduce to lowest
terms, solve the inner RDE via `cRischDE`, and transform back by `y = ỹ/q'`. -/

section Solver

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β DensePoly]
  [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CPolyResultant DensePoly]
  [CRischField β]

/-- `crischDERawSolveWf ftilde gtilde`: run `cRischDE [1]` on the num/den components, re-lifting
the returned `(ynum, yden)` to `DenseFrac β` under a `cisZero` denominator guard. -/
def crischDERawSolveWf (ftilde gtilde : DenseFrac β) : Option (DenseFrac β) :=
  match DensePoly.cRischDE ([CCommRing.one] : DensePoly β) (CFrac.num ftilde) (CFrac.den ftilde)
      (CFrac.num gtilde) (CFrac.den gtilde) with
  | none => none
  | some (ynum, yden) =>
    if h : DensePoly.cisZero yden = false then some (CFrac.ofFraction ynum yden h) else none

omit [CFieldSpec β] [CFieldDomain β DensePoly] [CPolyResultant DensePoly] in
/-- `crischDERawSolveWf` returns `some y` exactly when `cRischDE [1]` returns a pair with nonzero
denominator and `y` is its `CFrac` lift. -/
theorem crischDERawSolveWf_some_iff (ftilde gtilde y : DenseFrac β) :
    crischDERawSolveWf ftilde gtilde = some y ↔
      ∃ ynum yden, ∃ hden : DensePoly.cisZero yden = false,
        DensePoly.cRischDE ([CCommRing.one] : DensePoly β) (CFrac.num ftilde) (CFrac.den ftilde)
          (CFrac.num gtilde) (CFrac.den gtilde)
            = some (ynum, yden) ∧
          CFrac.ofFraction ynum yden hden = y := by
  cases h :
      DensePoly.cRischDE ([CCommRing.one] : DensePoly β) (CFrac.num ftilde) (CFrac.den ftilde)
        (CFrac.num gtilde) (CFrac.den gtilde) with
  | none =>
      simp [crischDERawSolveWf, h]
  | some ypair =>
      rcases ypair with ⟨ynum, yden⟩
      by_cases hden : DensePoly.cisZero yden = false
      · simp [crischDERawSolveWf, h, hden]
      · simp [crischDERawSolveWf, h, hden]

/-- `crischDESolveSoundWf f g`: weak-normalize `f`, gate on `CFrac.canonNormalizedGate`, reduce to lowest
terms, solve via `crischDERawSolveWf`, and transform back by `y = ỹ/q'`. -/
def crischDESolveSoundWf (f g : DenseFrac β) : Option (DenseFrac β) :=
  let q : DensePoly β := cWeakNormalizer ([CCommRing.one] : DensePoly β) (CFrac.num f) (CFrac.den f)
  if DensePoly.cisZero q then none
  else
    let q' : DenseFrac β := CFrac.ofPoly q
    let ftilde : DenseFrac β := weakNormalizedF f q'
    if CFrac.canonNormalizedGate ftilde then
      match crischDERawSolveWf (CFrac.reduce ftilde) (mul q' g) with
      | none => none
      | some ytilde => some (mul ytilde (inv q'))
    else none

end Solver

/-! ## Structural facts about successful solves

Control-flow facts of a successful `crischDESolveSoundWf` run, letting downstream proofs consume the
solver without unfolding it. -/

section Reductions

variable {β : Type u} [CField β] [CFieldSpec.{u,v} β] [CDiffField β]
  [CFieldDomain β DensePoly] [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β]
  [CPolyResultant DensePoly] [CRischField β]

omit [CFieldSpec β] in
/-- A successful Wf sound solve has a nonzero Wf weak normalizer. -/
theorem crischDESolveSoundWf_weakNormalizer_ne_zero (f g y : DenseFrac β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    DensePoly.cisZero
      (cWeakNormalizer ([CCommRing.one] : DensePoly β) (CFrac.num f) (CFrac.den f)) = false := by
  set q : DensePoly β :=
    cWeakNormalizer ([CCommRing.one] : DensePoly β) (CFrac.num f) (CFrac.den f) with hq
  set q' : DenseFrac β := CFrac.ofPoly q with hq'
  set ftilde : DenseFrac β := weakNormalizedF f q' with hft
  rw [show crischDESolveSoundWf f g
      = (if DensePoly.cisZero q then none
         else if CFrac.canonNormalizedGate ftilde then
                match crischDERawSolveWf (CFrac.reduce ftilde) (mul q' g) with
                | none => none
                | some ytilde => some (mul ytilde (inv q'))
              else none) from rfl] at hsolve
  by_cases hqz : DensePoly.cisZero q = true
  · rw [if_pos hqz] at hsolve
    exact absurd hsolve (by simp)
  · exact by
      rw [Bool.not_eq_true] at hqz
      simpa [hq] using hqz

omit [CFieldSpec β] in
/-- A successful Wf sound solve passed the canonical-normality check. -/
theorem crischDESolveSoundWf_check (f g y : DenseFrac β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    CFrac.canonNormalizedGate (weakNormalizedF f
      (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β)
        (CFrac.num f) (CFrac.den f)))) = true := by
  set q : DensePoly β :=
    cWeakNormalizer ([CCommRing.one] : DensePoly β) (CFrac.num f) (CFrac.den f) with hq
  set q' : DenseFrac β := CFrac.ofPoly q with hq'
  set ftilde : DenseFrac β := weakNormalizedF f q' with hft
  rw [show crischDESolveSoundWf f g
      = (if DensePoly.cisZero q then none
         else if CFrac.canonNormalizedGate ftilde then
                match crischDERawSolveWf (CFrac.reduce ftilde) (mul q' g) with
                | none => none
                | some ytilde => some (mul ytilde (inv q'))
              else none) from rfl] at hsolve
  by_cases hqz : DensePoly.cisZero q = true
  · rw [if_pos hqz] at hsolve
    exact absurd hsolve (by simp)
  · rw [if_neg hqz] at hsolve
    by_cases hck : CFrac.canonNormalizedGate ftilde = true
    · simpa [hq, hq', hft] using hck
    · rw [if_neg hck] at hsolve
      exact absurd hsolve (by simp)

/-- A successful Wf sound solve supplies the Wf canonical-normality proposition. -/
theorem crischDESolveSoundWf_isCanonNormalized [LawfulCPolyGcd.{u,v} DensePoly β]
    (f g y : DenseFrac β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    IsCanonNormalized f
      (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β)
        (CFrac.num f) (CFrac.den f))) :=
  (canonNormalizedGate_iff f _).mp (crischDESolveSoundWf_check f g y hsolve)

end Reductions

/-! ## Soundness under the `RischDESoundnessWf` certificate -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β DensePoly]
  [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CPolyResultant DensePoly]
  [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- `RischDESoundnessWf f g`: every successful `crischDESolveSoundWf` run satisfies the field-level Risch-DE identity. -/
structure RischDESoundnessWf (f g : DenseFrac β) : Prop where
  /-- Every successful Wf solve returns a genuine field-level Risch-DE solution. -/
  sound : ∀ y : DenseFrac β, crischDESolveSoundWf f g = some y →
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β)
          (am β (toPoly (CFrac.num y)) / am β (toPoly (CFrac.den y)))
        + am β (toPoly (CFrac.num f)) / am β (toPoly (CFrac.den f))
          * (am β (toPoly (CFrac.num y)) / am β (toPoly (CFrac.den y)))
      = am β (toPoly (CFrac.num g)) / am β (toPoly (CFrac.den g))

/-- `crischDESolveSoundWf_field`: under `RischDESoundnessWf f g`, a successful `y` solves
`D(Y) + F·Y = G` for the original `f, g`. -/
theorem crischDESolveSoundWf_field (f g y : DenseFrac β)
    (hsolve : crischDESolveSoundWf f g = some y)
    (hsound : RischDESoundnessWf f g) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β)
          (am β (toPoly (CFrac.num y)) / am β (toPoly (CFrac.den y)))
        + am β (toPoly (CFrac.num f)) / am β (toPoly (CFrac.den f))
          * (am β (toPoly (CFrac.num y)) / am β (toPoly (CFrac.den y)))
      = am β (toPoly (CFrac.num g)) / am β (toPoly (CFrac.den g)) :=
  hsound.sound y hsolve

/-! ### Restatement example -/

example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β DensePoly]
    [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CPolyResultant DensePoly]
    [CRischField β] [Algebra ℚ (CFieldSpec.K β)]
    (f g y : DenseFrac β) (hsolve : crischDESolveSoundWf f g = some y)
    (hsound : RischDESoundnessWf f g) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β)
          (am β (toPoly (CFrac.num y)) / am β (toPoly (CFrac.den y)))
        + am β (toPoly (CFrac.num f)) / am β (toPoly (CFrac.den f))
          * (am β (toPoly (CFrac.num y)) / am β (toPoly (CFrac.den y)))
      = am β (toPoly (CFrac.num g)) / am β (toPoly (CFrac.den g)) :=
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
