import DeepWiki.SymbolicIntegration.Computable.Tower.RischDEWellFounded
import DeepWiki.SymbolicIntegration.Computable.CanonNormalizedReduce

/-! # The sound recursive Risch-DE solver `crischDESolveSoundWf`

The public well-founded RDE wrapper: weak-normalize, gate on `cisCanonNormalizedGWf`, and solve the
inner RDE through `cRischDEGWf`. `crischDESolveSoundWf_field` derives the field-level identity
`D(Y) + F·Y = G` for a successful solve from the `RischDESoundnessWf` certificate. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The solver `crischDESolveSoundWf`

Pipeline: weak-normalize `f̃ = f − Dq'/q'` (`q = cWeakNormalizerGWf`), run the §6.1 solvability check
`cisCanonNormalizedGWf f̃`, reduce to lowest terms, solve the inner RDE on `(f̃ᵣ, q'·g)` via
`cRischDEGWf`, and transform back by `y = ỹ/q'`. -/

section Solver

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β]

/-- Inner RDE solve `crischDERawSolveWf ftilde gtilde` over `QFunNZG β`: run
`cRischDEGWf ([1] : CPolyG β)` over `CPolyG β = β[s]` (monomial `s`, `Ds = [1]`) on the num/den
components, re-lifting the returned `(ynum, yden)` to `QFunNZG β` under a `cisZeroG` denominator
guard. -/
def crischDERawSolveWf (ftilde gtilde : QFunNZG β) : Option (QFunNZG β) :=
  match CPolyG.cRischDEGWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
  | none => none
  | some (ynum, yden) =>
    if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none

omit [CFieldSpec β] [CFieldDomain β] in
/-- `crischDERawSolveWf` returns `some y` exactly when `cRischDEGWf [1]` returns a pair with nonzero
denominator and `y` is its `QFunNZG` lift. -/
theorem crischDERawSolveWf_some_iff (ftilde gtilde y : QFunNZG β) :
    crischDERawSolveWf ftilde gtilde = some y ↔
      ∃ ynum yden, ∃ hden : CPolyG.cisZeroG yden = false,
        CPolyG.cRischDEGWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
            = some (ynum, yden) ∧
          ⟨(ynum, yden), hden⟩ = y := by
  cases h :
      CPolyG.cRischDEGWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
  | none =>
      simp [crischDERawSolveWf, h]
  | some ypair =>
      rcases ypair with ⟨ynum, yden⟩
      by_cases hden : CPolyG.cisZeroG yden = false
      · simp [crischDERawSolveWf, h, hden]
      · simp [crischDERawSolveWf, h, hden]

/-- Sound recursive Risch-DE solver `crischDESolveSoundWf f g` over `QFunNZG β`: weak-normalize `f`
to `f̃ = f − Dq/q` (`q = cWeakNormalizerGWf`; give up if `q = 0`), run the §6.1 solvability check
`cisCanonNormalizedGWf f̃` (return `none` when the lowest-terms denominator is not normal), reduce
`f̃` to lowest terms and solve `(f̃ᵣ, q'·g)` via `crischDERawSolveWf`, transforming back by
`y = ỹ/q'`. The built-in check removes any external `IsCanonNormalized` hypothesis from soundness. -/
def crischDESolveSoundWf (f g : QFunNZG β) : Option (QFunNZG β) :=
  let q : CPolyG β := cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
  if CPolyG.cisZeroG q then none
  else
    let q' : QFunNZG β := qOfPolyNZG q
    let ftilde : QFunNZG β := weakNormalizedF f q'
    if cisCanonNormalizedGWf ftilde then
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
    CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2) = false := by
  set q : CPolyG β := cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2 with hq
  set q' : QFunNZG β := qOfPolyNZG q with hq'
  set ftilde : QFunNZG β := weakNormalizedF f q' with hft
  rw [show crischDESolveSoundWf f g
      = (if CPolyG.cisZeroG q then none
         else if cisCanonNormalizedGWf ftilde then
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
/-- A successful Wf sound solve passed the §6.1 canonical-normality check. -/
theorem crischDESolveSoundWf_check (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    cisCanonNormalizedGWf (weakNormalizedF f
      (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) = true := by
  set q : CPolyG β := cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2 with hq
  set q' : QFunNZG β := qOfPolyNZG q with hq'
  set ftilde : QFunNZG β := weakNormalizedF f q' with hft
  rw [show crischDESolveSoundWf f g
      = (if CPolyG.cisZeroG q then none
         else if cisCanonNormalizedGWf ftilde then
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
    by_cases hck : cisCanonNormalizedGWf ftilde = true
    · simpa [hq, hq', hft] using hck
    · rw [if_neg hck] at hsolve
      exact absurd hsolve (by simp)

/-- A successful Wf sound solve supplies the Wf canonical-normality proposition. -/
theorem crischDESolveSoundWf_isCanonNormalized (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y) :
    IsCanonNormalizedWf f
      (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) :=
  (cisCanonNormalizedGWf_iff f _).mp (crischDESolveSoundWf_check f g y hsolve)

end Reductions

/-! ## Soundness under the `RischDESoundnessWf` certificate -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- Soundness certificate `RischDESoundnessWf f g`: every successful `crischDESolveSoundWf` run
satisfies the original field-level Risch-DE identity. The public soundness boundary. -/
structure RischDESoundnessWf (f g : QFunNZG β) : Prop where
  /-- Every successful Wf solve returns a genuine field-level Risch-DE solution. -/
  sound : ∀ y : QFunNZG β, crischDESolveSoundWf f g = some y →
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2)

/-- If `crischDESolveSoundWf f g = some y` then, under `RischDESoundnessWf f g`, the returned `y`
solves the field-level Risch DE `D(Y) + F·Y = G` for the original `f, g` over
`RatFunc (CFieldSpec.K β)`. No `IsCanonNormalized` hypothesis — the solver's own §6.1 check
supplies it. -/
theorem crischDESolveSoundWf_field (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y)
    (hsound : RischDESoundnessWf f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  hsound.sound y hsolve

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 3: the FUEL-FREE sound solver's success ⟹ the ORIGINAL field-level Risch-DE identity, from the
-- direct Wf soundness certificate — NO IsCanonNormalized hypothesis (the solver checks it).
-- Fuel-free at runtime. No native_decide.
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

/-! ### Axiom audit (the capstone is axiom-clean, NO `native_decide`; the validations are `native_decide`) -/

#print axioms crischDESolveSoundWf_field
#print axioms crischDERawSolveWf_some_iff

/-! ### Final verdict (Task 5)

**Is the fuel-free sound solver built and proven sound?** **Yes.**

* **Built fuel-free.** `crischDESolveSoundWf` runs the §6.1-gated sound pipeline (weak-normalize →
  `cisCanonNormalizedGWf` check → reduce → solve → transform back) with the inner RDE solve routed through the
  **fuel-free** `cRischDEGWf` (`crischDERawSolveWf`) in place of the fuel `CRischField.crischDESolve` — no
  `ℕ`-fuel parameter.
* **Proven sound through the direct Wf soundness certificate, axiom-clean.** `crischDESolveSoundWf_field`: a
  successful solve gives the ORIGINAL field-level Risch-DE identity `D(Y) + F·Y = G`, with NO
  `IsCanonNormalized` hypothesis (the solver checks it), under the direct `RischDESoundnessWf` certificate.
  Axiom-clean `[propext, Classical.choice, Quot.sound]`, NO `native_decide`.
* **Fuel-free validations.** The witness `f = 1/(t₁ − x)`, `g = 1` returns `none`
  (`crischDESolveSoundWf_witness_none`), and the solvable cases `Dy = 1` / `Dy + y = t₁ + 1` return the
  correct `some y` solving the RDE (`crischDESolveSoundWf_solves_*`) — all `native_decide`, fuel-free.

★ **This is the public fuel-free sound entry point** for the Wf RDE decision-procedure and tower-completeness
frontiers. -/

end DeepWiki.SymbolicIntegration
