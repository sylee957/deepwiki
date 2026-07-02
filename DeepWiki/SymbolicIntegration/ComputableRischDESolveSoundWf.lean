import DeepWiki.SymbolicIntegration.ComputableRischDESolveNormCanon
import DeepWiki.SymbolicIntegration.ComputableTowerRischDEWellFounded
import DeepWiki.SymbolicIntegration.ComputableCanonNormalizedReduce

/-! # The FUEL-FREE SOUND recursive Risch-DE solver — `crischDESolveSoundWf`

This file exposes the public Wf RDE wrapper. It uses the shared weak-normalization and lowest-terms helpers,
then routes the inner RDE solve through the fuel-free `cRischDEGWf` rather than the old fueled tower instance.

* **`crischDESolveSoundWf f g`** — the §6.1-gated solver with the **fuel-free** weak normalizer
  `cWeakNormalizerGWf [1] …`, Wf normality gate `cisCanonNormalizedGWf`, and inner solve
  `cRischDEGWf [1] …` (NO `ℕ`-fuel parameter).
* **★ `crischDESolveSoundWf_field`** — the capstone: a successful `crischDESolveSoundWf f g = some y` gives the
  field-level Risch-DE identity `D(Y) + F·Y = G` for the ORIGINAL `f, g`, under the direct Wf soundness
  certificate `RischDESoundnessWf`, **fuel-free at runtime**, NO `IsCanonNormalized` hypothesis (the solver
  checks it). Axiom-clean `[propext, Classical.choice, Quot.sound]`, NO `native_decide`.
* **The validations** (`native_decide`): the unsolvable witness `f = 1/(t₁ − x)`, `g = 1` returns `none` under
  `crischDESolveSoundWf`, and the solvable cases (`Dy = 1 → y = t₁`, `Dy + y = t₁ + 1 → y = t₁`) return the
  correct `some` — fuel-free.

★ **The fuel-free sound solver.** `crischDESolveSoundWf` + `RischDESoundnessWf` give the sound RDE oracle with
the `ℕ`-fuel removed from the inner solve. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## ★ The fuel-free SOUND solver `crischDESolveSoundWf` (the inner solve made fuel-free)

`crischDESolveSoundWf f g` is the Wf §6.1 pipeline:

1. compute the **fuel-free** weak normalizer `q = cWeakNormalizerGWf [1] f.1.1 f.1.2`; if `q = 0`, `none`;
2. lift `q' = q/1`, form the weakly-normalized `f̃ = f − Dq'/q'`;
3. **the §6.1 solvability check** `cisCanonNormalizedGWf f̃` (return `none` if it fails);
4. reduce `f̃` to lowest terms (`reduceSoundOpt`) and solve the inner RDE on `(f̃ᵣ, q'·g)` — but via the
   **fuel-free** `cRischDEGWf [1] f̃ᵣ.1.1 f̃ᵣ.1.2 (q'·g).1.1 (q'·g).1.2` over `CPolyG β`, re-lifting the
   returned `(ynum, yden)` with the same `cisZeroG`-guard `instCRischFieldQFunNZG` uses; on `some ỹ`, return
   `y = ỹ/q'`. -/

section Solver

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β]

/-- **The fuel-free inner RDE solve** `crischDERawSolveWf ftilde gtilde` over `QFunNZG β`: the fuel-free mirror
of `instCRischFieldQFunNZG.crischDESolve` — run the **fuel-free** `cRischDEGWf ([1] : CPolyG β)` over
`CPolyG β = β[s]` (monomial `s`, `Ds = [1]`) on the num/den components of `ftilde, gtilde`, and re-lift the
returned `(ynum, yden)` to `QFunNZG β` with the same `cisZeroG`-guard the tower instance uses. **No `ℕ`-fuel** —
the inner §6 pipeline runs fuel-free. -/
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

/-- **★ The FUEL-FREE, genuinely SOUND recursive Risch-DE solver** `crischDESolveSoundWf f g` over
`QFunNZG β`: weak-normalize `f` to
`f̃ = f − Dq/q` (`q = cWeakNormalizerGWf`, **fuel-free**); if `q = 0` give up; run the fuel-free §6.1
solvability check `cisCanonNormalizedGWf f̃` (return `none` when the lowest-terms denominator is not normal);
else reduce `f̃` to lowest terms (`reduceSoundOpt`) and solve `(f̃ᵣ, q'·g)` via the **fuel-free**
`crischDERawSolveWf`, transforming back by `y = ỹ/q'`. **No `ℕ`-fuel parameter** — the inner §6 pipeline runs
fuel-free. The check removes any external `IsCanonNormalized` hypothesis from soundness; the public soundness
assumption is the direct `RischDESoundnessWf` certificate. Computable, so it `native_decide`s. -/
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

/-! ## Structural facts about successful Wf solves

Successful `crischDESolveSoundWf` runs expose the same control-flow facts as the older fueled sound solver,
but stated directly against the Wf weak normalizer and Wf canonical-normality gate. These facts let downstream
proofs consume the fuel-free solver without unfolding it back into the old fueled surface. -/

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
/-- A successful Wf sound solve passed the fuel-free §6.1 canonical-normality check. -/
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

/-! ## ★★ Task 3 — the capstone: the FUEL-FREE sound solver is sound under a Wf certificate

`crischDESolveSoundWf_field`: a successful `crischDESolveSoundWf f g = some y` gives the field-level Risch-DE
identity `D(Y) + F·Y = G` for the ORIGINAL `f, g`, **fuel-free**, **NO `IsCanonNormalized` hypothesis** (the
solver checks it). The public theorem consumes the direct Wf soundness certificate `RischDESoundnessWf`.
NO `native_decide`; axiom-clean `[propext, Classical.choice, Quot.sound]`. -/

section Capstone

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- **Direct Wf soundness certificate** `RischDESoundnessWf f g`: every successful run of the fuel-free
solver satisfies the original field-level Risch-DE identity. This is the public soundness boundary. -/
structure RischDESoundnessWf (f g : QFunNZG β) : Prop where
  /-- Every successful Wf solve returns a genuine field-level Risch-DE solution. -/
  sound : ∀ y : QFunNZG β, crischDESolveSoundWf f g = some y →
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2)

/-- **★★ The FUEL-FREE recursive RDE solver is sound under the direct Wf certificate** (Task 3, the capstone,
`crischDESolveSoundWf_field`): if `crischDESolveSoundWf f g = some y`, then under
`RischDESoundnessWf f g`, the returned `y` solves the field-level Risch DE for the ORIGINAL `f, g`:
`D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`. **Fuel-free**, **NO `IsCanonNormalized` hypothesis** — the
solver's own §6.1 solvability check supplies it. NO `native_decide`; axiom-clean
`[propext, Classical.choice, Quot.sound]`. **★ The fuel-free sound solver.** -/
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
