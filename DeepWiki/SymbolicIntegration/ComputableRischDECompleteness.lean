import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound
import DeepWiki.SymbolicIntegration.ComputableRischDESolveSoundWf

/-! # §6 RDE decision-procedure completeness — Wf `solvable ⟹ some`

`ComputableRischDESolveSoundWf` exposes the fuel-free RDE wrapper `crischDESolveSoundWf`. This file isolates
the fuel-free completeness direction: `FieldRDESolvable f g ⟹ ∃ y, crischDESolveSoundWf f g = some y`,
modulo explicit §6 residual clauses.

**The Wf structure of completeness.** `crischDESolveSoundWf f g` produces `none` on exactly four branches:

1. **§6.1 weak-normalizer vanishes** — `cWeakNormalizerGWf … = 0` (`cisZeroG q`);
2. **§6.1 normality check fails** — `cisCanonNormalizedG f̃ = false`;
3. **the lowest-terms reduction fails** — `reduceSoundOpt f̃ = none` (impossible: `reduceSoundOpt_eq`);
4. **the fuel-free inner solve fails** — `crischDERawSolveWf (qReduce f̃) (q'·g) = none`.

Equivalently, the Wf solver succeeds (`crischDESolveSoundWf_some_iff`) iff the Wf weak normalizer is nonzero,
the §6.1 check passes, and the Wf inner solve succeeds. Completeness is then exactly the conjunction of
these Wf stage-completeness facts.

**What is reachable here.**
* **The structural Wf `some`-characterization** `crischDESolveSoundWf_some_iff` — the exact reading of when
  the Wf solver succeeds (the three stage tests passing); pure control flow, no §6 mathematics.
* **The base-field completeness** `rischDE_complete_base` — over the constant base `ℚ` (`D = 0`),
  `crischDESolve` is the direct division `g/b`, so it is **decidably complete**: an RDE `b·y = g`
  has a solution iff `crischDESolve b g = some _` (axiom-clean, no `native_decide`).
* **The Wf residual reduction** — `crischDESolveSoundWf_complete_of_residualWf`: modulo
  `RischDECompletenessResidualWf`, `solvable ⟹ some`; with Wf soundness this gives
  `crischDESolveSoundWf_decides_of_residualWf`.

**The deep §6 residual (precisely isolated, NEVER `sorry`).** The genuine content of completeness — that a
solvable RDE survives every Wf §6 `none`-gate — is bundled in `RischDECompletenessResidualWf`. Its clauses are
the converse directions the soundness layer does not self-certify: Wf weak-normalizer non-vanishing, §6.1
normality completeness, and fuel-free inner-solve completeness. The inner clause is the research-grade core:
it needs the §6.4 degree bound to be a provable upper bound on any solution's degree and the SPDE/poly-RDE
solve to be exhaustive within it. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The field-level RDE solvability predicate `FieldRDESolvable`

`FieldRDESolvable f g` is the existence of a `QFunNZG β` solution to the field-level Risch DE
`D(Y) + F·Y = G`, phrased through the exact expression used by the RDE soundness theorems
(`towerFractionFieldDerivG` + `amG ∘ toPolyG` readings). This is the "solvable" side of the decision
procedure: Wf soundness says `some ⟹ FieldRDESolvable`, Wf completeness says `FieldRDESolvable ⟹ some`. -/

section Solvable

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [CTowerGcdWitness β] [Algebra ℚ (CFieldSpec.K β)]

/-- **Field-level RDE solvability** `FieldRDESolvable f g`: there exists `y : QFunNZG β` solving the
field-level Risch differential equation `D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`, read through
`amG ∘ toPolyG` exactly as the RDE soundness conclusions do. -/
def FieldRDESolvable (f g : QFunNZG β) : Prop :=
  ∃ y : QFunNZG β,
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2)

end Solvable

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

/-! ## ★ The Wf inner clause decomposed: the three §6 inner-stage completeness sub-residuals

The inner clause of `RischDECompletenessResidualWf` — the §6.2–6.6 inner-solve completeness — is itself the
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
`cRischDEG_some_imp_stages`), which lifts to the Wf inner residual clause. Each sub-residual is a stated
`Prop`, NO `sorry`; together they are clause (c)'s exact content, with the §6.4 degree-upper-bound the single
deepest gap. -/

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
gden`: the Wf inner residual clause, decomposed into the precise §6.2/6.4/6.5-6.6 converse
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

/-! ## Fuel-free completeness wrapper

`RischDECompletenessResidualWf` is the native fuel-free residual: its clauses are stated against
`cWeakNormalizerGWf` and `crischDERawSolveWf`, so the completeness direction goes straight through
`crischDESolveSoundWf_some_of_stages`. -/

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

/-- **Fuel-free §6 completeness residual** `RischDECompletenessResidualWf f g`: the three Wf
stage-completeness facts consumed directly by `crischDESolveSoundWf_some_of_stages`. `hwn`: a solvable RDE
has nonzero `cWeakNormalizerGWf`. `hck`: the Wf weak-normalized input passes the §6.1 canon-normality gate.
`hinner`: the fuel-free inner solver `crischDERawSolveWf` succeeds on the reduced pair. This is a
`Prop`-bundle of stated §6 completeness assumptions, NO `sorry`. -/
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
`RischDECompletenessResidualWf` holds, then `crischDESolveSoundWf` returns `some`. This completeness
direction uses the Wf structural skeleton directly and does not rewrite through the fueled solver. -/
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

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The Wf-native residual gives the same decision statement with a fuel-free completeness direction.
example (f g : QFunNZG β) (hres : RischDECompletenessResidualWf f g) (hfit : InputFitsFuel f g)
    (hqwn : cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2
      = cWeakNormalizerG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2)
    (hwf : SoundWfInnerRegular f g) :
    (∃ y, crischDESolveSoundWf f g = some y) ↔ FieldRDESolvable f g :=
  crischDESolveSoundWf_decides_of_residualWf f g hres hfit hqwn hwf

end CompleteWf

/-! ### Final verdict (stated precisely)

**Is the RDE solver a verified decision procedure?** **Modulo a precisely isolated deep §6 residual,
yes.** The fuel-free surface has `crischDESolveSoundWf_decides_of_residualWf`, whose completeness direction
uses the Wf-native residual `RischDECompletenessResidualWf` and the Wf structural skeleton directly. The `⟹`
half (soundness) is the proven soundness theorem; the `⟸` half is completeness modulo the residual.

**Which completeness stages are closed, and which is the deep residual?**
* **Closed unconditionally.** The structural reductions `crischDESolveSoundWf_some_iff` /
  `crischDESolveSoundWf_some_of_stages` (completeness ⟺ the three stage tests passing — pure control flow);
  the lowest-terms reduction gate (never blocks, `reduceSoundOpt_eq`); the **base-field completeness**
  `rischDE_complete_base` (the constant-field oracle over `ℚ` is a genuine decision procedure, `b·y = g`
  solvable ↔ `some`).
* **The deep residual** (`RischDECompletenessResidualWf`, NEVER `sorry`). Three converse facts the engine does
  not self-certify: (a) the §6.1 weak normalizer is nonzero on a solvable input; (b) the §6.1 normality check
  passes on a solvable input (contrapositive: a non-normalizable denominator's RDE is unsolvable); (c) the
  **§6.2–6.6 inner solve succeeds on a solvable input** — the
  research-grade core, needing the §6.4 degree bound to be a provable upper bound on any solution's degree
  and the SPDE/poly-RDE solve to be exhaustive within it, *neither of which is formalized in the engine*
  (the §6 files prove only `some ⟹ cleared-identity`, never a degree-upper-bound or an exhaustiveness lemma).

So full `some ⟺ solvable` is reached **modulo the precise Wf §6 completeness residual** on the fuel-free
surface — the degree-bound + SPDE/poly-RDE exhaustiveness (clause c) being the genuinely deep, unformalized
core; the §6.1 clauses (a, b) the converse of the §6.1 soundness facts. -/

/-! ### Axiom audit (the structural skeleton, base-field completeness, and the modular assembly are
axiom-clean; NO `native_decide`, NO `sorry`) -/

#print axioms crischDESolveSoundWf_some_iff
#print axioms crischDESolveSoundWf_some_of_stages
#print axioms rischDE_complete_base
#print axioms crischDESolveSoundWf_complete_of_residualWf
#print axioms crischDESolveSoundWf_decides_of_residualWf

end DeepWiki.SymbolicIntegration
