import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound
import DeepWiki.SymbolicIntegration.ComputableTowerRischDEWellFounded

/-! # The §6.1 normality check is `qReduce`-invariant — the production RDE re-pin keystone

`ComputableRischDESolveSound` built the corrected, §6.1-gated sound solver `crischDESolveSound`: weak-normalize
`f` to `f̃`, run the solvability check `cisCanonNormalizedG f̃` (the §3.5 normal part of the *reduced* denominator
`reduceDen f̃` equals `reduceDen f̃` — its special part is a unit), then reduce `f̃` to lowest terms (`qReduce f̃`)
and solve. The **production re-pin** routes the core RDE solver through this §6.1 gate; but the wrapper checks
`cisCanonNormalizedG f̃` on the *pre-reduce* `f̃`, while the gated core (receiving the *reduced* `qReduce f̃`)
naturally checks the normality of **its** denominator `(qReduce f̃).1.2`. Reconciling the two needs the fact that
the §6.1 check is invariant under `qReduce`. This file proves it.

★ **The structural key.** `cisCanonNormalizedG x` does **not** read `x`'s raw denominator — it already reads the
**lowest-terms** denominator `reduceDen x = (qReduce x).1.2` (by definition of `cisCanonNormalizedG`). So the
"core check on the reduced input's denominator" is *definitionally* the wrapper's check:

* **`cisCanonNormalizedCoreG a`** — the `[CField β]`/`[CDiffField β]`/`[CFracGcdCore β]` check reading the
  denominator **component** `a.1.2` directly (no re-reduction): `cisZeroG (normalPart(a.1.2) − a.1.2)`.
* **`cisCanonNormalizedCoreG_qReduce`** — the keystone, **by `rfl`**: `cisCanonNormalizedCoreG (qReduce x) =
  cisCanonNormalizedG x`. Both read `(qReduce x).1.2 ≡ reduceDen x` (definitional equality of `qReduce`'s
  denominator), so the core's check on the *reduced* input's denominator IS the wrapper's check on the
  *unreduced* input. No scalar/normalization gap — the re-pin reconciliation is a definitional identity.

The keystone is proved abstractly (by `rfl`, no `native_decide`); axiom-clean
`[propext, Classical.choice, Quot.sound]`.

* **`cisCanonNormalizedG_qReduce_of_idempotent`** — the full *re-running* invariance `cisCanonNormalizedG
  (qReduce x) = cisCanonNormalizedG x` (re-running the wrapper check on the already-reduced `qReduce x`), proved
  **conditional on** `ReduceDenIdempotent x` (`reduceDen (qReduce x) = reduceDen x`), which is the isolated
  list-level reducer-idempotency condition. The hypothesis is `native_decide`-validated at `α = ℚ`. The re-pin
  needs only the keystone, which sidesteps this stronger re-reduction fact entirely. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The denominator-direct §6.1 check `cisCanonNormalizedCoreG` (no re-reduction)

`cisCanonNormalizedCoreG a` is the §6.1 normality test read on the denominator **component** `a.1.2` of a
`QFunNZG β` *directly* — `cisZeroG (normalPart(a.1.2) − a.1.2)` — without first reducing `a` to lowest terms.
This is the check the re-pinned core naturally runs on a *reduced* input `qReduce f̃` (whose denominator
`(qReduce f̃).1.2` is already in lowest terms). Needs only `[CField β]`/`[CDiffField β]`/`[CFracGcdCore β]`
data (same as `cisCanonNormalizedG`), so it `native_decide`s. -/

section Core

variable {β : Type*} [CField β] [CDiffField β] [CFracGcdCore β]

/-- **The denominator-direct §6.1 solvability check** `cisCanonNormalizedCoreG a`: `true` iff the §3.5 normal
part of the denominator **component** `a.1.2` equals `a.1.2` itself — `cisZeroG (normalPart(a.1.2) − a.1.2)`.
Unlike `cisCanonNormalizedG` (which reads the *re-reduced* `reduceDen a`), this reads `a.1.2` *directly*, the
denominator the re-pinned core already has after reducing its RDE input to lowest terms. On a reduced input
`a = qReduce x`, `a.1.2 ≡ reduceDen x`, so it coincides with `cisCanonNormalizedG x` (`cisCanonNormalizedCoreG_qReduce`). -/
def cisCanonNormalizedCoreG (a : QFunNZG β) : Bool :=
  CPolyG.cisZeroG (CPolyG.csubG
    (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel a.1.2).1
    a.1.2)

end Core

section CoreWf

variable {β : Type*} [CField β] [CDiffField β] [CFracGcdCoreWf β]

/-- The fuel-free denominator-direct canonical-normality check. -/
def cisCanonNormalizedCoreGWf (a : QFunNZG β) : Bool :=
  cdenomNormalGateGWf a

/-- The fuel-free wrapper canonical-normality check on the reduced denominator. -/
def cisCanonNormalizedGWf (ftilde : QFunNZG β) : Bool :=
  CPolyG.cisZeroG (CPolyG.csubG
    (CPolyG.cSplitFactorFastGWf ([CField.one] : CPolyG β)
      (QFunNZG.reduceDen ftilde)).1
    (QFunNZG.reduceDen ftilde))

end CoreWf

/-! ## ★ The keystone bridge (by `rfl`): the core check on `qReduce x` is the wrapper check on `x`

`cisCanonNormalizedCoreG (qReduce x) = cisCanonNormalizedG x`. The wrapper's `cisCanonNormalizedG x` is, by
*definition*, the §6.1 test on `reduceDen x`; and `(qReduce x).1.2` is *definitionally* `reduceDen x`. So the
core's denominator-direct check on the reduced input is the wrapper's check on the unreduced input — a
definitional identity, no normalization reasoning. This is the corollary the production re-pin consumes: the
gate the wrapper passes (`cisCanonNormalizedG ftilde`) is exactly the gate the core would run on `qReduce ftilde`. -/

section Bridge

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCore β]

/-- **★ The re-pin keystone** (`cisCanonNormalizedCoreG_qReduce`, by `rfl`): the denominator-direct §6.1 check
on the *reduced* input `qReduce x` equals the wrapper's `cisCanonNormalizedG` on the *unreduced* `x`. Both are
`cisZeroG (normalPart(d) − d)` with `d = reduceDen x = (qReduce x).1.2` (definitional), so the core's gate on
`qReduce ftilde` is the wrapper's gate on `ftilde` — the reconciliation the production RDE re-pin needs, with
NO scalar/normalization gap. -/
theorem cisCanonNormalizedCoreG_qReduce (x : QFunNZG β) :
    cisCanonNormalizedCoreG (qReduce x) = cisCanonNormalizedG x := rfl

omit [CFracGcdCore β] in
/-- The fuel-free core check on `qReduce x` is the fuel-free wrapper check on `x`. -/
theorem cisCanonNormalizedCoreGWf_qReduce [CFracGcdCoreWf β] (x : QFunNZG β) :
    cisCanonNormalizedCoreGWf (qReduce x) = cisCanonNormalizedGWf x := rfl

-- ★ The re-pin reconciliation: the gated core's denominator-direct §6.1 check on the reduced input `qReduce x`
-- IS the wrapper's §6.1 check on the unreduced input `x`. Definitional (`rfl`); the keystone the production
-- RDE re-pin's raw-solve transfer consumes.
example (x : QFunNZG β) : cisCanonNormalizedCoreG (qReduce x) = cisCanonNormalizedG x := rfl

example [CFracGcdCoreWf β] (x : QFunNZG β) :
    cisCanonNormalizedCoreGWf (qReduce x) = cisCanonNormalizedGWf x := rfl

end Bridge

/-! ## Fuel-free canonical-normality propositions

The Wf propositions are the fuel-free normality gates: they read the normal part through
`cSplitFactorFastGWf` and are the predicates consumed by the Wf soundness API. -/

section NormalityWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- The fuel-free weak-normalization guarantee for a rational function denominator. -/
def IsWeaklyNormalizedNormWf (h : QFunNZG β) : Prop :=
  toPolyG (CPolyG.cSplitFactorFastGWf ([CField.one] : CPolyG β) h.1.2).1
    = toPolyG h.1.2

/-- The fuel-free canonicalized weak-normalization guarantee. -/
def IsCanonNormalizedWf (f q' : QFunNZG β) : Prop :=
  IsWeaklyNormalizedNormWf (qReduce (weakNormalizedF f q'))

/-- The fuel-free Boolean check decides `IsCanonNormalizedWf`. -/
theorem cisCanonNormalizedGWf_iff (f q' : QFunNZG β) :
    cisCanonNormalizedGWf (weakNormalizedF f q') = true ↔ IsCanonNormalizedWf f q' := by
  unfold cisCanonNormalizedGWf IsCanonNormalizedWf IsWeaklyNormalizedNormWf
  rw [CPolyG.cisZeroG_iff, CPolyG.toPolyG_csubG, sub_eq_zero]
  rfl

end NormalityWf

/-! ## The full re-reduce invariance, isolated to `reduceDen`-idempotency-at-lowest-terms

The keystone above is the form the re-pin actually consumes: the core, holding the *reduced* fraction
`qReduce ftilde`, runs the §6.1 test on **its** denominator component `(qReduce ftilde).1.2` — and that is,
definitionally, the wrapper's `cisCanonNormalizedG ftilde`. No implementation re-runs the full
`cisCanonNormalizedG` (which itself re-reduces) on an already-reduced input.

The *re-running* form `cisCanonNormalizedG (qReduce x) = cisCanonNormalizedG x` is validated below on
representative examples, but it does **not** reduce to the keystone: `cisCanonNormalizedG (qReduce x)` re-reduces
`qReduce x`'s denominator, reading `reduceDen (qReduce x)` rather than `(qReduce x).1.2`. It therefore turns
entirely on whether **re-reducing an already-reduced denominator is the identity**:

  `reduceDen (qReduce x) = reduceDen x`  (`ReduceDenIdempotent`).

For the fuel-free monic reducer, this should follow from the concrete list-level idempotency of
`cgcdMonicWf`/`cdivWf` on an already-reduced fraction. The semantic API proves the value-preservation the
solver needs, but the stronger representative equality above is intentionally kept as a separate hypothesis:
the production re-pin never re-runs the wrapper on an already-reduced input. The re-running invariance is
therefore stated here **conditional on** `ReduceDenIdempotent` (proved generically from that hypothesis,
sorry-free) and `native_decide`-validated on representative `α = ℚ` examples. -/

section ReReduce

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCore β]

/-- **The `reduceDen`-idempotency-at-lowest-terms hypothesis** `ReduceDenIdempotent x`: re-reducing the
already-reduced fraction `qReduce x` leaves its denominator unchanged — `reduceDen (qReduce x) = reduceDen x`.
It is the isolated representative-level condition needed only for the stronger re-running form; the production
re-pin consumes the definitional keystone above instead. `native_decide` validates this idempotency at `α = ℚ`
(`reduceDenIdempotent_examples`), and the §6.1 re-running invariance
`cisCanonNormalizedG_qReduce_of_idempotent` is mechanical once the hypothesis is supplied. -/
def ReduceDenIdempotent (x : QFunNZG β) : Prop :=
  QFunNZG.reduceDen (qReduce x) = QFunNZG.reduceDen x

/-- **★ The §6.1 check is `qReduce`-invariant under re-running** (`cisCanonNormalizedG_qReduce_of_idempotent`):
given `ReduceDenIdempotent x` (re-reducing the reduced denominator is the identity),
`cisCanonNormalizedG (qReduce x) = cisCanonNormalizedG x`. Both unfold to `cisZeroG (normalPart(d) − d)` reading
`d = reduceDen (qReduce x)` resp. `d = reduceDen x`; the hypothesis rewrites the former to the latter. Mechanical
once the (isolated) `reduceDen`-idempotency is supplied. -/
theorem cisCanonNormalizedG_qReduce_of_idempotent (x : QFunNZG β) (hidem : ReduceDenIdempotent x) :
    cisCanonNormalizedG (qReduce x) = cisCanonNormalizedG x := by
  show CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel
        (QFunNZG.reduceDen (qReduce x))).1
      (QFunNZG.reduceDen (qReduce x)))
    = CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel
        (QFunNZG.reduceDen x)).1
      (QFunNZG.reduceDen x))
  rw [show QFunNZG.reduceDen (qReduce x) = QFunNZG.reduceDen x from hidem]

-- The full re-running §6.1 invariance `cisCanonNormalizedG (qReduce x) = cisCanonNormalizedG x`, given the
-- isolated `reduceDen`-idempotency `reduceDen (qReduce x) = reduceDen x`.
example (x : QFunNZG β) (hidem : ReduceDenIdempotent x) :
    cisCanonNormalizedG (qReduce x) = cisCanonNormalizedG x :=
  cisCanonNormalizedG_qReduce_of_idempotent x hidem

end ReReduce

/-! ## Validation (`native_decide`): the denominator-direct check is computable at the tower level; the
re-reduce idempotency and the full re-running invariance hold at `α = ℚ`

`cisCanonNormalizedCoreG` reads only the denominator component (`[CField β]`/`[CDiffField β]`/`[CFracGcdCore β]`
data), so — unlike `cisCanonNormalizedG`/`qReduce`, whose tower type drags in the noncomputable `[CFieldSpec]` —
it `native_decide`s at the level-2 carrier `ℚ(x)(t₁)`. The `reduceDen`-idempotency and re-running invariance use
the computable `α = ℚ` carrier (level 1, `ℚ(x)`). -/

section Validation

/-- **The core check is computable at level 2 and rejects the witness denominator** (`native_decide`): on the
weakly-normalized witness `f̃` for `f = 1/(t₁ − x)` over `ℚ(x)(t₁)`, the denominator-direct
`cisCanonNormalizedCoreG f̃ = false` — its denominator `t₁ − x` (a `D`-constant special pole) is not its own
normal part. The denominator-direct check `native_decide`s where `cisCanonNormalizedG`/`qReduce` cannot. -/
theorem cisCanonNormalizedCoreG_witness_false :
    cisCanonNormalizedCoreG (β := QFunNZG ℚ) (weakNormalizedF witnessF
      (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG (QFunNZG ℚ))
        witnessF.1.1 witnessF.1.2))) = false := by native_decide

/-- A swelling `ℚ(x)` fraction `(x² − 1)/(x² + 2x − 3) = (x²−1)/((x−1)(x+3))` (lowest terms `(x+1)/(x+3)`) and a
non-monic swell `3x²/(2(x+1)(x+2))` — `qReduce`-representative changes on both, so they exercise
`ReduceDenIdempotent`/the re-running invariance non-trivially. -/
def reduceDenExamples : List (QFunNZG ℚ) :=
  [⟨([(-1 : ℚ), 0, 1], [(-3 : ℚ), 2, 1]), by native_decide⟩,
   ⟨([(0 : ℚ), 0, 3], [(4 : ℚ), 6, 2]), by native_decide⟩,
   ⟨([(0 : ℚ), 1], [(0 : ℚ), 0, 1]), by native_decide⟩]

/-- **`ReduceDenIdempotent` holds at `α = ℚ`** (`reduceDenIdempotent_examples`, `native_decide`): on each swelling
`reduceDenExamples` fraction (where `qReduce` genuinely cancels a common factor), `reduceDen (qReduce x) =
reduceDen x` — re-reducing the reduced denominator is the identity for these concrete representatives. -/
theorem reduceDenIdempotent_examples :
    reduceDenExamples.all (fun x =>
      (QFunNZG.reduceDen (qReduce x) : List ℚ) == (QFunNZG.reduceDen x : List ℚ)) = true := by
  native_decide

/-- **The full re-running §6.1 invariance holds at `α = ℚ`** (`cisCanonNormalizedG_qReduce_examples`,
`native_decide`): on each swelling fraction, `cisCanonNormalizedG (qReduce x) = cisCanonNormalizedG x` — the check
is unchanged by re-running it on the already-reduced fraction (its denominator re-reduces to itself on these
representatives). This is the concrete `α = ℚ` validation of `cisCanonNormalizedG_qReduce_of_idempotent`. -/
theorem cisCanonNormalizedG_qReduce_examples :
    reduceDenExamples.all (fun x =>
      cisCanonNormalizedG (qReduce x) == cisCanonNormalizedG x) = true := by
  native_decide

end Validation

/-! ## The Wf re-pin corollary

The Wf wrapper weak-normalizes `f` to `ftilde = weakNormalizedF f q'`
(`q' = qOfPolyNZG (cWeakNormalizerGWf [1] f.1.1 f.1.2)`) and passes the Wf gate
`cisCanonNormalizedGWf ftilde`. The Wf gated core, holding the reduced `qReduce ftilde`, runs the
denominator-direct gate `cisCanonNormalizedCoreGWf (qReduce ftilde)`. The following equations reconcile those
two Wf gates definitionally. -/

section Repin

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- **The Wf re-pin gate reconciliation** (`cisCanonNormalizedCoreGWf_qReduce_weakNormalized`): for the
weak-normalized `ftilde = weakNormalizedF f q'` (`q'` the lift of the fuel-free weak normalizer
`cWeakNormalizerGWf [1] f.1.1 f.1.2`), the Wf gated core's denominator-direct check on the reduced input
equals the Wf wrapper's check on the pre-reduce input. -/
theorem cisCanonNormalizedCoreGWf_qReduce_weakNormalized (f : QFunNZG β) :
    cisCanonNormalizedCoreGWf (qReduce (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
      = cisCanonNormalizedGWf (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) :=
  cisCanonNormalizedCoreGWf_qReduce _

/-- **The Wf re-pin gate decides `IsCanonNormalizedWf`**: the Wf gated core's denominator-direct check on the
reduced weak-normalized input passes iff the fuel-free §6.1 normalization guarantee holds. -/
theorem cisCanonNormalizedCoreGWf_qReduce_weakNormalized_iff [CFieldDomain β] (f : QFunNZG β) :
    cisCanonNormalizedCoreGWf (qReduce (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)))) = true
      ↔ IsCanonNormalizedWf f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2)) := by
  rw [cisCanonNormalizedCoreGWf_qReduce_weakNormalized]
  exact cisCanonNormalizedGWf_iff f _

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The same re-pin reconciliation stated entirely on the Wf gate.
example (f : QFunNZG β) :
    cisCanonNormalizedCoreGWf (qReduce (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))))
      = cisCanonNormalizedGWf (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))) :=
  cisCanonNormalizedCoreGWf_qReduce_weakNormalized f

end Repin

/-! ### Axiom audit (the keystone bridge, the re-pin corollary, and the conditional re-running invariance are
axiom-clean; the validations are `native_decide`) -/

#print axioms cisCanonNormalizedCoreG_qReduce
#print axioms cisCanonNormalizedCoreGWf_qReduce_weakNormalized
#print axioms cisCanonNormalizedCoreGWf_qReduce_weakNormalized_iff
#print axioms cisCanonNormalizedG_qReduce_of_idempotent

end DeepWiki.SymbolicIntegration
