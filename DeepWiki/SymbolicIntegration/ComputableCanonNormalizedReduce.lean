import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound

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
`[propext, Classical.choice, Quot.sound]`. The full *re-reduce* invariance `cisCanonNormalizedG (qReduce x) =
cisCanonNormalizedG x` (re-running `cisCanonNormalizedG` on the already-reduced `qReduce x`, which re-reduces its
denominator) is added next, via `reduceDen`-idempotency-at-lowest-terms. -/

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

end Bridge

/-! ## Validation (`native_decide`): the denominator-direct check is computable at the tower level

`cisCanonNormalizedCoreG` reads only the denominator component (`[CField β]`/`[CDiffField β]`/`[CFracGcdCore β]`
data), so — unlike `cisCanonNormalizedG`/`qReduce`, whose tower type drags in the noncomputable `[CFieldSpec]` —
it `native_decide`s at the level-2 carrier `ℚ(x)(t₁)`. -/

section Validation

/-- **The core check is computable at level 2 and rejects the witness denominator** (`native_decide`): on the
weakly-normalized witness `f̃` for `f = 1/(t₁ − x)` over `ℚ(x)(t₁)`, the denominator-direct
`cisCanonNormalizedCoreG f̃ = false` — its denominator `t₁ − x` (a `D`-constant special pole) is not its own
normal part. The denominator-direct check `native_decide`s where `cisCanonNormalizedG`/`qReduce` cannot. -/
theorem cisCanonNormalizedCoreG_witness_false :
    cisCanonNormalizedCoreG (β := QFunNZG ℚ) (weakNormalizedF witnessF
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPolyG (QFunNZG ℚ)) towerRischDEFuel
        witnessF.1.1 witnessF.1.2))) = false := by native_decide

end Validation

/-! ### Axiom audit (the keystone bridge is axiom-clean, by `rfl`; the validation is `native_decide`) -/

#print axioms cisCanonNormalizedCoreG_qReduce

end DeepWiki.SymbolicIntegration
