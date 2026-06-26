import DeepWiki.SymbolicIntegration.ComputableUnifiedMixedIntegrate
import DeepWiki.SymbolicIntegration.ComputableIntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness

/-! # The COMPOSED soundness capstone for the unified mixed integrator `cIntegrateMixed`

`ComputableUnifiedMixedIntegrate` builds the ONE dispatcher `cIntegrateMixed` over BOTH engines (the
transcendental `cIntegrateGFull` and the algebraic `cIntegrateAlgebraic`) and its single validator
`checkMixed`, validating concrete integrals through it by `native_decide` (`umTransc_validated`,
`umAlg_validated`). This file replaces "sound by parts + `native_decide` examples" with ONE **abstract,
axiom-clean** theorem: the validator `checkMixed` **certifies** the antiderivative identity `D(∫f) = f`,
per branch, with NO `native_decide` — the same check-based soundness as `cIntegrateGChecked_correct`
(`ComputableIntegrateTowerCorrectG`), here lifted across the unified dispatcher.

The two per-branch certificates already exist abstractly; this file *composes* them under one case-split:

* **transcendental branch** — `checkMixed`'s transcendental arm IS `CPolyG.checkIdentityG Dt r anum aden`,
  and `field_identity_of_checkIdentityG` (`ComputableIntegrateTowerCorrectG`) already proves
  `checkIdentityG = true → ` the field identity `D(g) + Σ cᵢ·(Δvᵢ)/vᵢ = anum/aden` over the tower fraction
  field `RatFunc (CFieldSpec.K α)`. This branch closes by `exact`.
* **algebraic branch** — `checkMixed`'s algebraic arm IS `radIsZero (radSub (algDeriv algRho res)
  algIntegrand)`, and `toPolyG_algDeriv_eq_of_roundtrip` (`ComputableRadicalLogSoundness`) already proves
  this `= true → toPolyG (algDeriv algRho res) = toPolyG algIntegrand` in `(RatFunc ℚ)[X]` — the
  un-cross-multiplied `D(v + Σ cᵢ log uᵢ) = f` over the curve `y² = algRho`. This branch closes by `exact`.

What this file delivers (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`):

* **`MixedResultDifferentiatesTo`** — the per-branch antiderivative identity predicate: on a
  `transcendental res`, the field identity over `RatFunc (CFieldSpec.K α)`; on an `algebraic res`, the
  `K[X]`-level `toPolyG (algDeriv algRho res) = toPolyG algIntegrand`. The exact shapes
  `umTransc_validated`/`umAlg_validated` validate on examples, stated abstractly.
* **`checkMixed_sound`** — `checkMixed … = true → MixedResultDifferentiatesTo …`, by `cases` on the result,
  reusing the two existing per-branch bridges. The honest, clean (check-based) soundness of the unified
  dispatcher.
* **★ `cIntegrateMixedChecked` / `cIntegrateMixedChecked_sound`** — the self-validating mixed integrator
  (`cIntegrateMixed` guarded by `checkMixed`) and its UNCONDITIONAL soundness: a `some` result is a genuine
  antiderivative. The mixed analogue of `cIntegrateGChecked` / `cIntegrateGChecked_correct`.

**Both branches are abstract theorems** — the mixed integrator is now sound as ONE axiom-clean statement
(modulo the structural nonzero-denominator side conditions the transcendental branch's field identity
needs, exactly as `cIntegrateGChecked_correct` carries them).

**Follow-up** (documented, not built): the `cIntegrateMixedWf` (well-founded, fuel-free) transfer — the
`…Wf = …fuel` correspondence (`ComputableUnifiedFuelFree`) carries this soundness to the fuel-free
dispatcher with no change to the per-branch bridges, since the validator `checkMixed` is identical. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG RadElem

/-! ### The per-branch antiderivative-identity predicate `MixedResultDifferentiatesTo`

A `MixedIntegralResult` is one of two shapes; "it differentiates to the integrand" means different,
faithful things per shape — exactly the conclusions the two existing per-branch bridges produce. The
transcendental case is the field identity over the tower fraction field (the conclusion of
`field_identity_of_checkIdentityG`); the algebraic case is the `K[X]`-level derivative equality (the
conclusion of `toPolyG_algDeriv_eq_of_roundtrip`). We package them as one predicate so the soundness
theorem reads `checkMixed = true → MixedResultDifferentiatesTo`. -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCore α]

/-- **The per-branch antiderivative identity** `MixedResultDifferentiatesTo Dt result anum aden algRho
algIntegrand` — the faithful "`result` differentiates to the integrand", dispatched on the result shape to
match the two engines' soundness conclusions.

* On a **transcendental** `res = some r`: the **field identity** over the tower fraction field
  `RatFunc (CFieldSpec.K α)`, `towerFractionFieldDerivG Dt (amG g.1 / amG g.2) + logResidueSumG Dt r.logs
  = amG anum / amG aden` — `D(g) + Σ cᵢ·(Δvᵢ)/vᵢ = anum/aden`, the conclusion of
  `field_identity_of_checkIdentityG`. A transcendental `none` is vacuously *not* a valid result, so the
  predicate is `False` there (it can never be reached under `checkMixed = true`).
* On an **algebraic** `res`: the `K[X]`-level identity `toPolyG (algDeriv algRho res) = toPolyG
  algIntegrand` over `(RatFunc ℚ)[X]` — the un-cross-multiplied `D(v + Σ cᵢ log uᵢ) = f` on the curve
  `y² = algRho`, the conclusion of `toPolyG_algDeriv_eq_of_roundtrip`. -/
def MixedResultDifferentiatesTo (Dt : CPolyG α) (result : MixedIntegralResult α)
    (anum aden : CPolyG α) (algRho : QFunNZG ℚ) (algIntegrand : RadElem (QFunNZG ℚ)) : Prop :=
  match result with
  | .transcendental res =>
      match res with
      | some r =>
          towerFractionFieldDerivG Dt
              (amG α (toPolyG r.rational.1) / amG α (toPolyG r.rational.2))
            + logResidueSumG Dt r.logs
          = amG α (toPolyG anum) / amG α (toPolyG aden)
      | none => False
  | .algebraic res =>
      CPolyG.toPolyG (algDeriv algRho res) = CPolyG.toPolyG algIntegrand

/-! ### `checkMixed_sound` — the validator certifies the identity, abstractly

`cases` on the result. The transcendental case unfolds `checkMixed` to `checkIdentityG Dt r anum aden` and
feeds `field_identity_of_checkIdentityG`. The algebraic case unfolds to `radIsZero (radSub (algDeriv …) …)`
and feeds `toPolyG_algDeriv_eq_of_roundtrip`. Neither bridge uses `native_decide`. -/

/-- **★ `checkMixed` certifies the antiderivative identity, abstractly** — `checkMixed Dt result anum aden
algRho algIntegrand = true → MixedResultDifferentiatesTo Dt result anum aden algRho algIntegrand`, the
COMPOSED soundness of the unified dispatcher. By `cases` on `result`:

* **transcendental** `some r`: `checkMixed` is `CPolyG.checkIdentityG Dt r anum aden`, so `= true` feeds
  `field_identity_of_checkIdentityG` (the engine ⟹ field bridge) — needs the structural nonzero-denominator
  facts `hgden` (`r.rational.2`), `haden` (`aden`), `hlogs` (each log argument), exactly as
  `cIntegrateGChecked_correct` does. A transcendental `none` makes `checkMixed = false`, contradicting the
  hypothesis.
* **algebraic** `res`: `checkMixed` is `radIsZero (radSub (algDeriv algRho res) algIntegrand)`, so `= true`
  feeds `toPolyG_algDeriv_eq_of_roundtrip` (the round-trip ⟹ `K[X]`-identity bridge) — no side conditions.

The mixed integrator's `D(∫f) = f` as one abstract theorem, reusing the two per-branch bridges verbatim;
no `native_decide`. The transcendental nonzero-denominator hypotheses are dispatched only on the
transcendental result (`hgden`/`haden`/`hlogs`); the algebraic branch ignores them. -/
theorem checkMixed_sound (Dt : CPolyG α) (result : MixedIntegralResult α)
    (anum aden : CPolyG α) (algRho : QFunNZG ℚ) (algIntegrand : RadElem (QFunNZG ℚ))
    (hgden : ∀ r, result = .transcendental (some r) → toPolyG r.rational.2 ≠ 0)
    (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ r, result = .transcendental (some r) → ∀ cv ∈ r.logs, toPolyG cv.2 ≠ 0)
    (h : checkMixed Dt result anum aden algRho algIntegrand = true) :
    MixedResultDifferentiatesTo Dt result anum aden algRho algIntegrand := by
  cases result with
  | transcendental res =>
    cases res with
    | some r =>
      -- transcendental: `checkMixed (.transcendental (some r)) …` IS (iota, definitionally)
      -- `CPolyG.checkIdentityG Dt r anum aden`, so `h` is accepted where the field bridge wants
      -- `checkIdentityG … = true`; and the goal reduces (iota) to that bridge's field-identity
      -- conclusion. Both crossings are by `exact`'s defeq check — no `checkMixed` unfold needed.
      exact field_identity_of_checkIdentityG Dt r anum aden
        (hgden r rfl) haden (hlogs r rfl) h
    | none =>
      -- `checkMixed (.transcendental none) … = false`, contradicting `h : … = true`
      simp [checkMixed] at h
  | algebraic res =>
    -- algebraic: `checkMixed (.algebraic res) …` IS (iota, definitionally) `radIsZero (radSub
    -- (algDeriv algRho res) algIntegrand)`, the round-trip bridge's hypothesis; the goal reduces
    -- to its `K[X]`-identity conclusion. Both crossings are by `exact`'s defeq check.
    exact toPolyG_algDeriv_eq_of_roundtrip algRho res algIntegrand h

/-! ### ★ The self-validating unified integrator — UNCONDITIONAL soundness

Guard `cIntegrateMixed`'s output by `checkMixed`: return `some` only when the validator passes. Then a
`some` result is a genuine antiderivative — `checkMixed_sound` supplies the identity. The mixed analogue of
`cIntegrateGChecked` / `cIntegrateGChecked_correct`. -/

/-- **★ The self-validating unified mixed integrator** `cIntegrateMixedChecked Dt fuel spec anum aden
algRho algIntegrand`: run the unified dispatcher `cIntegrateMixed fuel spec`, then **guard** the result by
`checkMixed` against the integrand (transcendental `anum/aden`, algebraic `algRho`/`algIntegrand`). Returns
`some result` only when `checkMixed … = true` (`result` is a genuine antiderivative), `none` otherwise — so
it never returns a wrong answer. A thin wrapper that does NOT modify `cIntegrateMixed`; the mixed analogue
of `cIntegrateGChecked`. -/
def cIntegrateMixedChecked [CRischField α] (Dt : CPolyG α) (fuel : ℕ) (spec : IntegrandSpec α)
    (anum aden : CPolyG α) (algRho : QFunNZG ℚ) (algIntegrand : RadElem (QFunNZG ℚ)) :
    Option (MixedIntegralResult α) :=
  let result := cIntegrateMixed fuel spec
  if checkMixed Dt result anum aden algRho algIntegrand then some result else none

/-- **★ `cIntegrateMixedChecked = some result → D(result) = integrand`** — the self-validating mixed
integrator's UNCONDITIONAL soundness, for ALL inputs and BOTH branches. If `cIntegrateMixedChecked Dt fuel
spec anum aden algRho algIntegrand = some result`, then `MixedResultDifferentiatesTo Dt result anum aden
algRho algIntegrand`: the per-branch antiderivative identity (the transcendental field identity over
`RatFunc (CFieldSpec.K α)`, or the algebraic `toPolyG (algDeriv …) = toPolyG integrand` over `(RatFunc ℚ)[X]`).
The `if checkMixed …` guard forces `checkMixed = true`, which `checkMixed_sound` turns into the identity —
gated only on the structural nonzero-denominator facts the transcendental field identity needs (dispatched
on the transcendental result; the algebraic branch carries none). No regime / residue-set hypothesis; the
validator alone supplies correctness. The mixed analogue of `cIntegrateGChecked_correct`, immediate from the
wrapper definition (`some` forces `checkMixed = true`) and `checkMixed_sound`; NO `native_decide`. -/
theorem cIntegrateMixedChecked_sound [CRischField α] (Dt : CPolyG α) (fuel : ℕ)
    (spec : IntegrandSpec α) (anum aden : CPolyG α) (algRho : QFunNZG ℚ)
    (algIntegrand : RadElem (QFunNZG ℚ)) (result : MixedIntegralResult α)
    (hsome : cIntegrateMixedChecked Dt fuel spec anum aden algRho algIntegrand = some result)
    (hgden : ∀ r, result = .transcendental (some r) → toPolyG r.rational.2 ≠ 0)
    (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ r, result = .transcendental (some r) → ∀ cv ∈ r.logs, toPolyG cv.2 ≠ 0) :
    MixedResultDifferentiatesTo Dt result anum aden algRho algIntegrand := by
  -- the guard returned `some result`, so `checkMixed` fired `true` and `result = cIntegrateMixed fuel spec`
  rw [cIntegrateMixedChecked] at hsome
  by_cases hc : checkMixed Dt (cIntegrateMixed fuel spec) anum aden algRho algIntegrand = true
  · -- guard passed: the `if` takes the `some` branch, so `result = cIntegrateMixed fuel spec`
    rw [if_pos hc, Option.some.injEq] at hsome
    subst hsome
    exact checkMixed_sound Dt (cIntegrateMixed fuel spec) anum aden algRho algIntegrand
      hgden haden hlogs hc
  · -- guard failed: the `if` takes the `none` branch, contradicting `hsome : … = some result`
    rw [if_neg hc] at hsome
    exact absurd hsome (by simp)

/-! ### Restatements against the intended wording (anonymous `example`s)

The `checkMixed`-certified mixed integrator never returns a wrong answer — `cIntegrateMixedChecked = some
result` ⟹ `result` differentiates to the integrand, per branch. The exact shapes `umTransc_validated` /
`umAlg_validated` validate on examples by `native_decide`, here as one abstract `cases`-on-result theorem. -/

-- ★ THE CAPSTONE (UNCONDITIONAL, checked form): the self-validating unified mixed integrator is sound for
-- BOTH the transcendental and the algebraic branch as ONE abstract theorem — no `native_decide`.
example [CRischField α] (Dt : CPolyG α) (fuel : ℕ) (spec : IntegrandSpec α)
    (anum aden : CPolyG α) (algRho : QFunNZG ℚ) (algIntegrand : RadElem (QFunNZG ℚ))
    (result : MixedIntegralResult α)
    (hsome : cIntegrateMixedChecked Dt fuel spec anum aden algRho algIntegrand = some result)
    (hgden : ∀ r, result = .transcendental (some r) → toPolyG r.rational.2 ≠ 0)
    (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ r, result = .transcendental (some r) → ∀ cv ∈ r.logs, toPolyG cv.2 ≠ 0) :
    MixedResultDifferentiatesTo Dt result anum aden algRho algIntegrand :=
  cIntegrateMixedChecked_sound Dt fuel spec anum aden algRho algIntegrand result hsome hgden haden hlogs

-- The validator certifies the identity directly (the check-soundness core), for either branch.
example (Dt : CPolyG α) (result : MixedIntegralResult α) (anum aden : CPolyG α)
    (algRho : QFunNZG ℚ) (algIntegrand : RadElem (QFunNZG ℚ))
    (hgden : ∀ r, result = .transcendental (some r) → toPolyG r.rational.2 ≠ 0)
    (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ r, result = .transcendental (some r) → ∀ cv ∈ r.logs, toPolyG cv.2 ≠ 0)
    (h : checkMixed Dt result anum aden algRho algIntegrand = true) :
    MixedResultDifferentiatesTo Dt result anum aden algRho algIntegrand :=
  checkMixed_sound Dt result anum aden algRho algIntegrand hgden haden hlogs h

/-! ### Axiom audit — the composed soundness rests only on the standard kernel axioms

Both `checkMixed_sound` and `cIntegrateMixedChecked_sound` carry **only** the standard `[propext,
Classical.choice, Quot.sound]` — no `native_decide` compiler axiom (`ofReduceBool`/`native`), no `sorry`.
The unified mixed integrator is sound for BOTH branches as ONE abstract theorem, certified by its own
validator `checkMixed`, reusing the transcendental `field_identity_of_checkIdentityG` and the algebraic
`toPolyG_algDeriv_eq_of_roundtrip`. -/

-- ★ The validator certifies the antiderivative identity, abstractly (both branches):
#print axioms checkMixed_sound
-- ★★ THE CAPSTONE: the self-validating mixed integrator is unconditionally sound (both branches):
#print axioms cIntegrateMixedChecked_sound

end DeepWiki.SymbolicIntegration
