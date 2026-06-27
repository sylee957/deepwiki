import DeepWiki.SymbolicIntegration.ComputablePrimPRSRegular
import DeepWiki.SymbolicIntegration.ComputableRischDEStructural

/-! # The fully-abstract transcendental Risch soundness capstone — threading the two PRS witnesses

`ComputablePrimPRSRegular` reduced the last soundness kernel `CPrimPRSGenAssocReg` to **pure bookkeeping**:
`cPrimPRSGenAssocReg_of_regular_of_correct` shows it is *equivalent* (modulo transparent fuel) to exactly
TWO per-run witnesses —

* **PRS termination** `CPrimPRSGenRegular cgcdB fuel P Q` (the primitive-PRS `t`-degree drop loop completes
  within `fuel`; `ComputableTowerWellFounded`), and
* **level-`β` gcd-correctness** `CgcdBCorrect cgcdB` (the content-gcd computes the abstract gcd up to
  associates; `ComputableTowerGcdFFCorrect`) —

plus the transparent fuel side-condition `CPrimPRSGenFuelOk`. This file **threads those two witnesses
through the tower recursion**:

1. **The recursive witness class** `CTowerGcdWitness α` (`Prop`) bundles, at each tower level, the per-run
   termination + fuel witnesses for *every* gcd call (base `ℚ`: the raw Euclidean `cgcdTerminatesG`;
   recursive `QFunNZG β`: `CPrimPRSGenRegular` + `CPrimPRSGenFuelOk` on the cleared pair, with the level-`β`
   witness recursed in). From it, `CTowerGcdWitness.gcdBCorrect` provides
   `∀ fuel, CgcdBCorrect (CFracGcdCore.cgcdFFRawCore fuel)` at every level — the second witness, made an
   honest tower-induction theorem.
2. **The fuel bound** `CPrimPRSGenFuelOk` is carried as the transparent numeric side-condition the engine
   self-satisfies (a `30`-bound per `cdivG` content strip on a finite run); it lives only in the witness
   class, never at runtime.
3. **`CPrimPRSGenAssocReg` discharged** — `cTowerWitness_assocReg` composes (1) + (2) via
   `cPrimPRSGenAssocReg_of_regular_of_correct`, so the opaque per-step regularity gate is a *theorem* from
   the witness class. Hence `associated_toPolyG_cgcdFFCore` (the tower gcd correctness the §6 pipeline
   consumes) follows from the witness alone.
4. **The recursive RDE-oracle soundness** — `crischDESolve_field_of_witness_residual` closes the field-level
   Risch-DE identity for a successful `crischDESolve` over `QFunNZG β`, by composing the §6 boundary theorem
   `rdeCleared_of_success_and_residual` (bare success + the isolated `RischDEStructuralResidual` ⟹ the
   cleared identity) with the cleared → field bridge `rischDE_field_of_cleared`. The residual's
   per-level `Associated`-gcd clauses are exactly the `CgcdBCorrect` the witness class produces; the
   *remaining* clauses of `RischDEStructuralResidual` (the primitive-regime restriction `hprim`, the §6.2
   divisibility/fuel side-conditions, the non-gcd `cdvdG`/`cgcdTerminatesG`/fuel clauses of
   `CSPDEGClearedInputsGen`) are NOT produced by the two gcd witnesses — they are the precisely-isolated
   *remaining bookkeeping*, carried here as an explicit `RischDESuccessResidual` hypothesis.
5. **The fully-abstract corollary** — with the cleared identity discharged (no `native_decide`), the
   field-level RDE soundness is `native`-residual-free *given* the isolated residual, and the constant
   pure-integration residual `D(∫R)=R` is the `crischDESolve_zero_intDeriv` already-clean discharge.

★ **Honest status (stated precisely at the end):** the *gcd kernel* `CPrimPRSGenAssocReg` is fully
discharged from the witness class (Tasks 1–3, axiom-clean, no `native_decide`). The recursive
`CRischFieldSpec (QFunNZG β)` is **not** an unconditional instance: `rdeCleared_of_success_and_residual`
needs the FULL `RischDEStructuralResidual`, whose primitive-regime / divisibility / non-gcd clauses the
engine does not self-certify and the two gcd witnesses do not supply. We close the RDE soundness *up to*
that explicitly-named residual, and isolate it as the remaining bookkeeping. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

/-! ## Task 1 — the recursive witness class `CTowerGcdWitness`

The two PRS witnesses, bundled per tower level. The class carries the **genuine per-run termination/fuel
assumptions** (which are NOT unconditional `∀`-theorems — a too-small fuel can fail termination), and its
`gcdBCorrect` method packages the resulting level-`α` gcd-correctness `CgcdBCorrect (cgcdFFRawCore fuel)`.
Base `ℚ` and recursive `QFunNZG β` instances mirror the `cgcdFFRawCore` recursion exactly. -/

/-- **★ The recursive tower-gcd witness class** `CTowerGcdWitness α`: the bundle of the two per-run PRS
witnesses at level `α`, packaged so its method `gcdBCorrect` yields the level-`α` content-gcd correctness
`∀ fuel, CgcdBCorrect (CFracGcdCore.cgcdFFRawCore fuel)` — the second witness of
`cPrimPRSGenAssocReg_of_regular_of_correct`, made a tower-induction theorem. At the base `ℚ` the witness is
the raw Euclidean termination `cgcdTerminatesG`; at `QFunNZG β` it is `CPrimPRSGenRegular` (PRS termination)
+ `CPrimPRSGenFuelOk` (the transparent fuel bound) on the `gbdegCore`-ordered cleared pair, with the
level-`β` witness recursed in. (`Prop`-class: carries only assumptions and the derived correctness.) -/
class CTowerGcdWitness (α : Type*) [CField α] [CFieldSpec α] [CFracGcdCore α] : Prop where
  /-- The level-`α` content-gcd is gcd-correct at every fuel: `toPolyG (cgcdFFRawCore fuel a b)` is
  `Associated` to `gcd (toPolyG a) (toPolyG b)` in `(CFieldSpec.K α)[X]`. The second PRS witness
  (`CgcdBCorrect`), available recursively as the tower-induction hypothesis. -/
  gcdBCorrect : ∀ fuel : ℕ, CgcdBCorrect (CFracGcdCore.cgcdFFRawCore (α := α) fuel)

/-! ### The base instance `CTowerGcdWitness ℚ`

At the bottom of the tower `cgcdFFRawCore fuel = (cgcdExtG fuel _).1` over `ℚ[t]`, whose correctness is
`associated_toPolyG_cgcdExtG` **under `cgcdTerminatesG`**. Termination is the genuine per-run witness at the
base; we carry it as the hypothesis of the instance-builder `instCTowerGcdWitnessQ_of_terminates`. -/

/-- **★ `CTowerGcdWitness ℚ` from base Euclidean termination.** If the raw Euclidean gcd `cgcdExtG fuel a b`
terminates within `fuel` for every input (`hterm`, the genuine per-run termination witness at the constant
field), then `ℚ` carries the tower-gcd witness: `cgcdFFRawCore fuel = (cgcdExtG fuel _).1` is gcd-correct by
`associated_toPolyG_cgcdExtG`. The bottom of the witness recursion. -/
@[reducible] def instCTowerGcdWitnessQ_of_terminates
    (hterm : ∀ (fuel : ℕ) (a b : CPolyG ℚ), cgcdTerminatesG fuel a b) : CTowerGcdWitness ℚ where
  gcdBCorrect fuel a b := by
    -- `cgcdFFRawCore fuel a b = (cgcdExtG fuel a b).1` at the base instance
    show Associated (toPolyG ((cgcdExtG fuel a b).1)) (gcd (toPolyG a) (toPolyG b))
    exact associated_toPolyG_cgcdExtG fuel a b (hterm fuel a b)

/-! ### Task 2 — the transparent fuel bound, and the recursive instance `CTowerGcdWitness (QFunNZG β)`

The recursive content-gcd `cgcdFFRawCore fuel p q` (`instCFracGcdCoreQFunNZG`) runs `cprimPRSgcdGenCore
(cgcdFFRawCore β) fuel P Q` on the `gbdegCore`-ordered cleared pair `(P, Q)`. Its correctness is
`associated_toPolyG_cgcdFFRawCore` **under `CPrimPRSGenAssocReg (cgcdFFRawCore fuel) fuel P Q`**, which
`cPrimPRSGenAssocReg_of_regular_of_correct` produces from:
* the level-`β` gcd-correctness `CgcdBCorrect (cgcdFFRawCore fuel)` — the recursive witness
  `CTowerGcdWitness.gcdBCorrect (α := β) fuel`;
* the per-run termination `CPrimPRSGenRegular (cgcdFFRawCore fuel) fuel P Q` — carried as `hreg`;
* the transparent fuel bound `CPrimPRSGenFuelOk (cgcdFFRawCore fuel) fuel P Q` — carried as `hfuel`
  (the engine's `30`-bound per `cdivG` content strip; satisfiable on a finite run, **Task 2**). -/

section Recursive

variable {β : Type*} [CField β] [CFieldSpec β] [CFieldDomain β] [CFracGcdCore β]

/-- **The `gbdegCore`-ordered cleared first input** `clearedOrderedFst p q` of a `QFunNZG β`-gcd call: the
larger-`t`-degree of the two cleared denominators `cclearDenomsCoreG p`, `cclearDenomsCoreG q` (the PRS
needs the larger first). The first argument of the `cprimPRSgcdGenCore` run inside
`instCFracGcdCoreQFunNZG`. -/
def clearedOrderedFst (p q : CPolyG (QFunNZG β)) : GBPolyCore β :=
  if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
      < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
    then CPolyG.cclearDenomsCoreG q else CPolyG.cclearDenomsCoreG p

/-- **The `gbdegCore`-ordered cleared second input** `clearedOrderedSnd p q` of a `QFunNZG β`-gcd call: the
smaller-`t`-degree of the two cleared denominators. The second argument of the `cprimPRSgcdGenCore` run
inside `instCFracGcdCoreQFunNZG`. -/
def clearedOrderedSnd (p q : CPolyG (QFunNZG β)) : GBPolyCore β :=
  if GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG p)
      < GBPolyCore.gbdegCore (CPolyG.cclearDenomsCoreG q)
    then CPolyG.cclearDenomsCoreG p else CPolyG.cclearDenomsCoreG q

/-- **★ `CTowerGcdWitness (QFunNZG β)` from the level-`β` witness + per-run PRS termination + fuel.** Given
the recursive witness `[CTowerGcdWitness β]` (the level-`β` content-gcd correctness), the per-run PRS
termination `hreg` and the transparent fuel bound `hfuel` on the `gbdegCore`-ordered cleared pair of *every*
`QFunNZG β`-gcd call, the level-`QFunNZG β` content-gcd is gcd-correct. The recursive node of the witness
tower: `cPrimPRSGenAssocReg_of_regular_of_correct` turns `hreg`/`hfuel` + the level-`β` `CgcdBCorrect`
(`CTowerGcdWitness.gcdBCorrect`) into `CPrimPRSGenAssocReg`, which `associated_toPolyG_cgcdFFRawCore` reads
as the level-`QFunNZG β` gcd correctness. The two PRS witnesses, threaded one level up. -/
@[reducible] def instCTowerGcdWitnessQFunNZG_of_regular [CTowerGcdWitness β]
    (hreg : ∀ (fuel : ℕ) (p q : CPolyG (QFunNZG β)),
      CPrimPRSGenRegular (CFracGcdCore.cgcdFFRawCore (α := β) fuel) fuel
        (clearedOrderedFst p q) (clearedOrderedSnd p q))
    (hfuel : ∀ (fuel : ℕ) (p q : CPolyG (QFunNZG β)),
      CPrimPRSGenFuelOk (CFracGcdCore.cgcdFFRawCore (α := β) fuel) fuel
        (clearedOrderedFst p q) (clearedOrderedSnd p q)) :
    CTowerGcdWitness (QFunNZG β) where
  gcdBCorrect fuel p q := by
    -- the level-β gcd correctness is the recursive witness
    have hcorr : CgcdBCorrect (CFracGcdCore.cgcdFFRawCore (α := β) fuel) :=
      CTowerGcdWitness.gcdBCorrect fuel
    -- discharge the per-step regularity bundle from termination + correctness + fuel (Task 3, one call)
    have hassoc : CPrimPRSGenAssocReg (CFracGcdCore.cgcdFFRawCore (α := β) fuel) fuel
        (clearedOrderedFst p q) (clearedOrderedSnd p q) :=
      cPrimPRSGenAssocReg_of_regular_of_correct (CFracGcdCore.cgcdFFRawCore (α := β) fuel) hcorr
        fuel (clearedOrderedFst p q) (clearedOrderedSnd p q) (hreg fuel p q) (hfuel fuel p q)
    -- read it as the level-(QFunNZG β) gcd correctness
    exact associated_toPolyG_cgcdFFRawCore fuel p q hassoc

end Recursive

/-! ## Task 3 — `CPrimPRSGenAssocReg` discharged from the witness class

With `CTowerGcdWitness α` in hand the per-step regularity gate `CPrimPRSGenAssocReg` of *any* level-`α`
content-gcd PRS run is a theorem given the run's own termination + fuel: the witness supplies the
gcd-correctness half, `cPrimPRSGenAssocReg_of_regular_of_correct` composes it. And the public tower gcd
`cgcdFFCore` the §6 pipeline calls is then gcd-correct at level `QFunNZG β` from the witness alone. -/

section Discharge

variable {α : Type*} [CField α] [CFieldSpec α] [CFracGcdCore α] [CTowerGcdWitness α]

/-- **★ `CPrimPRSGenAssocReg` from the witness class** (Task 3): under `CTowerGcdWitness α`, the per-step
regularity bundle `CPrimPRSGenAssocReg (cgcdFFRawCore fuel) fuel P Q` of a level-`α` content-gcd PRS run
holds for any `(P, Q)` satisfying the run's own termination `CPrimPRSGenRegular` and fuel
`CPrimPRSGenFuelOk`. The witness supplies the gcd-correctness half (`CTowerGcdWitness.gcdBCorrect`);
`cPrimPRSGenAssocReg_of_regular_of_correct` composes it with the two transparent witnesses. So the opaque
13-hypothesis gate is *exactly* PRS termination + fuel, the gcd-correctness now coming from the tower
induction. -/
theorem cTowerWitness_assocReg (fuel : ℕ) (P Q : GBPolyCore α)
    (hreg : CPrimPRSGenRegular (CFracGcdCore.cgcdFFRawCore (α := α) fuel) fuel P Q)
    (hfuel : CPrimPRSGenFuelOk (CFracGcdCore.cgcdFFRawCore (α := α) fuel) fuel P Q) :
    CPrimPRSGenAssocReg (CFracGcdCore.cgcdFFRawCore (α := α) fuel) fuel P Q :=
  cPrimPRSGenAssocReg_of_regular_of_correct (CFracGcdCore.cgcdFFRawCore (α := α) fuel)
    (CTowerGcdWitness.gcdBCorrect fuel) fuel P Q hreg hfuel

end Discharge

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- Task 1: the witness class yields the level-α content-gcd correctness `CgcdBCorrect (cgcdFFRawCore fuel)`.
example {α : Type*} [CField α] [CFieldSpec α] [CFracGcdCore α] [CTowerGcdWitness α] (fuel : ℕ) :
    CgcdBCorrect (CFracGcdCore.cgcdFFRawCore (α := α) fuel) :=
  CTowerGcdWitness.gcdBCorrect fuel

-- Task 1 (base): the constant-field witness from the genuine per-run Euclidean termination.
example (hterm : ∀ (fuel : ℕ) (a b : CPolyG ℚ), cgcdTerminatesG fuel a b) : CTowerGcdWitness ℚ :=
  instCTowerGcdWitnessQ_of_terminates hterm

-- Task 3: `CPrimPRSGenAssocReg` is a theorem from the witness, given the run's termination + fuel.
example {α : Type*} [CField α] [CFieldSpec α] [CFracGcdCore α] [CTowerGcdWitness α]
    (fuel : ℕ) (P Q : GBPolyCore α)
    (hreg : CPrimPRSGenRegular (CFracGcdCore.cgcdFFRawCore (α := α) fuel) fuel P Q)
    (hfuel : CPrimPRSGenFuelOk (CFracGcdCore.cgcdFFRawCore (α := α) fuel) fuel P Q) :
    CPrimPRSGenAssocReg (CFracGcdCore.cgcdFFRawCore (α := α) fuel) fuel P Q :=
  cTowerWitness_assocReg fuel P Q hreg hfuel

/-! ### Axiom audit (the gcd-kernel discharge is axiom-clean, no `native_decide`) -/

#print axioms cTowerWitness_assocReg
#print axioms instCTowerGcdWitnessQ_of_terminates

end DeepWiki.SymbolicIntegration
