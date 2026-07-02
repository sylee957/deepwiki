import DeepWiki.SymbolicIntegration.Computable.PrimPRSRegular
import DeepWiki.SymbolicIntegration.Computable.RischDE.Structural
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.FullSoundness

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
   self-satisfies (a `30`-bound per `cdivWf` content strip on a finite run); it lives only in the witness
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
   divisibility side-conditions, the non-gcd `cdvdG`/`cgcdTerminatesG`/fuel clauses of
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
  (the engine's `30`-bound per `cdivWf` content strip; satisfiable on a finite run, **Task 2**). -/

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

/-! ## Task 4 — the recursive RDE-oracle field-level soundness, up to the isolated residual

The headline. A successful `crischDESolve f g = some y` over `QFunNZG β` runs `cRischDEG [1] fuel f.1.1 f.1.2
g.1.1 g.1.2 = some (ynum, yden)` over `CPolyG β` (`instCRischFieldQFunNZG`). The §6 boundary theorem
`rdeCleared_of_success_and_residual` turns that bare success — *plus* the isolated
`RischDEStructuralResidual` — into the cleared polynomial RDE identity over `(CFieldSpec.K β)[X]`; the bridge
`rischDE_field_of_cleared` reads it as the field-level Risch-DE identity
`towerFractionFieldDerivG [1] (Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)` (`Y = amG ynum/amG yden`,
`F = amG f.1.1/amG f.1.2`, `G = amG g.1.1/amG g.1.2`). The residual's per-level `Associated`-gcd clauses are
exactly the `CgcdBCorrect` the witness `CTowerGcdWitness β` produces; the residual's *other* clauses
(primitive-regime `hprim`, §6.2 divisibility, the non-gcd `cdvdG`/`cgcdTerminatesG`/fuel clauses of
`CSPDEGClearedInputsGen`) are the precisely-isolated remaining bookkeeping, carried here. -/

section RDESoundness

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFracGcdCore β] [CRischField β]
  [Algebra ℚ (CFieldSpec.K β)] in
/-- **`cdegG [1] = 0`** over a `CFieldDomain`: the monomial derivative `Ds = [CField.one]` the recursive
RDE solve uses (`instCRischFieldQFunNZG`) is a constant, so it is in the **primitive** regime. From
`CFieldDomain.nz_one` (`cisZeroG [1] = false`): `cnormG [1] = [1]` (length `1`), hence `cdegG [1] = 0`. The
`hδ` side-condition `rdeCleared_of_success_and_residual` needs. -/
theorem cdegG_one_eq_zero : cdegG ([CField.one] : CPolyG β) = 0 := by
  have hnz : CPolyG.cisZeroG ([CField.one] : CPolyG β) = false := CFieldDomain.nz_one
  rw [CPolyG.cisZeroG, List.isEmpty_eq_false_iff_exists_mem] at hnz
  -- `cnormG [1] = if isZero one then [] else [one]`, nonempty ⇒ `= [one]`, length 1
  have hcn : CPolyG.cnormG ([CField.one] : CPolyG β) = [CField.one] := by
    show (match CPolyG.cnormG ([] : CPolyG β) with
      | [] => if CField.isZero (CField.one : β) then [] else [CField.one]
      | r => CField.one :: r) = [CField.one]
    show (if CField.isZero (CField.one : β) then ([] : CPolyG β) else [CField.one]) = [CField.one]
    by_cases h1 : CField.isZero (CField.one : β) = true
    · exfalso
      obtain ⟨a, ha⟩ := hnz
      rw [show CPolyG.cnormG ([CField.one] : CPolyG β)
          = (if CField.isZero (CField.one : β) then ([] : CPolyG β) else [CField.one]) from rfl,
        if_pos h1] at ha
      exact absurd ha (List.not_mem_nil)
    · rw [if_neg (by simpa using h1)]
  rw [cdegG, hcn]; rfl

/-- **The §6 RDE residual provider for a successful `QFunNZG β`-solve** `RischDESuccessResidual f g`: the
precisely-isolated remaining bookkeeping beyond the bare success and the gcd witness — the
`RischDEStructuralResidual` (primitive-regime restriction, §6.2 divisibility, the non-gcd
`CSPDEGClearedInputsGen` clauses) on the level-`β` `cRischDEG [1]` run's normal-denominator output, plus the
positive-`deg(bbar)` dispatcher side-condition, and the three denominator-nonzero facts the field bridge
needs. The per-level `Associated`-gcd clauses *inside* `RischDEStructuralResidual` are supplied separately by
`CTowerGcdWitness β`; this bundle is everything else `rdeCleared_of_success_and_residual` +
`rischDE_field_of_cleared` consume. -/
structure RischDESuccessResidual (f g : QFunNZG β) : Prop where
  /-- The §6 structural residual on the level-`β` run (`RischDEStructuralResidual`), for the matching
  normal-denominator output. -/
  hres : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
        = some (a0, b0, c0, h0) →
      RischDEStructuralResidual ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
        a0 b0 c0 h0
  /-- The positive-`deg(bbar)` dispatcher side-condition (Lemma 6.5.1 non-cancellation routing). -/
  hdb : ∀ a0 b0 c0 bbar cbar : CPolyG β, ∀ m : ℤ, ∀ α' β' : CPolyG β,
    cSPDEG ([CField.one] : CPolyG β) towerRischDEFuel
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPolyG β)
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β') → 0 < cdegG bbar
  /-- The output numerator's denominator (the special-denominator 4th component `h0` = `yden`) is nonzero. -/
  hyden : ∀ ynum yden : CPolyG β,
    cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 = some (ynum, yden) →
      toPolyG yden ≠ 0
  /-- The input `f`'s denominator is nonzero. -/
  hfden : toPolyG f.1.2 ≠ 0
  /-- The input `g`'s denominator is nonzero. -/
  hgden : toPolyG g.1.2 ≠ 0

/-- **★ The recursive RDE-oracle field-level soundness, from bare success + the gcd witness + the isolated
residual** (Task 4, the capstone — native-residual-free up to the named residual): if the recursive oracle
solves the Risch DE over `QFunNZG β` (`crischDESolve f g = some y`), then with the tower-gcd witness
`[CTowerGcdWitness β]` (supplying the per-level `Associated`-gcd correctness) and the isolated residual
`RischDESuccessResidual f g` (the primitive-regime / §6.2 divisibility-fuel / non-gcd `CSPDEGClearedInputsGen`
clauses the engine does not self-certify), the returned `y = ynum/yden` solves the field-level Risch DE
`towerFractionFieldDerivG [1] (amG ynum/amG yden) + (amG f.1.1/amG f.1.2)·(amG ynum/amG yden) =
amG g.1.1/amG g.1.2` over `RatFunc (CFieldSpec.K β)`. Composes the §6 boundary
`rdeCleared_of_success_and_residual` (bare success + residual ⟹ cleared identity, primitive regime via
`cdegG_one_eq_zero`) with the cleared → field bridge `rischDE_field_of_cleared`. **No `native_decide`** — the
gcd half is the witness's tower induction, the rest the explicit residual. -/
theorem crischDESolve_field_of_witness_residual [CTowerGcdWitness β]
    (f g y : QFunNZG β) (hsolve : CRischField.crischDESolve f g = some y)
    (hres : RischDESuccessResidual f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) := by
  -- the §6.1 gate passed (the gated oracle returned `some`), so the gated solve reduces to the bare
  -- `cRischDEG [1]`-then-guard match — the success unfolds with `y = ⟨(ynum,yden), _⟩`
  have hgate : cdenomNormalGateG f = true := cdenomNormalGateG_of_crischDESolve_isSome f g y hsolve
  rw [crischDESolve_eq_solve_of_normal f g hgate] at hsolve
  rcases hsucc : cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2
    with _ | ⟨ynum, yden⟩ <;> rw [hsucc] at hsolve
  · exact absurd hsolve (by simp)
  · -- read off `y.1.1 = ynum`, `y.1.2 = yden` from the `dif` success
    simp only at hsolve
    by_cases hyz : CPolyG.cisZeroG yden = false
    · rw [dif_pos hyz, Option.some.injEq] at hsolve
      have hy1 : y.1.1 = ynum := by rw [← hsolve]
      have hy2 : y.1.2 = yden := by rw [← hsolve]
      rw [hy1, hy2]
      -- the cleared polynomial RDE identity from bare success + the isolated residual (primitive regime)
      have hcleared := rdeCleared_of_success_and_residual ([CField.one] : CPolyG β) towerRischDEFuel
        f.1.1 f.1.2 g.1.1 g.1.2 ynum yden cdegG_one_eq_zero hsucc hres.hres hres.hdb
      -- lift the cleared identity through the ring hom `amG β` to the `amG`-image shape the bridge wants
      have hclam := congrArg (amG β) hcleared
      simp only [map_add, map_mul, map_sub, map_pow] at hclam
      -- the field bridge: cleared identity (amG-image) ⟹ the field-level RDE identity
      exact rischDE_field_of_cleared ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2 ynum yden
        hres.hfden hres.hgden (hres.hyden ynum yden hsucc) hclam
    · rw [dif_neg hyz] at hsolve; exact absurd hsolve (by simp)

end RDESoundness

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 4: the recursive RDE oracle's success over QFunNZG β gives the field-level Risch-DE identity,
-- from the gcd witness + the isolated residual — no native_decide.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] [CTowerGcdWitness β]
    (f g y : QFunNZG β) (hsolve : CRischField.crischDESolve f g = some y)
    (hres : RischDESuccessResidual f g) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2) :=
  crischDESolve_field_of_witness_residual f g y hsolve hres

/-! ## Task 5 — the fully-abstract hyperexp normal-part soundness corollary (native-residual-free)

`ComputableHyperexpFullSoundness.cIntegrateHyperexpNormalGWf_sound` is unconditional in `∑c`, reduced to the
**single** documented native residual `hintR` (`D(∫R) = R`, the base-RDE-oracle's pure-integration
soundness — `native_decide`-validated, e.g. `nNormInv_baseIntegral_eq_x`). `crischDESolve_zero_intDeriv`
(`ComputableRischFieldSpec`) discharges exactly that `hintR` from `CRischFieldSpec α` with NO `native_decide`.
So the headline corollary supplies `[CRischFieldSpec α]` and **removes the native residual** — the §5.9
hyperexp normal-part soundness becomes native-residual-free, gated only on the abstract engine bridges
(`hherm`/`hform`/… — the same documented inputs the primitive/hyperexp one-shots take, all algebraic, no
`native_decide`). At base `α = ℚ` the residual oracle is the unconditional `instCRischFieldSpecQ`; at
`QFunNZG β` it is the recursive `CRischFieldSpec` (the precise remaining bookkeeping — see the verdict). -/

section FullyAbstract

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CRischField α] [CRischFieldSpec α]

/-- **★★★ The fully-abstract fuel-free §5.9 hyperexp normal-part soundness**: the runtime driver is
`cIntegrateHyperexpNormalGWf`, the reduced and Hermite data are fuel-free, and the single base-oracle residual
is discharged from `[CRischFieldSpec α]` via `crischDESolve_zero_intDeriv`. -/
theorem cIntegrateHyperexpNormalGWf_sound_of_rischFieldSpec [CFracGcdCoreWf α] (Dt : CPolyG α)
    (a d : CPolyG α) (cands : List α) (res : IntegralResultG α) (intR : α)
    (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α)
    (hDt : toPolyG Dt = C b * X)
    (hgden : toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CField.zero : α)
        (cHyperexpResidualG (cExpEtaG Dt) (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalGWf Dt a d cands = some res)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hRval : amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG Dt)
              (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)))
        = amG α (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  cIntegrateHyperexpNormalGWf_sound Dt a d cands res intR s b hDt hgden hintRsome hsome hherm hden
    hA hnorm hform
    (crischDESolve_zero_intDeriv Dt
      (cHyperexpResidualG (cExpEtaG Dt) (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)
      intR hintRsome)
    hRval

end FullyAbstract

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- ★ Task 5, fuel-free: the §5.9 hyperexp normal-part soundness for `cIntegrateHyperexpNormalGWf`, with
-- the base-oracle native residual discharged from the RDE-oracle spec class.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CRischField α]
    [CRischFieldSpec α]
    (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) (res : IntegralResultG α) (intR : α)
    (s : Finset (CFieldSpec.K α)) (b : CFieldSpec.K α)
    (hDt : toPolyG Dt = C b * X)
    (hgden : toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2 ≠ 0)
    (hintRsome : CRischField.crischDESolve (CField.zero : α)
        (cHyperexpResidualG (cExpEtaG Dt) (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)
      = some intR)
    (hsome : CPolyG.cIntegrateHyperexpNormalGWf Dt a d cands = some res)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hden : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = Lagrange.nodal s id)
    (hA : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree < s.card)
    (hnorm : ∀ β ∈ s, (C b * X).eval β ≠ β′)
    (hform : (CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map
          (fun cv => (CFieldSpec.toK cv.1, toPolyG cv.2))
        = s.toList.map (fun β =>
            ((toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
                / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β,
              X - C β)))
    (hRval : amG α (Polynomial.C (CFieldSpec.toK
            (cHyperexpResidualG (cExpEtaG Dt)
              (CPolyG.cIntegrateReducedGWf Dt a d cands).logs)))
        = amG α (C (b * ∑ β ∈ s,
            (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).eval β
              / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval β))) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  cIntegrateHyperexpNormalGWf_sound_of_rischFieldSpec Dt a d cands res intR s b hDt hgden
    hintRsome hsome hherm hden hA hnorm hform hRval

/-! ## ★ VERDICT — is the recursive `CRischFieldSpec (QFunNZG β)` closed (fully-abstract, native-residual-free)?

**The gcd kernel IS fully discharged from the witness class (Tasks 1–3); the recursive RDE-oracle field
soundness IS closed up to a precisely-isolated, non-`native_decide` residual (Tasks 4–5). The recursive
`CRischFieldSpec (QFunNZG β)` is NOT an unconditional instance — and not because of any `native_decide` or
missing mathematical fact, but because of bookkeeping the *engine does not self-certify*, named exactly
below.**

### What IS closed (axiom-clean `[propext, Classical.choice, Quot.sound]`, NO `native_decide`)

* **The two PRS witnesses, threaded** (`CTowerGcdWitness`, base `ℚ` + recursive `QFunNZG β` builders):
  `CTowerGcdWitness.gcdBCorrect` makes level-`α` gcd-correctness `CgcdBCorrect (cgcdFFRawCore fuel)` a tower
  induction. `cTowerWitness_assocReg` discharges the opaque per-step gate `CPrimPRSGenAssocReg` from the
  witness + the run's own termination/fuel. **So the kernel A⁗ reduced to bookkeeping is now bookkeeping
  *carried by a class*** — no longer an open per-step regularity assumption at the gcd level.
* **The recursive RDE-oracle field identity** (`crischDESolve_field_of_witness_residual`): a successful
  `crischDESolve f g = some y` over `QFunNZG β` ⟹ the field-level Risch-DE identity
  `towerFractionFieldDerivG [1] (Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`, given `[CTowerGcdWitness β]`
  + the isolated `RischDESuccessResidual`. This is the `cRischDEG`-output form of `CRischFieldSpec`'s spec
  (the `towerFractionFieldDerivG`/`amG` reading the §6 layer uses), with the residual **fully explicit**.
* **The fully-abstract hyperexp soundness** (`cIntegrateHyperexpNormalGWf_sound_of_rischFieldSpec`): the
  fuel-free §5.9 normal-part soundness, with the **single** documented native residual `hintR` (`D(∫R) = R`)
  DISCHARGED from
  `[CRischFieldSpec α]` (via the already-clean `crischDESolve_zero_intDeriv`). At base `α = ℚ` the residual
  oracle is the unconditional `instCRischFieldSpecQ`, so this is genuinely `native_decide`-free there.

### The precise remaining bookkeeping (why the recursive instance is NOT unconditional)

To register `instance CRischFieldSpec (QFunNZG β)` one must prove its spec for *every* successful solve. Via
`rdeCleared_of_success_and_residual` that needs the FULL `RischDEStructuralResidual`, whose clauses split:

1. **The per-level `Associated`-gcd clauses** — SUPPLIED by `CTowerGcdWitness β` (Tasks 1–3). Not a residual.
2. **The NON-gcd clauses, the genuine remaining bookkeeping** (`RischDESuccessResidual` here): the
   primitive-regime restriction `hprim` (`cRischDEG` runs *all* monomial regimes; the §6 cleared identity
   `cRischDEG_rdeCleared_gen` is proved primitive-only), the §6.2 divisibility side-conditions
   (`hdn`/`hdvdB`/`hdvdC` — `cRdeNormalDenominatorG` checks only one `cdvdG`, truncating the rest), and the
   non-gcd clauses of `CSPDEGClearedInputsGen` (per-level fuel bounds, `cdvdG`,
   `cgcdTerminatesG`). **None is forced by the bare `cRischDEG … = some _`** (this is the
   `ComputableRischDEStructural` structural-decomposition verdict), and none is a gcd fact the witness
   produces. They hold on every regular run but the engine **never re-validates them**, so they are not
   recoverable from success — exactly the role the integrator's `checkIdentityG` self-check bridge
   (`field_identity_of_checkIdentityG`) plays (the tractable route: a *checked* RDE oracle, an engine
   addition out of this file's scope).
3. **A prerequisite gap**: the `CRischFieldSpec` *class* needs `[CDiffFieldSpec (QFunNZG β)]` to even state
   `(toK y)′`; only the concrete `instCDiffFieldSpecQFunNZG : CDiffFieldSpec (QFunNZG ℚ)` exists — no generic
   one. So even the *statement* of the recursive instance is pinned to a concrete level until that generic
   instance is added (a mechanical lift of `toQFunNZG_towerDerivQFunNZG`). The field identity above sidesteps
   this by reading the conclusion in `towerFractionFieldDerivG`/`amG` form, which needs no `CDiffFieldSpec`.

**Bottom line:** transcendental soundness is native-residual-free *modulo* the explicitly-named
`RischDESuccessResidual` (the primitive-regime / §6.2-divisibility / non-gcd-`CSPDEGClearedInputsGen`
bookkeeping) — NOT modulo any `native_decide`, missing theorem, or the gcd kernel (which is closed). The
honest residual is the §6 pipeline's *structural-decomposition + self-certification* gap, identical in
character to the integrator's `checkIdentityG` route, isolated here so the boundary is citable. -/

/-! ### Axiom audit (the gcd-kernel discharge + the RDE soundness are axiom-clean, no `native_decide`) -/

#print axioms cTowerWitness_assocReg
#print axioms instCTowerGcdWitnessQ_of_terminates
#print axioms crischDESolve_field_of_witness_residual
#print axioms cIntegrateHyperexpNormalGWf_sound_of_rischFieldSpec

end DeepWiki.SymbolicIntegration
