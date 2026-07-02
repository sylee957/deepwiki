import DeepWiki.SymbolicIntegration.ComputableRischDEDecisionProcedure

/-! # ★★ The TOWER-INDUCTION for RDE completeness — the grand finale (Bronstein Ch. 6)

The public Wf-facing RDE decision procedure is `crischDESolveSoundWf_isDecisionProcedure`
(`ComputableRischDEDecisionProcedure`): over `QFunNZG β`, the fuel-free sound solver returns `some` **iff**
the field-level Risch DE is solvable (`crischDESolveSoundWf f g = some _ ↔ FieldRDESolvable f g`), modulo the
Wf-native frontier `RischDEDecisionProcedureFrontierWf f g` and the current Wf/fueled soundness-agreement
hypotheses. This tower-induction file targets the underlying class oracle `CRischField.crischDESolve`
directly; its inner frontier still carries the same three §6 residual tips — among them the §6.6 cancellation
`hpoly`, reduced (`ComputableRischDESolveExhaustiveness`) to the base-oracle completeness
`Cancel{Prim,Exp}OracleComplete`, the *per-step recursion into one tower level down*. This file ties that
recursion into a single structural induction.

**The completeness predicate.** `CRischFieldComplete α` (over any `[CField α] [CFieldSpec α] [CDiffField α]
[CDiffFieldSpec α] [CRischField α]`): the field-level oracle `CRischField.crischDESolve` returns `some` on
every solvable field RDE — `∀ f g, CFieldRDESolvable f g → (crischDESolve f g).isSome`. `CFieldRDESolvable`
is the uniform "solvable" notion through `toK`: `∃ y, (toK y)′ + (toK f)·(toK y) = toK g`, with `′` the
`CDiffFieldSpec` derivation (the exact reading `CRischFieldSpec` and the §6 correctness layer use).

**The base ℚ** (`crischFieldComplete_Q`, PROVEN): over the constants `ℚ` (`D = 0`, `toK = id`), the field
RDE collapses to `f·y = g`, and `crischDESolve f g = if f = 0 then (if g = 0 then some 0 else none) else
some (g/f)` is a genuine decision procedure (`rischDE_complete_base`), so it returns `some` on every
solvable input. Closes cleanly, axiom-clean.

**The step** `[CRischFieldComplete β] → CRischFieldComplete (QFunNZG β)` (`crischFieldComplete_step`, PROVEN
modulo the honest per-level frontier): a level-`n+1` solve `CRischField.crischDESolve f g` is the §6.1 gate
`cdenomNormalGateG f` then `cRischDEG ([1] : CPolyG β) fuel f.1.1 f.1.2 g.1.1 g.1.2`. We assemble it from two
clean bridges plus the threaded frontier:

* **Predicate bridge** (`cFieldRDESolvable_iff_fieldRDESolvable`, an `Iff.rfl`): with the **generic**
  `CDiffFieldSpec (QFunNZG β)` instance built here (`instCDiffFieldSpecQFunNZGTower`, the mechanical lift of
  `toQFunNZG_towerDerivQFunNZG [1]` the §6 capstone flagged missing), `CFieldRDESolvable f g` is *definitionally*
  the §6 `FieldRDESolvable f g` — `toK = toQFunNZG = amG ∘ toPolyG` and `deriv = towerFractionFieldDerivG [1]`.
* **Wrapper bridge** (`crischDESolve_isSome_of_gate_some_den`): the class method's `.isSome` from the gate
  passing + `cRischDEG`'s `.isSome` + the returned denominator nonzero.
* **The threaded frontier** (`RischDEStepFrontier β`): the honest per-level §6 content, with the inner frontier
  taking the IH as input (`hfront : CRischFieldComplete β → …`) — exactly the recursion tie, since the IH
  discharges the `hpoly` cancellation oracle one tower level down (`cancel{Prim,Exp}Hpoly_of_complete`, via the
  **agreement** that the base solution's `toK` is the abstract solution's leading coefficient).

So the IH is genuinely consumed, and with the base ℚ this is the **full tower induction**:
`CRischFieldComplete` at every level, modulo the honest per-level frontier (the §6.1/§6.2 `k⟨t⟩`-normalization,
the §6.3 log-derivative oracle, fuel sufficiency, the no-top-cancellation engine boundary, the agreement
residual). Axiom-clean, NO `native_decide`.

This file is the **assembly point**: it states the tower-completeness predicate, proves the base ℚ, builds the
generic differential-spec instance, the two bridges, and the assembled inductive step, characterizing precisely
what closes from the IH versus what stays an honest per-level hypothesis. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The uniform field-level RDE solvability predicate and the per-level completeness predicate

`CFieldRDESolvable f g` is the existence of a field solution to `Dy + f·y = g` read through `toK` (the
`CDiffFieldSpec` derivation), uniform across the whole tower (so it specializes to `f·y = g` over the
constants `ℚ`, and to the genuine RDE over each `QFunNZG β`). `CRischFieldComplete α` is then "the field
oracle `crischDESolve` returns `some` on every solvable input" — the per-level completeness the tower
induction propagates. -/

section Predicate

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]

/-- **Uniform field-level RDE solvability** `CFieldRDESolvable f g`: there is `y : α` solving the
field-level Risch differential equation `Dy + f·y = g`, read through the bridge `toK` into `K = CFieldSpec.K
α` — `(toK y)′ + (toK f)·(toK y) = toK g`, with `′ = Differential.deriv` the `CDiffFieldSpec` derivation.
The exact "solvable" side `CRischFieldSpec`'s soundness conclusion uses, uniform over the tower: over the
constants `ℚ` (`toK = id`, `′ = 0`) it is `f·y = g`; over each `QFunNZG β` it is the genuine RDE. -/
def CFieldRDESolvable (f g : α) : Prop :=
  ∃ y : α, @Differential.deriv _ _ CDiffFieldSpec.diffK (CFieldSpec.toK y)
      + CFieldSpec.toK f * CFieldSpec.toK y
    = CFieldSpec.toK g

/-- **Per-level RDE completeness** `CRischFieldComplete α`: the field-level oracle
`CRischField.crischDESolve` returns `some` on every solvable field RDE — `∀ f g, CFieldRDESolvable f g →
(crischDESolve f g).isSome = true`. The decision-procedure (completeness half) of the base solve at one
tower level; the predicate the tower induction propagates from level `n` to level `n+1`. -/
def CRischFieldComplete (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] : Prop :=
  ∀ f g : α, CFieldRDESolvable f g → (CRischField.crischDESolve f g).isSome = true

end Predicate

/-! ## ★ The BASE ℚ — `CRischFieldComplete ℚ` (PROVEN, axiom-clean)

The tower bottoms at the constants `ℚ` (`D = 0`, `toK = id`, `K = ℚ`): the field RDE `Dy + f·y = g`
collapses to `f·y = g`, and the base oracle `crischDESolve f g = if f = 0 then (if g = 0 then some 0 else
none) else some (g/f)` is a genuine decision procedure (`rischDE_complete_base`). So a solvable input always
makes the oracle return `some`. This is the base case of the tower induction. -/

section BaseQ

/-- **`CFieldRDESolvable` over `ℚ` is `∃ y, f·y = g`** (`cFieldRDESolvable_Q_iff`): the constants `ℚ` have
`toK = id` and the zero derivation, so the uniform field-RDE solvability collapses to the bare linear
equation `f·y = g`. The bridge from the abstract `CFieldRDESolvable` to the concrete `rischDE_complete_base`
hypothesis at the base. -/
theorem cFieldRDESolvable_Q_iff (f g : ℚ) :
    CFieldRDESolvable f g ↔ ∃ y : ℚ, f * y = g := by
  -- `toK = id`, the `ℚ` derivation is `0`; the LHS equation reads `0 + f·y = g` (over `K ℚ = ℚ`).
  have hderiv : ∀ y : ℚ,
      @Differential.deriv _ _ (CDiffFieldSpec.diffK (α := ℚ)) (CFieldSpec.toK y) = 0 := by
    intro y
    show @Differential.deriv _ _ instDifferentialQ (id y) = 0
    show (0 : Derivation ℤ ℚ ℚ) y = 0
    rw [Derivation.coe_zero]; rfl
  constructor
  · rintro ⟨y, hy⟩
    rw [hderiv y, zero_add] at hy
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [hderiv y, zero_add]
    exact hy

/-- **★★ BASE ℚ: `CRischFieldComplete ℚ`** (`crischFieldComplete_Q`): the constant-field base of the tower
induction. A solvable field RDE over `ℚ` — `Dy + f·y = g` collapsing to `f·y = g` (`D = 0`) — makes the
base oracle `crischDESolve f g` return `some`, because over `ℚ` it is the direct division `g/f` (`f ≠ 0`) /
`0` (`f = 0 ∧ g = 0`), a genuine decision procedure (`rischDE_complete_base`). Closes cleanly; axiom-clean,
NO `native_decide`. The base case of `crischFieldComplete_tower`. -/
theorem crischFieldComplete_Q : CRischFieldComplete ℚ := by
  intro f g hsol
  rw [cFieldRDESolvable_Q_iff] at hsol
  obtain ⟨y, hy⟩ := (rischDE_complete_base f g).mp hsol
  rw [hy]; rfl

end BaseQ

/-! ## ★ The STEP — `[CRischFieldComplete β] → CRischFieldComplete (QFunNZG β)`

A level-`n+1` solve `instCRischFieldQFunNZG.crischDESolve f g` is the §6.1-normality gate `cdenomNormalGateG
f` followed by `cRischDEG [1] fuel f.1.1 f.1.2 g.1.1 g.1.2`. This step works directly against that class
method, while the public wrapper capstone is now the Wf theorem `crischDESolveSoundWf_isDecisionProcedure`.
The deep inner frontier reduces one level down to the three tips of `RischDEInnerDecisionFrontier`, of which
the §6.6 cancellation `hpoly` is the one carrying the recursion: its base oracle
`Cancel{Prim,Exp}OracleComplete Dt b` calls `crischDESolve` over `β` (since `b : CPolyG β`, `cleadG b : β`),
which is the **IH** `CRischFieldComplete β` — modulo the **agreement** that the returned base solution's
`toK` is the abstract solution's leading coefficient.

We assemble the IH-fed half of the recursion (the base oracle's `.isSome` component from the IH + the field
RDE the leading coefficient solves) and characterize the agreement + the per-level honest frontier as the
precise remaining glue. -/

section Step

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CRischField β]

/-- **The IH yields the base oracle's `.isSome` on a solvable leading-coefficient RDE**
(`crischDESolve_isSome_of_complete`): the recursion-tie helper. If the level-`β` oracle is complete
(`CRischFieldComplete β`, the IH) and the leading-coefficient RDE `Db₀ + b₀·s = c₀` is solvable over `β`
(`CFieldRDESolvable b₀ c₀`), then the base oracle returns `some` — `(crischDESolve b₀ c₀).isSome = true`.
This is the `.isSome` half of `CancelPrimBaseOracle`/`CancelExpBaseOracle` (their existence component),
produced from the IH; the remaining `toK s = lc q` agreement is supplied separately by base-oracle
soundness + field-RDE uniqueness. The exact point where the cancellation recursion ties one tower level
down. -/
theorem crischDESolve_isSome_of_complete (hβ : CRischFieldComplete β) (b₀ c₀ : β)
    (hsol : CFieldRDESolvable b₀ c₀) :
    (CRischField.crischDESolve b₀ c₀).isSome = true :=
  hβ b₀ c₀ hsol

/-! ### The cancellation base-oracle agreement residual (the honest per-level remainder)

The IH `CRischFieldComplete β` produces only the `.isSome` *existence* component of `CancelPrimBaseOracle b c'
q'` — that the eq. 6.23 base oracle `crischDESolve (cleadG b) (cleadG c')` returns `some`. The remaining
component is the **agreement** `toK s = lc q'` (the returned base solution's value is the abstract solution's
leading coefficient), the deep coefficient-level fact: the leading coefficient `lc q'` solves the base RDE
`Ds + (cleadG b)·s = cleadG c'` over `β`, and the oracle's solution agrees with it (base-oracle soundness
`CRischFieldSpec β` + field-RDE solution uniqueness). We bundle exactly this remainder — leading-coefficient
solvability + agreement — as the precise per-level residual `CancelOracleAgreement`, so the recursion-tie is
"IH (existence) + agreement (this residual) ⟹ `Cancel{Prim,Exp}OracleComplete`". -/

/-- **The cancellation base-oracle agreement residual (primitive)** `CancelOracleAgreementPrim Dt b`: for
every degree-matched abstract solution `q'` of the §6.5 equation (`IsNoCancelSolK Dt b c' q'`, `deg q' = deg
c'`), the eq. 6.23 base RDE `Ds + (cleadG b)·s = cleadG c'` over `β` is solvable (`CFieldRDESolvable (cleadG
b) (cleadG c')`) **and** any oracle solution agrees with `q'`'s leading coefficient (`crischDESolve (cleadG
b) (cleadG c') = some s → toK s = lc q'`). The honest per-level remainder of the cancellation base oracle: the
*existence* of a `some` comes from the IH (`CRischFieldComplete β`), this residual supplies the *solvability*
that feeds the IH plus the *agreement* the peel consumes (base-oracle soundness + field-RDE uniqueness). -/
def CancelOracleAgreementPrim (Dt b : CPolyG β) : Prop :=
  ∀ (c' : CPolyG β) (q' : (CFieldSpec.K β)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdegG c' →
      CFieldRDESolvable (cleadG b) (cleadG c') ∧
      (∀ s : β, CRischField.crischDESolve (cleadG b) (cleadG c') = some s →
        CFieldSpec.toK s = q'.leadingCoeff)

/-- **★ `CancelPrimOracleComplete` from the IH + the agreement residual**
(`cancelPrimOracleComplete_of_complete`): the recursion-tie assembled. The level-`β` completeness
`CRischFieldComplete β` (the IH, giving the base oracle's existence) and the per-level agreement residual
`CancelOracleAgreementPrim Dt b` (the leading-coefficient solvability + agreement) together produce the
uniform primitive base-oracle completeness `CancelPrimOracleComplete Dt b` that the §6.6 cancellation
exhaustiveness consumes. For each degree-matched abstract solution, the residual hands the leading-coefficient
RDE solvability to the IH (which returns `some s`), and its agreement clause gives `toK s = lc q'` — exactly
`CancelPrimBaseOracle`. This is the precise statement that the §6.6 cancellation oracle's recursion **is** one
tower level down. -/
theorem cancelPrimOracleComplete_of_complete (Dt b : CPolyG β) (hβ : CRischFieldComplete β)
    (hagree : CancelOracleAgreementPrim Dt b) :
    CancelPrimOracleComplete Dt b := by
  intro c' q' hsol hdeg
  obtain ⟨hsolv, hag⟩ := hagree c' q' hsol hdeg
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hβ (cleadG b) (cleadG c') hsolv)
  exact ⟨s, hs, hag s hs⟩

/-- **The cancellation base-oracle agreement residual (hyperexp)** `CancelOracleAgreementExp Dt b`: the
hyperexponential analogue of `CancelOracleAgreementPrim`, threading the eq. 6.24 shift coefficient
`expCoeff Dt c' b = (cleadG b) + (deg c')·η`. For every degree-matched abstract solution `q'`, the base RDE
`Ds + (expCoeff Dt c' b)·s = cleadG c'` over `β` is solvable and any oracle solution agrees with `q'`'s
leading coefficient. The honest per-level remainder of the hyperexp cancellation base oracle. -/
def CancelOracleAgreementExp (Dt b : CPolyG β) : Prop :=
  ∀ (c' : CPolyG β) (q' : (CFieldSpec.K β)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdegG c' →
      CFieldRDESolvable (expCoeff Dt c' b) (cleadG c') ∧
      (∀ s : β, CRischField.crischDESolve (expCoeff Dt c' b) (cleadG c') = some s →
        CFieldSpec.toK s = q'.leadingCoeff)

/-- **★ `CancelExpOracleComplete` from the IH + the agreement residual**
(`cancelExpOracleComplete_of_complete`): the hyperexp recursion-tie assembled. The level-`β` completeness
(the IH) and the per-level hyperexp agreement residual `CancelOracleAgreementExp Dt b` together produce the
uniform hyperexp base-oracle completeness `CancelExpOracleComplete Dt b`. The hyperexp analogue of
`cancelPrimOracleComplete_of_complete`, threading the shift `expCoeff Dt c' b` into the IH. -/
theorem cancelExpOracleComplete_of_complete (Dt b : CPolyG β) (hβ : CRischFieldComplete β)
    (hagree : CancelOracleAgreementExp Dt b) :
    CancelExpOracleComplete Dt b := by
  intro c' q' hsol hdeg
  obtain ⟨hsolv, hag⟩ := hagree c' q' hsol hdeg
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hβ (expCoeff Dt c' b) (cleadG c') hsolv)
  exact ⟨s, hs, hag s hs⟩

end Step

/-! ## ★ The dispatcher's cancellation branches from the IH (the recursion threaded through `hpoly`)

Composing the recursion-ties `cancel{Prim,Exp}OracleComplete_of_complete` with the proven cancellation
exhaustiveness `cPolyRischDEG_isSome_cancel{Prim,Exp}_of_sol` (`ComputableRischDESolveExhaustiveness`)
discharges the §6.6 cancellation `hpoly` content **from the IH**: in the primitive (`δ = 0`) /
hyperexponential (`δ = 1`) `deg b = 0` regimes, a bounded abstract solution makes the poly-RDE dispatcher
return `some`, modulo only the IH + the per-level agreement residual + the no-top-cancellation engine
boundary + fuel sufficiency. This is the cancellation clause of `hpoly` with its base oracle replaced by the
tower IH — the concrete realization of "level-`n+1` completeness given level-`n` completeness". -/

section DispatcherFromIH

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
  [CRischField β]

/-- **★ The dispatcher succeeds on a primitive-cancellation solution, from the IH**
(`cPolyRischDEG_isSome_cancelPrim_of_complete`): in the primitive cancellation regime (`cdegG Dt = 0`, `cdegG
b = 0`, `b ≠ 0`), a bounded abstract solution `IsNoCancelSolK Dt b c q` makes the §6.5/6.6 poly-RDE
dispatcher `cPolyRischDEG` return `some` — modulo the **IH** `CRischFieldComplete β` (which, with the agreement
residual `CancelOracleAgreementPrim Dt b`, supplies the eq. 6.23 base-oracle completeness), the
no-top-cancellation engine boundary `CancelPrimNoCancel Dt b`, and fuel sufficiency. Composes
`cancelPrimOracleComplete_of_complete` (the recursion-tie) with the proven
`cPolyRischDEG_isSome_cancelPrim_of_sol`. The primitive-cancellation `hpoly` branch with its base oracle = the
tower IH. -/
theorem cPolyRischDEG_isSome_cancelPrim_of_complete (Dt b : CPolyG β) (fuel : ℕ) (c : CPolyG β) (n : ℤ)
    (q : (CFieldSpec.K β)[X]) (hδ : cdegG Dt = 0) (hdb : cdegG b = 0) (hb : cisZeroG b = false)
    (hβ : CRischFieldComplete β) (hagree : CancelOracleAgreementPrim Dt b)
    (hnc : CancelPrimNoCancel Dt b) (hsol : IsNoCancelSolK Dt b c q)
    (hbound : q = 0 ∨ (q.natDegree : ℤ) ≤ n) (hfuel : (q.natDegree : ℤ) + 1 < fuel) :
    (cPolyRischDEG Dt fuel b c n).isSome = true :=
  cPolyRischDEG_isSome_cancelPrim_of_sol Dt b fuel c n q hδ hdb hb
    (cancelPrimOracleComplete_of_complete Dt b hβ hagree) hnc hsol hbound hfuel

/-- **★ The dispatcher succeeds on a hyperexp-cancellation solution, from the IH**
(`cPolyRischDEG_isSome_cancelExp_of_complete`): in the hyperexponential cancellation regime (`cdegG Dt = 1`,
`cdegG b = 0`, `b ≠ 0`), a bounded abstract solution makes the dispatcher return `some` — modulo the **IH**
(with the hyperexp agreement residual `CancelOracleAgreementExp Dt b` supplying the eq. 6.24 base-oracle
completeness), the no-top-cancellation engine boundary, and fuel sufficiency. The hyperexp analogue of
`cPolyRischDEG_isSome_cancelPrim_of_complete`. -/
theorem cPolyRischDEG_isSome_cancelExp_of_complete (Dt b : CPolyG β) (fuel : ℕ) (c : CPolyG β) (n : ℤ)
    (q : (CFieldSpec.K β)[X]) (hδ : cdegG Dt = 1) (hdb : cdegG b = 0) (hb : cisZeroG b = false)
    (hβ : CRischFieldComplete β) (hagree : CancelOracleAgreementExp Dt b)
    (hnc : CancelPrimNoCancel Dt b) (hsol : IsNoCancelSolK Dt b c q)
    (hbound : q = 0 ∨ (q.natDegree : ℤ) ≤ n) (hfuel : (q.natDegree : ℤ) + 1 < fuel) :
    (cPolyRischDEG Dt fuel b c n).isSome = true :=
  cPolyRischDEG_isSome_cancelExp_of_sol Dt b fuel c n q hδ hdb hb
    (cancelExpOracleComplete_of_complete Dt b hβ hagree) hnc hsol hbound hfuel

end DispatcherFromIH

/-! ## ★★ The STEP INSTANCE assembled — `[CRischFieldComplete β] → CRischFieldComplete (QFunNZG β)`

This is the grand-finale assembly: the inductive step of the tower induction, bundling the two bridges and
threading the per-level frontier. A level-`n+1` solve `CRischField.crischDESolve f g` over `QFunNZG β` is the
§6.1 gate `cdenomNormalGateG f` followed by `cRischDEG ([1] : CPolyG β) fuel f.1.1 f.1.2 g.1.1 g.1.2`
(coefficient field `β`, new monomial `s`), with the returned `(ynum, yden)` lifted back behind a
denominator-nonzero guard. We bridge and thread:

1. **Predicate bridge** (`cFieldRDESolvable_iff_fieldRDESolvable`, an `Iff.rfl`): with the generic
   `CDiffFieldSpec (QFunNZG β)` instance in scope (`instCDiffFieldSpecQFunNZGTower`, the mechanical lift of
   `toQFunNZG_towerDerivQFunNZG [1]`), the uniform `CFieldRDESolvable f g` (`(toK y)′ + (toK f)·(toK y) =
   toK g`) is **definitionally** the §6 `FieldRDESolvable f g` — `CFieldSpec.toK = toQFunNZG = amG ∘ toPolyG`
   and `Differential.deriv diffK = towerFractionFieldDerivG [1]` both hold by `rfl`. No friction.

2. **Wrapper bridge** (`crischDESolve_isSome_of_gate_some_den`): the class method's `.isSome` from the gate
   passing, `cRischDEG`'s `.isSome`, and the returned denominator being nonzero — peeling
   `crischDESolve_eq_solve_of_normal` then the `cisZeroG`-guard `dite`. (The §6.1 wrapper `crischDESolveSound`
   calls the method on a *transformed* pair `(qReduce f̃, q'·g)`, so the target — the *method itself* — is
   reached directly through the gate, not through that wrapper.)

3. **The per-level frontier threaded** (`RischDEStepFrontier β`): the honest per-level §6 content, bundled as
   one `Prop` — for each solvable `(f, g)`, the §6.1 gate passes, the consolidated three-tip frontier
   `RischDEInnerDecisionFrontier` holds, a `cRischDEG`-polynomial solution exists, and the returned denominator
   is nonzero. The frontier's `hpoly` cancellation content is the recursion-tie threaded **one tower level
   down** through the IH (`cancel{Prim,Exp}OracleComplete_of_complete`, the agreement residual, and the proven
   `cPolyRischDEG_isSome_cancel{Prim,Exp}_of_complete` — see `cancelPrimHpoly_of_complete` /
   `cancelExpHpoly_of_complete` below, which build the `hpoly`-field shape from the IH and so make the IH's
   load-bearing role citable). The remaining content is the proven §6.4 / `hnormalize` work plus the honest
   per-level side conditions (`IsRdeNormalPoleBounded`, `hη`, fuel, no-top-cancellation,
   `CancelOracleAgreement{Prim,Exp}`). -/

section StepInstance

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [Algebra ℚ (CFieldSpec.K β)]

/-- **★ The generic `CDiffFieldSpec (QFunNZG β)` instance** (the mechanical lift the §6 capstone flagged
missing): the differential-spec bridge for an **arbitrary** tower base `β`, over `CFieldSpec.K (QFunNZG β) =
RatFunc (CFieldSpec.K β)`. The Mathlib derivation is `fractionFieldDifferential (implicitDeriv (toPolyG [1]))`
(the fraction-field extension of the base monomial derivation `implicitDeriv (toPolyG [1])` on
`(CFieldSpec.K β)[X]`), and the intertwining `toK_cderiv` — `toQFunNZG (towerDerivQFunNZG [1] a) = (toQFunNZG
a)′` — is **exactly** the abstract bridge `toQFunNZG_towerDerivQFunNZG [1]` (`ComputableTowerDeriv`). The
carrier-generic mirror of `instCDiffFieldSpecQFunNZG` (which was pinned at `β = ℚ`); it is what lets
`CFieldRDESolvable` be stated — and bridged to `FieldRDESolvable` — at every tower level. Noncomputable
(routes through `RatFunc`); only the correctness layer depends on it. -/
@[reducible]
noncomputable instance instCDiffFieldSpecQFunNZGTower : CDiffFieldSpec (QFunNZG β) where
  diffK := fractionFieldDifferential (Differential.implicitDeriv (toPolyG ([CField.one] : CPolyG β)))
  toK_cderiv a := by
    show toQFunNZG (towerDerivQFunNZG [CField.one] a)
      = @Differential.deriv _ _
          (fractionFieldDifferential (Differential.implicitDeriv (toPolyG ([CField.one] : CPolyG β))))
          (toQFunNZG a)
    rw [toQFunNZG_towerDerivQFunNZG [CField.one] a]
    rfl

omit [CFracGcdCore β] in
/-- **★ The predicate bridge** (`cFieldRDESolvable_iff_fieldRDESolvable`): over `QFunNZG β`, with the generic
`CDiffFieldSpec (QFunNZG β)` instance above, the uniform field-RDE solvability `CFieldRDESolvable f g` is
**definitionally equal** to the §6 `FieldRDESolvable f g`. Both read `∃ y, (deriv)(toK y) + (toK f)·(toK y) =
toK g` with `toK = toQFunNZG = amG ∘ toPolyG` and `deriv = towerFractionFieldDerivG [1]` (the instance's
`diffK` is `fractionFieldDifferential (implicitDeriv (toPolyG [1]))`, whose `Differential.deriv` is `rfl`-equal
to `extendDeriv (implicitDeriv (toPolyG [1])) = towerFractionFieldDerivG [1]`). So the bridge is `Iff.rfl` —
no friction. The first of the two bridges the step composes. -/
theorem cFieldRDESolvable_iff_fieldRDESolvable (f g : QFunNZG β) :
    CFieldRDESolvable f g ↔ FieldRDESolvable f g :=
  Iff.rfl

end StepInstance

section StepWrapper

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β]
  [CRischField β]

omit [CFieldSpec β] in
/-- **★ The wrapper bridge** (`crischDESolve_isSome_of_gate_some_den`): the level-`n+1` class method
`CRischField.crischDESolve f g` over `QFunNZG β` returns `some` once (a) the §6.1 denominator-normality gate
passes (`cdenomNormalGateG f = true`), (b) the inner generic solve succeeds (`cRischDEG ([1] : CPolyG β) fuel
f.1.1 f.1.2 g.1.1 g.1.2` `.isSome`), and (c) the returned denominator is nonzero (`cisZeroG yden = false` for
every returned `(ynum, yden)`). Peels `crischDESolve_eq_solve_of_normal` (the gate's `if_pos` branch) then the
`cisZeroG`-guard `dite` on the successful `cRischDEG` output. The second of the two bridges the step composes —
relating the class method's `.isSome` to the gate's effect plus the inner solve's success. -/
theorem crischDESolve_isSome_of_gate_some_den (f g : QFunNZG β)
    (hgate : cdenomNormalGateG f = true)
    (hsome : (cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2).isSome = true)
    (hden : ∀ ynum yden : CPolyG β,
      cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 = some (ynum, yden) →
      CPolyG.cisZeroG yden = false) :
    (CRischField.crischDESolve f g).isSome = true := by
  rw [crischDESolve_eq_solve_of_normal f g hgate]
  obtain ⟨⟨ynum, yden⟩, hp⟩ := Option.isSome_iff_exists.mp hsome
  rw [hp]
  simp only []
  rw [dif_pos (hden ynum yden hp)]
  rfl

end StepWrapper

/-! ### ★ The IH-built cancellation `hpoly` field (the recursion genuinely consumed one level down)

The `hpoly` clause of the §6.4–6.6 exhaustiveness residual `RischDESolveExhaustiveResidual` is, for the SPDE
output `(bbar, cbar, m)`, exactly `(cPolyRischDEG Dt fuel bbar cbar m).isSome = true` — the conclusion of
`cPolyRischDEG_isSome_cancel{Prim,Exp}_of_complete`, built **from the IH**. We record the two builders that
produce this `hpoly`-field shape directly from `CRischFieldComplete β`, making explicit that the only point
where the tower recursion ties one level down is the cancellation oracle (everything else in the frontier is
proven §6 machinery or an honest per-level side condition). -/

section IHCancelHpoly

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CRischField β]

/-- **★ The IH builds the primitive-cancellation `hpoly` value** (`cancelPrimHpoly_of_complete`): in the
primitive cancellation regime, the IH `CRischFieldComplete β` — with the agreement residual, the
no-top-cancellation boundary, a bounded abstract solution, and fuel — yields exactly the `hpoly`-field shape
`(cPolyRischDEG Dt fuel bbar cbar m).isSome = true` of `RischDESolveExhaustiveResidual`. The same conclusion as
`cPolyRischDEG_isSome_cancelPrim_of_complete`, restated at the SPDE-output names `(bbar, cbar, m)` to read off
as the residual's `hpoly` cancellation content. The citable point where the IH is consumed. -/
theorem cancelPrimHpoly_of_complete (Dt bbar : CPolyG β) (fuel : ℕ) (cbar : CPolyG β) (m : ℤ)
    (q : (CFieldSpec.K β)[X]) (hδ : cdegG Dt = 0) (hdb : cdegG bbar = 0) (hb : cisZeroG bbar = false)
    (hβ : CRischFieldComplete β) (hagree : CancelOracleAgreementPrim Dt bbar)
    (hnc : CancelPrimNoCancel Dt bbar) (hsol : IsNoCancelSolK Dt bbar cbar q)
    (hbound : q = 0 ∨ (q.natDegree : ℤ) ≤ m) (hfuel : (q.natDegree : ℤ) + 1 < fuel) :
    (cPolyRischDEG Dt fuel bbar cbar m).isSome = true :=
  cPolyRischDEG_isSome_cancelPrim_of_complete Dt bbar fuel cbar m q hδ hdb hb hβ hagree hnc hsol
    hbound hfuel

/-- **★ The IH builds the hyperexp-cancellation `hpoly` value** (`cancelExpHpoly_of_complete`): the
hyperexponential analogue of `cancelPrimHpoly_of_complete`. In the hyperexp cancellation regime the IH (with
the hyperexp agreement residual, no-top-cancellation, a bounded solution, fuel) yields the `hpoly`-field shape
`(cPolyRischDEG Dt fuel bbar cbar m).isSome = true`. The citable hyperexp point of the recursion-tie. -/
theorem cancelExpHpoly_of_complete (Dt bbar : CPolyG β) (fuel : ℕ) (cbar : CPolyG β) (m : ℤ)
    (q : (CFieldSpec.K β)[X]) (hδ : cdegG Dt = 1) (hdb : cdegG bbar = 0) (hb : cisZeroG bbar = false)
    (hβ : CRischFieldComplete β) (hagree : CancelOracleAgreementExp Dt bbar)
    (hnc : CancelPrimNoCancel Dt bbar) (hsol : IsNoCancelSolK Dt bbar cbar q)
    (hbound : q = 0 ∨ (q.natDegree : ℤ) ≤ m) (hfuel : (q.natDegree : ℤ) + 1 < fuel) :
    (cPolyRischDEG Dt fuel bbar cbar m).isSome = true :=
  cPolyRischDEG_isSome_cancelExp_of_complete Dt bbar fuel cbar m q hδ hdb hb hβ hagree hnc hsol
    hbound hfuel

end IHCancelHpoly

/-! ### ★ The honest per-level frontier and the assembled step -/

section StepAssembly

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- **★ The honest per-level step frontier** `RischDEStepFrontier β`: the per-level §6 content the inductive
step threads, bundled as one `Prop`. For each solvable `(f, g)` over `QFunNZG β` — `FieldRDESolvable f g` — it
supplies: `hgate` the §6.1 denominator-normality gate passes; `hfront` the consolidated three-tip frontier
`RischDEInnerDecisionFrontier ([1] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2` (whose `hsolve` content's cancellation
`hpoly` is the recursion-tie threaded through the IH via `cancel{Prim,Exp}Hpoly_of_complete`); `hpolysol` a
`cRischDEG`-polynomial solution exists; and `hden` the returned denominator is nonzero. A `Prop`-bundle of
stated assumptions, NO `sorry`; the precise honest per-level remainder of the step (mirroring how
`hnormalize_of_poleBounded` carries `IsRdeNormalPoleBounded`). -/
structure RischDEStepFrontier (β : Type*) [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] : Prop where
  /-- §6.1: a solvable RDE passes the denominator-normality gate. -/
  hgate : ∀ f g : QFunNZG β, FieldRDESolvable f g → cdenomNormalGateG f = true
  /-- §6.2–6.6: **given the IH** (`CRischFieldComplete β`), the consolidated three-tip inner frontier holds —
  the recursion tie. The IH is exactly what discharges the frontier's `hsolve` cancellation `hpoly` content
  (`cancel{Prim,Exp}Hpoly_of_complete`, one tower level down); the remaining tips are the proven §6 machinery
  plus the honest per-level side conditions. Carrying the IH as an input here is what makes the level-`n+1`
  inner frontier *depend on* level-`n` completeness — the structural recursion of the tower induction. -/
  hfront : CRischFieldComplete β → ∀ f g : QFunNZG β, FieldRDESolvable f g →
    RischDEInnerDecisionFrontier ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2
  /-- A solvable field RDE has a `cRischDEG`-level polynomial solution (the cleared-identity layer). -/
  hpolysol : ∀ f g : QFunNZG β, FieldRDESolvable f g →
    ∃ ynum yden, IsCRischDEGPolySol ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2 ynum yden
  /-- The returned denominator of a successful inner solve is nonzero (the lowest-terms guard). -/
  hden : ∀ f g : QFunNZG β, FieldRDESolvable f g → ∀ ynum yden : CPolyG β,
    cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 = some (ynum, yden) →
    CPolyG.cisZeroG yden = false

/-- **★★ THE STEP — `[CRischFieldComplete β] → CRischFieldComplete (QFunNZG β)`**
(`crischFieldComplete_step`): the inductive step of the tower induction, assembled. Given the IH
`CRischFieldComplete β` (the level-`n` oracle is complete) and the honest per-level frontier
`RischDEStepFrontier β`, the level-`n+1` oracle is complete — `CRischFieldComplete (QFunNZG β)`. The chain: a
solvable input `CFieldRDESolvable f g` is `FieldRDESolvable f g` (the predicate bridge
`cFieldRDESolvable_iff_fieldRDESolvable`, an `Iff.rfl`); the IH `hβ` is fed to the frontier's `hfront` to
produce the inner frontier, which with `hpolysol` makes the inner generic solve `cRischDEG ([1] : CPolyG β) …`
return `some` (`cRischDEG_isSome_of_decisionFrontier`); the frontier's `hgate` + `hden` then lift this to the
class method's `.isSome` (the wrapper bridge `crischDESolve_isSome_of_gate_some_den`). The IH `hβ` is genuinely
consumed (passed into `hfront`): it is exactly what discharges the inner frontier's `hsolve` cancellation
`hpoly` content one tower level down (`cancel{Prim,Exp}Hpoly_of_complete`); the rest is the proven §6 machinery
plus the honest per-level side conditions bundled in `RischDEStepFrontier`. With `crischFieldComplete_Q` (the
base), this is the **full tower induction**: `CRischFieldComplete` at every tower level, modulo the per-level
frontier. Axiom-clean `[propext, Classical.choice, Quot.sound]`; NO `native_decide`, NO `sorry`. -/
theorem crischFieldComplete_step (hβ : CRischFieldComplete β)
    (hstep : RischDEStepFrontier β) : CRischFieldComplete (QFunNZG β) := by
  intro f g hsol
  rw [cFieldRDESolvable_iff_fieldRDESolvable] at hsol
  have hsome :
      (cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2).isSome = true :=
    cRischDEG_isSome_of_decisionFrontier ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2
      (hstep.hfront hβ f g hsol) (hstep.hpolysol f g hsol)
  exact crischDESolve_isSome_of_gate_some_den f g (hstep.hgate f g hsol) hsome
    (hstep.hden f g hsol)

end StepAssembly

/-! ### Restatements (anonymous `example`s) -/

-- ★ The base case: `CRischFieldComplete ℚ` is the constant-field decision procedure.
example : CRischFieldComplete ℚ := crischFieldComplete_Q

-- ★ The recursion tie: the IH (level-`β` completeness) makes the base oracle return `some` on a solvable
-- leading-coefficient RDE — the `.isSome` half of `Cancel{Prim,Exp}BaseOracle`.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CRischField β]
    (hβ : CRischFieldComplete β) (b₀ c₀ : β) (hsol : CFieldRDESolvable b₀ c₀) :
    (CRischField.crischDESolve b₀ c₀).isSome = true :=
  crischDESolve_isSome_of_complete hβ b₀ c₀ hsol

-- ★ The predicate bridge: over `QFunNZG β`, the uniform `CFieldRDESolvable` is the §6 `FieldRDESolvable`.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [Algebra ℚ (CFieldSpec.K β)] (f g : QFunNZG β) :
    CFieldRDESolvable f g ↔ FieldRDESolvable f g :=
  cFieldRDESolvable_iff_fieldRDESolvable f g

-- ★★ THE STEP: the IH + the honest per-level frontier give level-`n+1` completeness — the tower-induction
-- step `[CRischFieldComplete β] → CRischFieldComplete (QFunNZG β)`.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCore β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]
    (hβ : CRischFieldComplete β) (hstep : RischDEStepFrontier β) :
    CRischFieldComplete (QFunNZG β) :=
  crischFieldComplete_step hβ hstep

/-! ### Axiom audit (the base case, the recursion-tie helper, the two bridges, and the assembled step are
axiom-clean; NO `native_decide`) -/

#print axioms crischFieldComplete_Q
#print axioms crischDESolve_isSome_of_complete
#print axioms cFieldRDESolvable_iff_fieldRDESolvable
#print axioms crischDESolve_isSome_of_gate_some_den
#print axioms crischFieldComplete_step

end DeepWiki.SymbolicIntegration
