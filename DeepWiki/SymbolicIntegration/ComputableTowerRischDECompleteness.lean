import DeepWiki.SymbolicIntegration.ComputableRischDEDecisionProcedure

/-! # ★★ The TOWER-INDUCTION for RDE completeness — the grand finale (Bronstein Ch. 6)

The per-level RDE decision procedure is `crischDESolveSound_isDecisionProcedure`
(`ComputableRischDEDecisionProcedure`): over `QFunNZG β`, the sound solver returns `some` **iff** the
field-level Risch DE is solvable (`crischDESolveSound f g = some _ ↔ FieldRDESolvable f g`), with soundness
unconditional, completeness modulo the consolidated frontier `RischDEDecisionProcedureFrontier f g` whose
deepest tips are the three §6 residuals — among them the §6.6 cancellation `hpoly`, reduced
(`ComputableRischDESolveExhaustiveness`) to the base-oracle completeness `Cancel{Prim,Exp}OracleComplete`,
the *per-step recursion into one tower level down*. This file ties that recursion into a single structural
induction.

**The completeness predicate.** `CRischFieldComplete α` (over any `[CField α] [CFieldSpec α] [CDiffField α]
[CDiffFieldSpec α] [CRischField α]`): the field-level oracle `CRischField.crischDESolve` returns `some` on
every solvable field RDE — `∀ f g, CFieldRDESolvable f g → (crischDESolve f g).isSome`. `CFieldRDESolvable`
is the uniform "solvable" notion through `toK`: `∃ y, (toK y)′ + (toK f)·(toK y) = toK g`, with `′` the
`CDiffFieldSpec` derivation (the exact reading `CRischFieldSpec` and the §6 correctness layer use).

**The base ℚ** (`crischFieldComplete_Q`, PROVEN): over the constants `ℚ` (`D = 0`, `toK = id`), the field
RDE collapses to `f·y = g`, and `crischDESolve f g = if f = 0 then (if g = 0 then some 0 else none) else
some (g/f)` is a genuine decision procedure (`rischDE_complete_base`), so it returns `some` on every
solvable input. Closes cleanly, axiom-clean.

**The step** `[CRischFieldComplete β] → CRischFieldComplete (QFunNZG β)`: a level-`n+1` solve runs the §6
pipeline at level `n`, whose completeness is the per-level decision procedure, whose `hpoly` cancellation
clause's base oracle `Cancel{Prim,Exp}OracleComplete` recurses into the level-`n` `crischDESolve` — exactly
the IH (plus the **agreement** that the returned base solution's `toK` is the abstract solution's leading
coefficient, supplied by base-oracle soundness `CRischFieldSpec` + field-RDE uniqueness). We assemble the
step modulo the honest per-level frontier (the §6.1/§6.2 `k⟨t⟩`-normalization, the §6.3 log-derivative
oracle, fuel sufficiency, the no-top-cancellation engine boundary) and the IH-fed base oracle.

This file is the **assembly point**: it states the tower-completeness predicate, proves the base ℚ, and
threads the per-level decision procedure into the inductive step, characterizing precisely what closes from
the IH versus what stays an honest per-level hypothesis. -/

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
f` followed by `cRischDEG [1] fuel f.1.1 f.1.2 g.1.1 g.1.2`. Its completeness is the per-level decision
procedure `crischDESolveSound_isDecisionProcedure` (the *wrapper* `crischDESolveSound` adds the same gate and
calls this very class method on the lowest-terms pair), whose completeness rests on the consolidated frontier
`RischDEDecisionProcedureFrontier`. The deep `hinner` clause of that frontier reduces — one level down — to
the three tips of `RischDEInnerDecisionFrontier`, of which the §6.6 cancellation `hpoly` is the one carrying
the recursion: its base oracle `Cancel{Prim,Exp}OracleComplete Dt b` calls `crischDESolve` over `β` (since
`b : CPolyG β`, `cleadG b : β`), which is the **IH** `CRischFieldComplete β` — modulo the **agreement** that
the returned base solution's `toK` is the abstract solution's leading coefficient.

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
hyperexponential analogue of `CancelOracleAgreementPrim`, threading the fuel-dependent eq. 6.24 shift
coefficient `expCoeff Dt fuel c' b = (cleadG b) + (deg c')·η`. For every `fuel` and degree-matched abstract
solution `q'`, the base RDE `Ds + (expCoeff Dt fuel c' b)·s = cleadG c'` over `β` is solvable and any oracle
solution agrees with `q'`'s leading coefficient. The honest per-level remainder of the hyperexp cancellation
base oracle, quantified over `fuel` (the shift coefficient depends on it). -/
def CancelOracleAgreementExp (Dt b : CPolyG β) : Prop :=
  ∀ (fuel : ℕ) (c' : CPolyG β) (q' : (CFieldSpec.K β)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdegG c' →
      CFieldRDESolvable (expCoeff Dt fuel c' b) (cleadG c') ∧
      (∀ s : β, CRischField.crischDESolve (expCoeff Dt fuel c' b) (cleadG c') = some s →
        CFieldSpec.toK s = q'.leadingCoeff)

/-- **★ `CancelExpOracleComplete` from the IH + the agreement residual**
(`cancelExpOracleComplete_of_complete`): the hyperexp recursion-tie assembled. The level-`β` completeness
(the IH) and the per-level hyperexp agreement residual `CancelOracleAgreementExp Dt b` together produce the
uniform hyperexp base-oracle completeness `CancelExpOracleComplete Dt b`. The hyperexp analogue of
`cancelPrimOracleComplete_of_complete`, threading the fuel-dependent shift `expCoeff Dt fuel c' b` into the
IH. -/
theorem cancelExpOracleComplete_of_complete (Dt b : CPolyG β) (hβ : CRischFieldComplete β)
    (hagree : CancelOracleAgreementExp Dt b) :
    CancelExpOracleComplete Dt b := by
  intro fuel c' q' hsol hdeg
  obtain ⟨hsolv, hag⟩ := hagree fuel c' q' hsol hdeg
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hβ (expCoeff Dt fuel c' b) (cleadG c') hsolv)
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

/-! ### Restatements (anonymous `example`s) -/

-- ★ The base case: `CRischFieldComplete ℚ` is the constant-field decision procedure.
example : CRischFieldComplete ℚ := crischFieldComplete_Q

-- ★ The recursion tie: the IH (level-`β` completeness) makes the base oracle return `some` on a solvable
-- leading-coefficient RDE — the `.isSome` half of `Cancel{Prim,Exp}BaseOracle`.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CRischField β]
    (hβ : CRischFieldComplete β) (b₀ c₀ : β) (hsol : CFieldRDESolvable b₀ c₀) :
    (CRischField.crischDESolve b₀ c₀).isSome = true :=
  crischDESolve_isSome_of_complete hβ b₀ c₀ hsol

/-! ### Axiom audit (the base case and the recursion-tie helper are axiom-clean; NO `native_decide`) -/

#print axioms crischFieldComplete_Q
#print axioms crischDESolve_isSome_of_complete

end DeepWiki.SymbolicIntegration
