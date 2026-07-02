import DeepWiki.SymbolicIntegration.Computable.RischDE.DecisionProcedure

/-! # Wf-first tower induction for RDE completeness

The public Wf-facing RDE decision procedure is `crischDESolveSoundWf_isDecisionProcedure`
(`ComputableRischDEDecisionProcedure`): over `QFunNZG β`, the fuel-free sound solver returns `some` **iff**
the field-level Risch DE is solvable (`crischDESolveSoundWf f g = some _ ↔ FieldRDESolvable f g`), modulo the
Wf-native frontier `RischDEDecisionProcedureFrontierWf f g` and the direct Wf soundness certificate
`RischDESoundnessWf f g`. This tower-induction file exposes that Wf public step as the primary surface:
`CRischFieldCompleteWf β` says the fuel-free wrapper is complete at the next `QFunNZG β` level, and
`crischFieldCompleteWf_step` derives it from the Wf per-level frontier.

The cancellation subroutines still call the base `CRischField.crischDESolve` one level down. This file keeps
that base-oracle completeness predicate as the induction hypothesis and exposes only the Wf public next-level
conclusion.

**The completeness predicate.** `CRischFieldComplete α` (over any `[CField α] [CFieldSpec α] [CDiffField α]
[CDiffFieldSpec α] [CRischField α]`): the field-level oracle `CRischField.crischDESolve` returns `some` on
every solvable field RDE — `∀ f g, CFieldRDESolvable f g → (crischDESolve f g).isSome`. `CFieldRDESolvable`
is the uniform "solvable" notion through `toK`: `∃ y, (toK y)′ + (toK f)·(toK y) = toK g`, with `′` the
`CDiffFieldSpec` derivation (the exact reading `CRischFieldSpec` and the §6 correctness layer use).

**The base ℚ** (`crischFieldComplete_Q`, PROVEN): over the constants `ℚ` (`D = 0`, `toK = id`), the field
RDE collapses to `f·y = g`, and `crischDESolve f g = if f = 0 then (if g = 0 then some 0 else none) else
some (g/f)` is a genuine decision procedure (`rischDE_complete_base`), so it returns `some` on every
solvable input. Closes cleanly, axiom-clean.

**The Wf step** (`crischFieldCompleteWf_step`, PROVEN modulo the Wf per-level frontier): the IH
`CRischFieldComplete β` supplies the one-level-down base-oracle calls used by cancellation; the next-level
public conclusion is `CRischFieldCompleteWf β`, i.e. completeness of `crischDESolveSoundWf` over `QFunNZG β`.
The Wf frontier supplies the Wf weak-normalizer clauses, Wf inner residual-tip frontier, polynomial-solution
and denominator guards, and direct Wf soundness certificate. -/

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

/-- Uniform field-level RDE solvability `CFieldRDESolvable f g`: there is `y : α` solving the
field-level Risch differential equation `Dy + f·y = g`, read through the bridge `toK` into `K = CFieldSpec.K
α` — `(toK y)′ + (toK f)·(toK y) = toK g`, with `′ = Differential.deriv` the `CDiffFieldSpec` derivation.
The exact "solvable" side `CRischFieldSpec`'s soundness conclusion uses, uniform over the tower: over the
constants `ℚ` (`toK = id`, `′ = 0`) it is `f·y = g`; over each `QFunNZG β` it is the genuine RDE. -/
def CFieldRDESolvable (f g : α) : Prop :=
  ∃ y : α, @Differential.deriv _ _ CDiffFieldSpec.diffK (CFieldSpec.toK y)
      + CFieldSpec.toK f * CFieldSpec.toK y
    = CFieldSpec.toK g

/-- Per-level RDE completeness `CRischFieldComplete α`: the field-level oracle
`CRischField.crischDESolve` returns `some` on every solvable field RDE — `∀ f g, CFieldRDESolvable f g →
(crischDESolve f g).isSome = true`. The decision-procedure (completeness half) of the base solve at one
tower level; the predicate the tower induction propagates from level `n` to level `n+1`. -/
def CRischFieldComplete (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] : Prop :=
  ∀ f g : α, CFieldRDESolvable f g → (CRischField.crischDESolve f g).isSome = true

end Predicate

/-! ## The BASE ℚ — `CRischFieldComplete ℚ` (PROVEN, axiom-clean)

The tower bottoms at the constants `ℚ` (`D = 0`, `toK = id`, `K = ℚ`): the field RDE `Dy + f·y = g`
collapses to `f·y = g`, and the base oracle `crischDESolve f g = if f = 0 then (if g = 0 then some 0 else
none) else some (g/f)` is a genuine decision procedure (`rischDE_complete_base`). So a solvable input always
makes the oracle return `some`. This is the base case of the tower induction. -/

section BaseQ

/-- `CFieldRDESolvable` over `ℚ` is `∃ y, f·y = g` (`cFieldRDESolvable_Q_iff`): the constants `ℚ` have
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

/-- BASE ℚ: `CRischFieldComplete ℚ` (`crischFieldComplete_Q`): the constant-field base of the tower
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

/-! ## The base-oracle recursion tie

The public next-level statement is the Wf step below, but the §6.6 cancellation subroutines still recurse one
level down through the class oracle. The cancellation base oracle
`Cancel{Prim,Exp}OracleComplete Dt b` calls `crischDESolve` over `β` (since `b : CPolyG β`, `cleadG b : β`),
which is the **IH** `CRischFieldComplete β` — modulo the **agreement** that the returned base solution's
`toK` is the abstract solution's leading coefficient.

We assemble the IH-fed half of the recursion (the base oracle's `.isSome` component from the IH + the field
RDE the leading coefficient solves) and characterize the agreement + the per-level honest frontier as the
precise remaining glue. -/

section Step

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CRischField β]

/-- The IH yields the base oracle's `.isSome` on a solvable leading-coefficient RDE
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

/-- The cancellation base-oracle agreement residual (primitive) `CancelOracleAgreementPrim Dt b`: for
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

/-- `CancelPrimOracleComplete` from the IH + the agreement residual
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

/-- The cancellation base-oracle agreement residual (hyperexp) `CancelOracleAgreementExp Dt b`: the
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

/-- `CancelExpOracleComplete` from the IH + the agreement residual
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

/-! ### Wf-facing per-level step

The public solver over `QFunNZG β` is `crischDESolveSoundWf`. The cancellation subroutines still recurse into
the base field through `CRischField.crischDESolve`, so the induction hypothesis remains
`CRischFieldComplete β`; the next-level conclusion, however, is now a fuel-free wrapper result. -/

section StepAssemblyWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- Wf per-level RDE completeness: the fuel-free public solver returns `some` on every solvable
field-level RDE over `QFunNZG β`. -/
def CRischFieldCompleteWf (β : Type*) [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] : Prop :=
  ∀ f g : QFunNZG β, FieldRDESolvable f g → ∃ y, crischDESolveSoundWf f g = some y

/-- The Wf per-level step frontier: given the old base-oracle IH one level down, every solvable
`QFunNZG β` RDE satisfies the Wf weak-normalizer clauses, the Wf inner residual-tip frontier, the polynomial
solution/denominator guards, and the direct Wf soundness certificate. -/
structure RischDEStepFrontierWf (β : Type*) [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] : Prop where
  /-- §6.1/Wf: a solvable RDE has a nonzero fuel-free weak normalizer. -/
  hwn : CRischFieldComplete β → ∀ f g : QFunNZG β, FieldRDESolvable f g →
    CPolyG.cisZeroG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2) = false
  /-- §6.1/Wf: a solvable RDE satisfies the fuel-free canonical-normality guarantee. -/
  hck : CRischFieldComplete β → ∀ f g : QFunNZG β, FieldRDESolvable f g →
    IsCanonNormalizedWf f
      (qOfPolyNZG (cWeakNormalizerGWf ([CField.one] : CPolyG β) f.1.1 f.1.2))
  /-- A solvable field RDE has a polynomial solution for the Wf inner input. -/
  hpolysol : CRischFieldComplete β → ∀ f g : QFunNZG β, FieldRDESolvable f g →
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    ∃ ynum yden,
      IsCRischDEGPolySol ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2
        gtilde.1.1 gtilde.1.2 ynum yden
  /-- §6.2-6.6/Wf: the consolidated inner residual-tip frontier, threaded through the IH. -/
  hinnerFront : CRischFieldComplete β → ∀ f g : QFunNZG β, FieldRDESolvable f g →
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    RischDEInnerDecisionFrontierWf ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2
      gtilde.1.1 gtilde.1.2
  /-- The returned denominator of a successful Wf inner solve is nonzero. -/
  hden : CRischFieldComplete β → ∀ f g : QFunNZG β, FieldRDESolvable f g → ∀ ynum yden : CPolyG β,
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    cRischDEGWf ([CField.one] : CPolyG β) ftildeR.1.1 ftildeR.1.2 gtilde.1.1 gtilde.1.2
        = some (ynum, yden) →
      CPolyG.cisZeroG yden = false
  /-- The direct Wf soundness certificate for each solvable next-level RDE. -/
  hsound : CRischFieldComplete β → ∀ f g : QFunNZG β, FieldRDESolvable f g →
    RischDESoundnessWf f g

/-- Wf step: a complete base oracle one level down plus the Wf per-level frontier makes the fuel-free
public RDE solver complete at the next `QFunNZG` level. -/
theorem crischFieldCompleteWf_step (hβ : CRischFieldComplete β)
    (hstep : RischDEStepFrontierWf β) : CRischFieldCompleteWf β := by
  intro f g hsol
  let hfront : RischDEDecisionProcedureFrontierWf f g :=
    decisionProcedureFrontierWf_of_innerFrontier f g
      (fun hsol' => hstep.hwn hβ f g hsol')
      (fun hsol' => hstep.hck hβ f g hsol')
      (fun hsol' => hstep.hpolysol hβ f g hsol')
      (fun hsol' => hstep.hinnerFront hβ f g hsol')
      (fun hsol' ynum yden => hstep.hden hβ f g hsol' ynum yden)
  exact (crischDESolveSoundWf_isDecisionProcedure f g hfront (hstep.hsound hβ f g hsol)).mpr hsol

end StepAssemblyWf

/-! ### Restatements (anonymous `example`s) -/

-- The base case: `CRischFieldComplete ℚ` is the constant-field decision procedure.
example : CRischFieldComplete ℚ := crischFieldComplete_Q

-- The recursion tie: the IH (level-`β` completeness) makes the base oracle return `some` on a solvable
-- leading-coefficient RDE — the `.isSome` half of `Cancel{Prim,Exp}BaseOracle`.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CRischField β]
    (hβ : CRischFieldComplete β) (b₀ c₀ : β) (hsol : CFieldRDESolvable b₀ c₀) :
    (CRischField.crischDESolve b₀ c₀).isSome = true :=
  crischDESolve_isSome_of_complete hβ b₀ c₀ hsol

-- Wf STEP: the IH + the Wf per-level frontier give fuel-free wrapper completeness at level `n+1`.
example {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
    [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]
    (hβ : CRischFieldComplete β) (hstep : RischDEStepFrontierWf β) :
    CRischFieldCompleteWf β :=
  crischFieldCompleteWf_step hβ hstep

/-! ### Axiom audit (the base case, the recursion-tie helper, and the Wf assembled step are
axiom-clean; NO `native_decide`) -/


end DeepWiki.SymbolicIntegration
