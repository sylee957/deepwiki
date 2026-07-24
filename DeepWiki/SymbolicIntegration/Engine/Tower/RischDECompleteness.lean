import DeepWiki.SymbolicIntegration.Engine.RischDE.DecisionProcedure

/-! # Tower induction for RDE completeness

Propagates completeness of the field-level Risch DE oracle up the tower. `CRischFieldComplete α` says the
base oracle `crischDESolve` returns `some` on every solvable field RDE; the tower bottoms at
`crischFieldComplete_Q` over the constants `ℚ` and steps with `crischFieldCompleteWf_step`, which derives
next-level completeness `CRischFieldCompleteWf β` of the fuel-free solver from the per-level frontier. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

universe u v

/-! ## Field-level RDE predicates

`CFieldRDESolvable` and `CRischFieldComplete` live in `RischFieldSpec.lean`, alongside the
field-oracle soundness contract. This tower module supplies their induction through `DenseFrac`. -/

/-! ## The base case `CRischFieldComplete ℚ`

Over the constants `ℚ` (`D = 0`, `toK = id`) the field RDE collapses to `f·y = g`, and the base oracle
is a genuine decision procedure (`rischDE_complete_base`), so a solvable input makes it return `some`. -/

section BaseQ

/-- `CFieldRDESolvable` over `ℚ` collapses to `∃ y, f·y = g` (`toK = id`, zero derivation). -/
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

/-- `CRischFieldComplete ℚ`: over the constants `ℚ` a solvable field RDE makes the base oracle return
`some` (direct division `g/f`, or `0` when `f = g = 0`). -/
theorem crischFieldComplete_Q : CRischFieldComplete ℚ := by
  intro f g hsol
  rw [cFieldRDESolvable_Q_iff] at hsol
  obtain ⟨y, hy⟩ := (rischDE_complete_base f g).mp hsol
  rw [hy]; rfl

end BaseQ

/-! ## The base-oracle recursion tie

The cancellation subroutines recurse one level down through `crischDESolve` over `β`, which is the
induction hypothesis `CRischFieldComplete β`. This section assembles the IH-fed half of the recursion (the
base oracle's `.isSome`) and isolates the remaining agreement residual. -/

section Step

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CRischField β]

/-- The IH yields the base oracle's `.isSome` on a solvable leading-coefficient RDE: if
`CRischFieldComplete β` and `CFieldRDESolvable b₀ c₀`, then `(crischDESolve b₀ c₀).isSome = true`. -/
theorem crischDESolve_isSome_of_complete (hβ : CRischFieldComplete β) (b₀ c₀ : β)
    (hsol : CFieldRDESolvable b₀ c₀) :
    (CRischField.crischDESolve b₀ c₀).isSome = true :=
  hβ b₀ c₀ hsol

/-! ### The cancellation base-oracle agreement residual

The IH gives only the `.isSome` existence half of the cancellation base oracle; the remaining component is
the agreement `toK s = lc q'` between the returned base solution and the abstract solution's leading
coefficient. This residual bundles leading-coefficient solvability plus that agreement. -/

/-- The cancellation base-oracle agreement residual (primitive) `CancelOracleAgreementPrim Dt b`: for
every degree-matched abstract solution `q'` (`IsNoCancelSolK Dt b c' q'`, `deg q' = deg c'`), the base RDE
`Ds + (clead b)·s = clead c'` over `β` is solvable **and** any oracle solution agrees with `q'`'s leading
coefficient (`crischDESolve (clead b) (clead c') = some s → toK s = lc q'`). -/
def CancelOracleAgreementPrim (Dt b : DensePoly β) : Prop :=
  ∀ (c' : DensePoly β) (q' : (CFieldSpec.K β)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdeg c' →
      CFieldRDESolvable (clead b) (clead c') ∧
      (∀ s : β, CRischField.crischDESolve (clead b) (clead c') = some s →
        CFieldSpec.toK s = q'.leadingCoeff)

/-- `CancelPrimOracleComplete` from the IH plus the agreement residual: the level-`β` completeness
`CRischFieldComplete β` and the per-level residual `CancelOracleAgreementPrim Dt b` together give the
uniform primitive base-oracle completeness `CancelPrimOracleComplete Dt b`. -/
theorem cancelPrimOracleComplete_of_complete (Dt b : DensePoly β) (hβ : CRischFieldComplete β)
    (hagree : CancelOracleAgreementPrim Dt b) :
    CancelPrimOracleComplete Dt b := by
  intro c' q' hsol hdeg
  obtain ⟨hsolv, hag⟩ := hagree c' q' hsol hdeg
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hβ (clead b) (clead c') hsolv)
  exact ⟨s, hs, hag s hs⟩

/-- The cancellation base-oracle agreement residual (hyperexp) `CancelOracleAgreementExp Dt b`: the
hyperexponential analogue of `CancelOracleAgreementPrim`, threading the shift coefficient
`expCoeff Dt c' b = (clead b) + (deg c')·η`. For every degree-matched abstract solution `q'`, the base RDE
`Ds + (expCoeff Dt c' b)·s = clead c'` over `β` is solvable and any oracle solution agrees with `q'`'s
leading coefficient. -/
def CancelOracleAgreementExp (Dt b : DensePoly β) : Prop :=
  ∀ (c' : DensePoly β) (q' : (CFieldSpec.K β)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdeg c' →
      CFieldRDESolvable (expCoeff Dt c' b) (clead c') ∧
      (∀ s : β, CRischField.crischDESolve (expCoeff Dt c' b) (clead c') = some s →
        CFieldSpec.toK s = q'.leadingCoeff)

/-- `CancelExpOracleComplete` from the IH plus the hyperexp agreement residual
`CancelOracleAgreementExp Dt b`: the hyperexp analogue of `cancelPrimOracleComplete_of_complete`. -/
theorem cancelExpOracleComplete_of_complete (Dt b : DensePoly β) (hβ : CRischFieldComplete β)
    (hagree : CancelOracleAgreementExp Dt b) :
    CancelExpOracleComplete Dt b := by
  intro c' q' hsol hdeg
  obtain ⟨hsolv, hag⟩ := hagree c' q' hsol hdeg
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hβ (expCoeff Dt c' b) (clead c') hsolv)
  exact ⟨s, hs, hag s hs⟩

end Step

/-! ### The per-level step

The next-level solver over `DenseFrac β` is `crischDESolveSoundWf`; the induction hypothesis remains
`CRischFieldComplete β` (the cancellation subroutines recurse into `CRischField.crischDESolve` one level
down). -/

section StepAssemblyWf

variable {β : Type u} [CField β] [CFieldSpec.{u,v} β] [CDiffField β] [CDiffFieldSpec β]
  [CFieldDomain β DensePoly]
  [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CPolyResultant DensePoly]
  [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- Next-level RDE completeness `CRischFieldCompleteWf β`: the public solver returns `some` on every
solvable field-level RDE over `DenseFrac β`. -/
def CRischFieldCompleteWf (β : Type*) [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β DensePoly] [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β]
    [CPolyResultant DensePoly]
    [CRischField β] [Algebra ℚ (CFieldSpec.K β)] : Prop :=
  ∀ f g : DenseFrac β, FieldRDESolvable f g → ∃ y, crischDESolveSoundWf f g = some y

/-- The per-level step frontier `RischDEStepFrontierWf β`: given the base-oracle IH one level down, every
solvable `DenseFrac β` RDE satisfies the weak-normalizer clauses, the inner residual-tip frontier, the
polynomial solution/denominator guards, and the direct soundness certificate. -/
structure RischDEStepFrontierWf (β : Type*) [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β DensePoly] [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β]
    [CPolyResultant DensePoly] [CRischField β] [Algebra ℚ (CFieldSpec.K β)] : Prop where
  /-- A solvable RDE has a nonzero weak normalizer. -/
  hwn : CRischFieldComplete β → ∀ f g : DenseFrac β, FieldRDESolvable f g →
    DensePoly.cisZero
      (cWeakNormalizer ([CCommRing.one] : DensePoly β) (CFrac.num f) (CFrac.den f)) = false
  /-- A solvable RDE satisfies the canonical-normality guarantee. -/
  hck : CRischFieldComplete β → ∀ f g : DenseFrac β, FieldRDESolvable f g →
    IsCanonNormalized f
      (CFrac.ofPoly
        (cWeakNormalizer ([CCommRing.one] : DensePoly β) (CFrac.num f) (CFrac.den f)))
  /-- A solvable field RDE has a polynomial solution for the inner input. -/
  hpolysol : CRischFieldComplete β → ∀ f g : DenseFrac β, FieldRDESolvable f g →
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    ∃ ynum yden,
      IsCRischDEGPolySol ([CCommRing.one] : DensePoly β) (CFrac.num ftildeR)
        (CFrac.den ftildeR) (CFrac.num gtilde) (CFrac.den gtilde) ynum yden
  /-- The consolidated inner residual-tip frontier, threaded through the IH. -/
  hinnerFront : CRischFieldComplete β → ∀ f g : DenseFrac β, FieldRDESolvable f g →
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    RischDEInnerDecisionFrontierWf ([CCommRing.one] : DensePoly β) (CFrac.num ftildeR)
      (CFrac.den ftildeR) (CFrac.num gtilde) (CFrac.den gtilde)
  /-- The returned denominator of a successful inner solve is nonzero. -/
  hden : CRischFieldComplete β → ∀ f g : DenseFrac β, FieldRDESolvable f g → ∀ ynum yden : DensePoly β,
    let ftildeR := (rischDEInnerInputWf f g).1
    let gtilde := (rischDEInnerInputWf f g).2
    cRischDE ([CCommRing.one] : DensePoly β) (CFrac.num ftildeR) (CFrac.den ftildeR)
        (CFrac.num gtilde) (CFrac.den gtilde)
        = some (ynum, yden) →
      DensePoly.cisZero yden = false
  /-- The direct soundness certificate for each solvable next-level RDE. -/
  hsound : CRischFieldComplete β → ∀ f g : DenseFrac β, FieldRDESolvable f g →
    RischDESoundnessWf f g

/-- Step: a complete base oracle one level down plus the per-level frontier makes the public RDE solver
complete at the next `CFrac` level. -/
theorem crischFieldCompleteWf_step (hβ : CRischFieldComplete β)
    [LawfulCPolyGcd.{u,v} DensePoly β]
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

/-- `CRischFieldCompleteWf β` grounded directly on the per-input Risch-DE decision-procedure frontier: if
every `DenseFrac β` RDE carries the named completeness frontier `RischDEDecisionProcedureFrontierWf` and the
direct soundness certificate `RischDESoundnessWf`, then the public fuel-free solver returns `some` on every
solvable field-level RDE. Mirrors how `primitiveFrontierLrt_of_genuineData` grounds the primitive frontier:
the Wf-solver's completeness rests transparently on the honest Bronstein RDE frontier, with no
`CRischFieldComplete`/`CRischFieldCompleteWf` assumption. -/
theorem crischFieldCompleteWf_of_decisionFrontier
    [LawfulCPolyGcd.{u,v} DensePoly β]
    (hfront : ∀ f g : DenseFrac β, RischDEDecisionProcedureFrontierWf f g)
    (hsound : ∀ f g : DenseFrac β, RischDESoundnessWf f g) :
    CRischFieldCompleteWf β := fun f g hsol =>
  (crischDESolveSoundWf_isDecisionProcedure f g (hfront f g) (hsound f g)).mpr hsol

end StepAssemblyWf

/-! ### Whole-tower Wf completeness

The tower step at an arbitrary concrete depth `DenseFracTower n`: given field-RDE completeness at that
level (the fuel'd recursion hypothesis) and the honest per-level Bronstein frontier
`RischDEStepFrontierWf`, the public fuel-free solver is complete at that level. This packages the tower
induction at every depth, resting transparently on exactly the necessary conditions — the honest
whole-tower form (the frontier is genuine Bronstein-completeness content, correctly a hypothesis; it
cannot be discharged, and the normalization-free instance solver cannot be made complete without a
rebase onto this weak-normalizing solver). -/
theorem crischFieldCompleteWf_tower (n : ℕ)
    [CRischField (DenseFracTower n)] [CFracGcdCoreWf (DenseFracTower n)]
    [LawfulCPolyGcd DensePoly (DenseFracTower n)]
    (hn : CRischFieldComplete (DenseFracTower n))
    (hstep : RischDEStepFrontierWf (DenseFracTower n)) :
    CRischFieldCompleteWf (DenseFracTower n) :=
  crischFieldCompleteWf_step hn hstep

/-! ### Axiom audit

The base case, recursion-tie helper, the Wf assembled step, and the frontier-grounding
`crischFieldCompleteWf_of_decisionFrontier` are axiom-clean and do not rely on `native_decide`. -/

end DeepWiki.SymbolicIntegration
