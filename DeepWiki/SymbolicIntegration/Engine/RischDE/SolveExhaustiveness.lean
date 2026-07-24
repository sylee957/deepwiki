import DeepWiki.SymbolicIntegration.Engine.RischDE.NormCompleteness
import DeepWiki.SymbolicIntegration.Engine.RischDE.DegreeBound
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural
import DeepWiki.SymbolicIntegration.Engine.RatFuncValuation

/-! # RDE inner-solve exhaustiveness (`hsolveWf`)

The assembled solve `cRischDE` succeeds iff its three stages (normal-denominator, SPDE, poly-RDE
dispatcher) each return `some`; `RischDESolveExhaustiveResidualWf` bundles the three stage-`some`
implications and yields the `hsolveWf` completeness clause, assembled into `RischDEInnerCompletenessWf`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-! ## Engine layer: `cRischDE.isSome` from stage `some`s -/

section EngineLayerWf

variable {α : Type*} [CField α] [CDiffField α] [CPolyGcd DensePoly α]
  [CPolySplitFactor DensePoly α] [CRischField α]

/-- The Wf stage `some`s force `cRischDE.isSome`. -/
theorem cRischDEG_isSome_of_stages (Dt : DensePoly α) (fnum fden gnum gden : DensePoly α)
    (a0 b0 c0 h0 bbar cbar : DensePoly α) (m : ℤ) (α' β v : DensePoly α)
    (hnorm : cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0))
    (hspde : cSPDE Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
        (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hpoly : cPolyRischDE Dt bbar cbar m = some v) :
    (cRischDE Dt fnum fden gnum gden).isSome = true := by
  rw [cRischDE, hnorm]
  simp only [hspde, hpoly, Option.isSome_some]

/-- The fuel-free assembled solve succeeds iff its three Wf stages succeed. -/
theorem cRischDEG_isSome_iff_stages (Dt : DensePoly α) (fnum fden gnum gden : DensePoly α) :
    (cRischDE Dt fnum fden gnum gden).isSome = true ↔
      ∃ (a0 b0 c0 h0 bbar cbar : DensePoly α) (m : ℤ) (α' β v : DensePoly α),
        cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0)
        ∧ cSPDE Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
            (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
              (cRdeSpecialDenominator Dt a0 b0 c0).2.1
              (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)
          = some (bbar, cbar, m, α', β)
        ∧ cPolyRischDE Dt bbar cbar m = some v := by
  constructor
  · intro h
    obtain ⟨⟨ynum, yden⟩, hy⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly, _, _⟩ :=
      DensePoly.cRischDEG_some_imp_stages Dt fnum fden gnum gden ynum yden hy
    exact ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly⟩
  · rintro ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly⟩
    exact cRischDEG_isSome_of_stages Dt fnum fden gnum gden a0 b0 c0 h0 bbar cbar m α' β v
      hnorm hspde hpoly

end EngineLayerWf

/-! ## The abstract non-cancellation solution predicate -/

section NoCancelPredicate

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- `IsNoCancelSolK Dt b c q`: `implicitDeriv (toPoly Dt) q + toPoly b · q = toPoly c` for
`q ∈ (CFieldSpec.K α)[X]` — the non-cancellation equation `Dq + b·q = c`. -/
def IsNoCancelSolK (Dt b c : DensePoly α) (q : (CFieldSpec.K α)[X]) : Prop :=
  Differential.implicitDeriv (toPoly Dt) q + toPoly b * q = toPoly c

end NoCancelPredicate

/-! ## The cancellation base-oracle hypotheses -/

section CancelPredicate

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α]

/-- `CancelPrimBaseOracle b c q`: the base oracle `crischDESolve (clead b) (clead c)` returns `some s`
with `toK s = q.leadingCoeff` (completeness plus leading-coefficient agreement). -/
def CancelPrimBaseOracle (b c : DensePoly α) (q : (CFieldSpec.K α)[X]) : Prop :=
  ∃ s : α, CRischField.crischDESolve (clead b) (clead c) = some s
    ∧ CFieldSpec.toK s = q.leadingCoeff

/-- `CancelPrimOracleComplete Dt b`: for every `c'` and degree-matched solution `q'`, the base oracle
finds its leading coefficient (`CancelPrimBaseOracle b c' q'`). -/
def CancelPrimOracleComplete (Dt b : DensePoly α) : Prop :=
  ∀ (c' : DensePoly α) (q' : (CFieldSpec.K α)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdeg c' → CancelPrimBaseOracle b c' q'

omit [CRischField α] in
/-- `CancelPrimNoCancel Dt b`: every nonzero solution `q'` of `D q' + b·q' = c'` is degree-matched
(`deg q' = deg c'`) — the regime where the engine's `m = deg c` search is exhaustive. -/
def CancelPrimNoCancel (Dt b : DensePoly α) : Prop :=
  ∀ (c' : DensePoly α) (q' : (CFieldSpec.K α)[X]),
    IsNoCancelSolK Dt b c' q' → q' ≠ 0 → (q'.natDegree : ℤ) = cdeg c'

/-- `expCoeff Dt c b = clead b + (deg c)·cExpEta Dt`: the shifted base-RDE coefficient for the
hyperexponential cancellation case. -/
def expCoeff (Dt : DensePoly α) (c b : DensePoly α) : α :=
  CCommRing.add (clead b) (CCommRing.mul (CField.natCast (cdeg c)) (cExpEta Dt))

/-- `CancelExpBaseOracle Dt b c q`: the base oracle `crischDESolve (expCoeff Dt c b) (clead c)` returns
`some s` with `toK s = q.leadingCoeff` (hyperexp analogue of `CancelPrimBaseOracle`). -/
def CancelExpBaseOracle (Dt : DensePoly α) (b c : DensePoly α) (q : (CFieldSpec.K α)[X]) : Prop :=
  ∃ s : α, CRischField.crischDESolve (expCoeff Dt c b) (clead c) = some s
    ∧ CFieldSpec.toK s = q.leadingCoeff

/-- `CancelExpOracleComplete Dt b`: for every `c'` and degree-matched solution `q'`, the base oracle
`crischDESolve (expCoeff Dt c' b) (clead c')` finds its leading coefficient (hyperexp analogue of
`CancelPrimOracleComplete`). -/
def CancelExpOracleComplete (Dt b : DensePoly α) : Prop :=
  ∀ (c' : DensePoly α) (q' : (CFieldSpec.K α)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdeg c' → CancelExpBaseOracle Dt b c' q'

end CancelPredicate


/-! ## Exhaustiveness residual

A solution forces the normal-denominator, SPDE, and poly-RDE dispatcher stages to succeed, yielding
the `RischDEInnerCompletenessWf.hsolve` field. -/

section ExhaustiveResidualWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CRischField α]

/-- The inner-solve exhaustiveness residual: the three stage-`some` implications. -/
structure RischDESolveExhaustiveResidualWf (Dt fnum fden gnum gden : DensePoly α) : Prop where
  /-- A polynomial solution makes the normal-denominator step return `some`. -/
  hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true
  /-- A solution makes the SPDE peel return `some`. -/
  hspde : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 : DensePoly α,
      cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      (cSPDE Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
          (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)).isSome = true
  /-- For the SPDE output, a solution makes the poly-RDE dispatcher return `some`. -/
  hpoly : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 bbar cbar : DensePoly α, ∀ m : ℤ, ∀ α' β : DensePoly α,
      cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      cSPDE Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
          (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) →
      (cPolyRischDE Dt bbar cbar m).isSome = true

/-- The Wf exhaustiveness residual produces the exact Wf `hsolve` clause. -/
theorem hsolveWf_of_exhaustiveResidualWf (Dt fnum fden gnum gden : DensePoly α)
    (hres : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRischDE Dt fnum fden gnum gden).isSome = true := by
  intro hsol
  obtain ⟨⟨a0, b0, c0, h0⟩, hnorm⟩ := Option.isSome_iff_exists.mp (hres.hnorm hsol)
  obtain ⟨⟨bbar, cbar, m, α', β⟩, hspde⟩ :=
    Option.isSome_iff_exists.mp (hres.hspde hsol a0 b0 c0 h0 hnorm)
  obtain ⟨v, hpoly⟩ :=
    Option.isSome_iff_exists.mp (hres.hpoly hsol a0 b0 c0 h0 bbar cbar m α' β hnorm hspde)
  exact cRischDEG_isSome_of_stages Dt fnum fden gnum gden
    a0 b0 c0 h0 bbar cbar m α' β v hnorm hspde hpoly

end ExhaustiveResidualWf

/-! ## `RischDEInnerCompletenessWf` from its three component residuals -/

section AssembleWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CRischField α]

/-- `RischDEInnerCompletenessWf` assembled from its three component residuals. -/
theorem rischDEInnerCompletenessWf_of_residuals (Dt fnum fden gnum gden : DensePoly α)
    (hnormRes : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden)
    (hboundRes : RdeBoundCancellationResidualWf Dt fnum fden gnum gden)
    (hsolveRes : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden where
  hnorm := hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hnormRes
  hbound := hboundWf_of_cancellationResidualWf Dt fnum fden gnum gden hboundRes
  hsolve := hsolveWf_of_exhaustiveResidualWf Dt fnum fden gnum gden hsolveRes

end AssembleWf

end DeepWiki.SymbolicIntegration
