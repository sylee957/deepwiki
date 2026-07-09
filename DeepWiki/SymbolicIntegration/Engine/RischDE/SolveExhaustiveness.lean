import DeepWiki.SymbolicIntegration.Engine.RischDE.NormCompleteness
import DeepWiki.SymbolicIntegration.Engine.RischDE.DegreeBound
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural
import DeepWiki.SymbolicIntegration.Engine.RatFuncValuation

/-! # RDE inner-solve exhaustiveness (`hsolveWf`)

The assembled solve `cRischDEG` succeeds iff its three stages (normal-denominator, SPDE, poly-RDE
dispatcher) each return `some`; `RischDESolveExhaustiveResidualWf` bundles the three stage-`some`
implications and yields the `hsolveWf` completeness clause, assembled into `RischDEInnerCompletenessWf`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG

/-! ## Engine layer: `cRischDEG.isSome` from stage `some`s -/

section EngineLayerWf

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-- The Wf stage `some`s force `cRischDEG.isSome`. -/
theorem cRischDEG_isSome_of_stages (Dt : CPoly α) (fnum fden gnum gden : CPoly α)
    (a0 b0 c0 h0 bbar cbar : CPoly α) (m : ℤ) (α' β v : CPoly α)
    (hnorm : cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0))
    (hspde : cSPDEG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hpoly : cPolyRischDEG Dt bbar cbar m = some v) :
    (cRischDEG Dt fnum fden gnum gden).isSome = true := by
  rw [cRischDEG, hnorm]
  simp only [hspde, hpoly, Option.isSome_some]

/-- The fuel-free assembled solve succeeds iff its three Wf stages succeed. -/
theorem cRischDEG_isSome_iff_stages (Dt : CPoly α) (fnum fden gnum gden : CPoly α) :
    (cRischDEG Dt fnum fden gnum gden).isSome = true ↔
      ∃ (a0 b0 c0 h0 bbar cbar : CPoly α) (m : ℤ) (α' β v : CPoly α),
        cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0)
        ∧ cSPDEG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
            (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
              (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
              (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)
          = some (bbar, cbar, m, α', β)
        ∧ cPolyRischDEG Dt bbar cbar m = some v := by
  constructor
  · intro h
    obtain ⟨⟨ynum, yden⟩, hy⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly, _, _⟩ :=
      cRischDEG_some_imp_stages_structural Dt fnum fden gnum gden ynum yden hy
    exact ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly⟩
  · rintro ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly⟩
    exact cRischDEG_isSome_of_stages Dt fnum fden gnum gden a0 b0 c0 h0 bbar cbar m α' β v
      hnorm hspde hpoly

end EngineLayerWf

/-! ## The abstract non-cancellation solution predicate -/

section NoCancelPredicate

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- `IsNoCancelSolK Dt b c q`: `implicitDeriv (toPolyG Dt) q + toPolyG b · q = toPolyG c` for
`q ∈ (CFieldSpec.K α)[X]` — the non-cancellation equation `Dq + b·q = c`. -/
def IsNoCancelSolK (Dt b c : CPoly α) (q : (CFieldSpec.K α)[X]) : Prop :=
  Differential.implicitDeriv (toPolyG Dt) q + toPolyG b * q = toPolyG c

end NoCancelPredicate

/-! ## The cancellation base-oracle hypotheses -/

section CancelPredicate

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α]

/-- `CancelPrimBaseOracle b c q`: the base oracle `crischDESolve (cleadG b) (cleadG c)` returns `some s`
with `toK s = q.leadingCoeff` (completeness plus leading-coefficient agreement). -/
def CancelPrimBaseOracle (b c : CPoly α) (q : (CFieldSpec.K α)[X]) : Prop :=
  ∃ s : α, CRischField.crischDESolve (cleadG b) (cleadG c) = some s
    ∧ CFieldSpec.toK s = q.leadingCoeff

/-- `CancelPrimOracleComplete Dt b`: for every `c'` and degree-matched solution `q'`, the base oracle
finds its leading coefficient (`CancelPrimBaseOracle b c' q'`). -/
def CancelPrimOracleComplete (Dt b : CPoly α) : Prop :=
  ∀ (c' : CPoly α) (q' : (CFieldSpec.K α)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdegG c' → CancelPrimBaseOracle b c' q'

omit [CRischField α] in
/-- `CancelPrimNoCancel Dt b`: every nonzero solution `q'` of `D q' + b·q' = c'` is degree-matched
(`deg q' = deg c'`) — the regime where the engine's `m = deg c` search is exhaustive. -/
def CancelPrimNoCancel (Dt b : CPoly α) : Prop :=
  ∀ (c' : CPoly α) (q' : (CFieldSpec.K α)[X]),
    IsNoCancelSolK Dt b c' q' → q' ≠ 0 → (q'.natDegree : ℤ) = cdegG c'

/-- `expCoeff Dt c b = cleadG b + (deg c)·cExpEtaG Dt`: the shifted base-RDE coefficient for the
hyperexponential cancellation case. -/
def expCoeff (Dt : CPoly α) (c b : CPoly α) : α :=
  CField.add (cleadG b) (CField.mul (cnatCastG (cdegG c)) (cExpEtaG Dt))

/-- `CancelExpBaseOracle Dt b c q`: the base oracle `crischDESolve (expCoeff Dt c b) (cleadG c)` returns
`some s` with `toK s = q.leadingCoeff` (hyperexp analogue of `CancelPrimBaseOracle`). -/
def CancelExpBaseOracle (Dt : CPoly α) (b c : CPoly α) (q : (CFieldSpec.K α)[X]) : Prop :=
  ∃ s : α, CRischField.crischDESolve (expCoeff Dt c b) (cleadG c) = some s
    ∧ CFieldSpec.toK s = q.leadingCoeff

/-- `CancelExpOracleComplete Dt b`: for every `c'` and degree-matched solution `q'`, the base oracle
`crischDESolve (expCoeff Dt c' b) (cleadG c')` finds its leading coefficient (hyperexp analogue of
`CancelPrimOracleComplete`). -/
def CancelExpOracleComplete (Dt b : CPoly α) : Prop :=
  ∀ (c' : CPoly α) (q' : (CFieldSpec.K α)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdegG c' → CancelExpBaseOracle Dt b c' q'

end CancelPredicate


/-! ## Exhaustiveness residual

A solution forces the normal-denominator, SPDE, and poly-RDE dispatcher stages to succeed, yielding
the `RischDEInnerCompletenessWf.hsolve` field. -/

section ExhaustiveResidualWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- The inner-solve exhaustiveness residual: the three stage-`some` implications. -/
structure RischDESolveExhaustiveResidualWf (Dt fnum fden gnum gden : CPoly α) : Prop where
  /-- A polynomial solution makes the normal-denominator step return `some`. -/
  hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRdeNormalDenominatorG Dt fnum fden gnum gden).isSome = true
  /-- A solution makes the SPDE peel return `some`. -/
  hspde : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 : CPoly α,
      cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      (cSPDEG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)).isSome = true
  /-- For the SPDE output, a solution makes the poly-RDE dispatcher return `some`. -/
  hpoly : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 bbar cbar : CPoly α, ∀ m : ℤ, ∀ α' β : CPoly α,
      cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      cSPDEG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) →
      (cPolyRischDEG Dt bbar cbar m).isSome = true

/-- The Wf exhaustiveness residual produces the exact Wf `hsolve` clause. -/
theorem hsolveWf_of_exhaustiveResidualWf (Dt fnum fden gnum gden : CPoly α)
    (hres : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRischDEG Dt fnum fden gnum gden).isSome = true := by
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

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- `RischDEInnerCompletenessWf` assembled from its three component residuals. -/
theorem rischDEInnerCompletenessWf_of_residuals (Dt fnum fden gnum gden : CPoly α)
    (hnormRes : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden)
    (hboundRes : RdeBoundCancellationResidualWf Dt fnum fden gnum gden)
    (hsolveRes : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden where
  hnorm := hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hnormRes
  hbound := hboundWf_of_cancellationResidualWf Dt fnum fden gnum gden hboundRes
  hsolve := hsolveWf_of_exhaustiveResidualWf Dt fnum fden gnum gden hsolveRes

end AssembleWf

/-! ### Restatement against `RischDEInnerCompletenessWf` (anonymous `example`) -/

-- The Wf solve residual fits directly into the Wf inner-completeness assembly.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
    [CRischField α] (Dt fnum fden gnum gden : CPoly α)
    (hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorG Dt fnum fden gnum gden).isSome = true)
    (hbound : ∀ a0 b0 c0 h0 : CPoly α,
      cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : CPoly α,
        IsReducedRdeSol Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 q →
        cdegG q ≤ cRdeBoundDegreeG Dt
          (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1)
    (hres : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden :=
  { hnorm := hnorm
    hbound := hbound
    hsolve := hsolveWf_of_exhaustiveResidualWf Dt fnum fden gnum gden hres }

end DeepWiki.SymbolicIntegration
