import DeepWiki.SymbolicIntegration.Engine.Tower.LrtDepth

/-! # Grounding the recursive LRT solver — the honest end state of the re-base

`Tower.LrtDepth` packages the dictionary-dependent carriers and proves the recursive soundness and
domain-relative completeness step at every depth. This file specializes that construction to `DenseFrac ℚ`
as a small concrete grounding theorem. The recursive construction depends on exactly two **honest** frontiers
per level, and no others:

* `PrimitiveFrontierLrt` — the reduced-part soundness. Closed (`hreducedLrt_of_genuineAll`) to the bundled
  genuine data `LrtReducedGenuineData` — Bronstein's *necessary* residue/normality conditions, which a
  properly-built tower satisfies but which are not derivable from the computable data. This **replaced** the
  rational `PrimitiveFrontier`, whose `IsIntegralResult` was not dischargeable at all (it forces the reduced
  denominator to split over `K`).
* selected polynomial gcd, split-factor, and squarefree capabilities, plus `CRischField`, at the tower
  coefficient carrier. The concrete `CFracGcdCoreWf` implementation and its PRS associatedness proof are
  needed only by the separate bridge that constructs `PrimitiveFrontierLrt` from genuine residue data.

So "no dangling frontier" is achieved in the honest sense: every remaining hypothesis is a **named genuine
mathematical condition**, not an opaque assumed lemma. Full recursive completeness additionally requires
coverage of the explicit limited-integration domains; `lrtTowerStep_succeeds_iff_integrable` deliberately does
not hide that requirement. See `docs/recursive-lrt-typeclass.md`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-- **★ The re-based recursive LRT solver is sound on the concrete ℚ(x)-tower, from the honest frontiers alone.**
At carrier `DenseFrac ℚ` (so `a/d ∈ (DenseFrac ℚ)(t)`, a genuine two-level tower), a successful run of the
assembled integrator `CRischLevelLrt.integrate` is a true `∀E` antiderivative — depending on the two
honest reduced frontiers (`PrimitiveFrontierLrt` at the base `ℚ` and at this level) and selected tower-level
polynomial and field capabilities. No concrete fraction-gcd implementation, rational-residue restriction, or
undischargeable `PrimitiveFrontier` appears in the solver theorem. -/
theorem lrtSolver_sound_on_tower [PrimitiveFrontierLrt ℚ]
    [CRischField (DenseFrac ℚ)] [CPolyGcd DensePoly (DenseFrac ℚ)]
    [CPolySplitFactor DensePoly (DenseFrac ℚ)] [LawfulCPolySplitFactor DensePoly (DenseFrac ℚ)]
    [CPolySquarefree DensePoly (DenseFrac ℚ)]
    [PrimitiveFrontierLrt (DenseFrac ℚ)]
    (Dt a d : DensePoly (DenseFrac ℚ)) (res : LrtResult (DenseFrac ℚ))
    (h : (inferInstance : CRischLevelLrt (DenseFrac ℚ)).integrate Dt a d = some res) :
    IsIntegralResultLrt Dt a d res :=
  (inferInstance : CRischLevelLrt (DenseFrac ℚ)).soundFormalLrt Dt a d res h

/-- On the explicit decomposition domain, the concrete recursive tower succeeds exactly when integrable. -/
theorem lrtSolver_succeeds_iff_integrable_on_tower [PrimitiveFrontierLrt ℚ]
    [CRischField (DenseFrac ℚ)] [CPolyGcd DensePoly (DenseFrac ℚ)]
    [CPolySplitFactor DensePoly (DenseFrac ℚ)] [LawfulCPolySplitFactor DensePoly (DenseFrac ℚ)]
    [CPolySquarefree DensePoly (DenseFrac ℚ)] [PrimitiveFrontierLrt (DenseFrac ℚ)]
    (Dt a d : DensePoly (DenseFrac ℚ))
    (hdomain : primitiveRischLevelLrtDomain
      (inferInstance : CRischLevelLrt (DenseFrac ℚ)) Dt a d)
    (hd : toPoly d ≠ 0) :
    IsElementaryIntegrableLrt Dt a d ↔
      ∃ res, (inferInstance : CRischLevelLrt (DenseFrac ℚ)).integrate Dt a d = some res :=
  rischLevelLrt_succeeds_iff_integrable
    (inferInstance : CRischLevelLrt (DenseFrac ℚ))
    (primitiveRischLevelLrtDomain (inferInstance : CRischLevelLrt (DenseFrac ℚ)))
    Dt a d hdomain hd

/-- The concrete `DenseFrac ℚ` primitive monomial case is complete on the checked recursive domains. -/
theorem completePrimitiveMonomialCase_on_tower [PrimitiveFrontierLrt ℚ] :
    CompleteCLrtMonomialCase (towerPrimitiveCaseLrt (β := ℚ))
      (towerPrimitiveRecursiveSpecialDomainLrt
        (towerLimitedCoefficientDomain DensePoly.CheckedLimitedIntegrateSingleBaseDomain)) := by
  exact completeTowerPrimitiveCaseLrt
    (rationalLrtAcceptanceDomain (inferInstance : CRischLevelLrt ℚ))
    DensePoly.CheckedLimitedIntegrateSingleBaseDomain

/-- The selected tower operation and its soundness contract resolve together. -/
example [PrimitiveFrontierLrt ℚ]
    [CRischField (DenseFrac ℚ)] [CPolyGcd DensePoly (DenseFrac ℚ)]
    [CPolySplitFactor DensePoly (DenseFrac ℚ)] [LawfulCPolySplitFactor DensePoly (DenseFrac ℚ)]
    [CPolySquarefree DensePoly (DenseFrac ℚ)] [PrimitiveFrontierLrt (DenseFrac ℚ)] :
    ∃ C : CRischLevelLrt (DenseFrac ℚ), LawfulCRischLevelLrt C :=
  ⟨inferInstance, inferInstance⟩

end DeepWiki.SymbolicIntegration
