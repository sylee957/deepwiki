import DeepWiki.SymbolicIntegration.Engine.DifferentialOneLevel

/-! # Presentation-indexed compositional transcendental towers

The legacy tower result fixes constants through the global `[CDiffField]` derivative.  This module
instead indexes every level contract by a `DifferentialTowerPresentation`, so primitive,
exponential, and tangent extensions retain their selected derivative throughout finite-tower
soundness and relative-completeness recursion.
-/

namespace DeepWiki.SymbolicIntegration

/-- The explicit differential context selected by a finite tower presentation at one depth. -/
noncomputable def DifferentialTowerPresentation.context
    (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N) :
    MonomialDifferentialContext (P := DensePoly) (DenseFracTower n) :=
  MonomialDifferentialContext.ofTowerPresentation T n hn

/-- A genuine one-level result interpreted with the derivative selected at its tower depth. -/
def IsPresentationIntegralResult (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : IntegralResult (DenseFracTower n)) : Prop :=
  IsGenuineDifferentialOneLevelResult (T.context n hn) input.toOneLevelInput result

/-- A certified presentation-indexed integration level at one finite tower depth. -/
structure DifferentialTranscendentalLevel (T : DifferentialTowerPresentation N)
    (n : ℕ) (hn : n ≤ N) where
  /-- Semantic integrability predicate selected for this depth. -/
  Integrable : RischStageInput DensePoly (DenseFracTower n) → Prop
  /-- Executable level with its selected-differential remainder invariant. -/
  stage : RemainderIntegrationStage
    (RischStageInput DensePoly (DenseFracTower n)) (IntegralResult (DenseFracTower n)) (Unit × Unit)
    Integrable (fun input result _ => IsPresentationIntegralResult T n hn input result)

namespace DifferentialTranscendentalLevel

/-- Build a presentation-indexed level from any stage already certified in that presentation's context. -/
def ofStage (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N)
    (Integrable : RischStageInput DensePoly (DenseFracTower n) → Prop)
    (stage : RemainderIntegrationStage
      (RischStageInput DensePoly (DenseFracTower n)) (IntegralResult (DenseFracTower n)) (Unit × Unit)
      Integrable (fun input result _ => IsPresentationIntegralResult T n hn input result)) :
    DifferentialTranscendentalLevel T n hn :=
  ⟨Integrable, stage⟩

/-- Every accepted presentation-indexed level result satisfies its selected derivative invariant. -/
theorem sound (L : DifferentialTranscendentalLevel T n hn) (fuel : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : RemainderResult (IntegralResult (DenseFracTower n)) (Unit × Unit))
    (hdomain : L.stage.stage.domain input) (hrun : L.stage.stage.run fuel input = some result) :
    IsPresentationIntegralResult T n hn input result.output :=
  L.stage.sound fuel input result hdomain hrun

/-- Every integrable in-domain presentation input eventually returns a certified result. -/
theorem complete (L : DifferentialTranscendentalLevel T n hn)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : L.stage.stage.domain input) (hintegrable : L.Integrable input) :
    ∃ fuel result, L.stage.stage.run fuel input = some result :=
  L.stage.complete input hdomain hintegrable

end DifferentialTranscendentalLevel

/-- A finite presentation-indexed tower builds every successor from the complete lower level. -/
structure DifferentialTranscendentalTowerScheme (T : DifferentialTowerPresentation N) where
  /-- Certified base level. -/
  base : DifferentialTranscendentalLevel T 0 (Nat.zero_le N)
  /-- Construct a successor level from the preceding certified level. -/
  step : ∀ n (hn : n + 1 ≤ N),
    DifferentialTranscendentalLevel T n (Nat.le_trans (Nat.le_succ n) hn) →
      DifferentialTranscendentalLevel T (n + 1) hn

namespace DifferentialTranscendentalTowerScheme

/-- The presentation-indexed level selected recursively at a finite tower depth. -/
noncomputable def level {N : ℕ} {T : DifferentialTowerPresentation N}
    (S : DifferentialTranscendentalTowerScheme (N := N) T) :
    ∀ n (hn : n ≤ N), DifferentialTranscendentalLevel (N := N) T n hn
  | 0, _ => S.base
  | n + 1, hn => S.step n hn (S.level n (Nat.le_trans (Nat.le_succ n) hn))

/-- Finite-tower soundness for the selected presentation derivative at every depth. -/
theorem stage_sound {N : ℕ} {T : DifferentialTowerPresentation N}
    (S : DifferentialTranscendentalTowerScheme (N := N) T)
    (n : ℕ) (hn : n ≤ N) (fuel : ℕ)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (result : RemainderResult (IntegralResult (DenseFracTower n)) (Unit × Unit))
    (hdomain : (S.level n hn).stage.stage.domain input)
    (hrun : (S.level n hn).stage.stage.run fuel input = some result) :
    IsPresentationIntegralResult T n hn input result.output :=
  (S.level n hn).sound fuel input result hdomain hrun

/-- Finite-tower relative completeness for the selected presentation derivative at every depth. -/
theorem stage_complete {N : ℕ} {T : DifferentialTowerPresentation N}
    (S : DifferentialTranscendentalTowerScheme (N := N) T)
    (n : ℕ) (hn : n ≤ N)
    (input : RischStageInput DensePoly (DenseFracTower n))
    (hdomain : (S.level n hn).stage.stage.domain input)
    (hintegrable : (S.level n hn).Integrable input) :
    ∃ fuel result, (S.level n hn).stage.stage.run fuel input = some result :=
  (S.level n hn).complete input hdomain hintegrable

end DifferentialTranscendentalTowerScheme

/-- The selected context for a primitive one-step presentation. -/
noncomputable abbrev primitiveOneStepContext :=
  DifferentialTowerPresentation.primitiveOneStep.context 1 (Nat.le_refl 1)

/-- The selected context for an exponential one-step presentation. -/
noncomputable abbrev exponentialOneStepContext :=
  DifferentialTowerPresentation.exponentialOneStep.context 1 (Nat.le_refl 1)

/-- The selected context for a tangent one-step presentation. -/
noncomputable abbrev tangentOneStepContext :=
  DifferentialTowerPresentation.tangentOneStep.context 1 (Nat.le_refl 1)

end DeepWiki.SymbolicIntegration
