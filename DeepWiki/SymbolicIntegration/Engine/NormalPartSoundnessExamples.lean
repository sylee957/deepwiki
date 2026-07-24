import DeepWiki.SymbolicIntegration.Engine.NormalPartSoundness

/-! # Specialized normal-part soundness

Level-1 specialization of the normal-part soundness API.
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-! ### The deliverables at the level-1 carrier `α = DenseFrac ℚ = ℚ(x)` -/

/-- The engine carrier `CFieldSpec.K (DenseFrac ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
`DenseFrac ℚ` deliverables synthesize the **same** `Algebra ℚ` the bridge `towerFractionFieldDeriv` uses. -/
noncomputable local instance normalPartSoundnessExamplesAlgebraRatKCFracG :
    Algebra ℚ (CFieldSpec.K (DenseFrac ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- The Hermite half over `ℚ(x)(t)`: the master Hermite telescoping `D(g) + h = a/d` (seed
`([CCommRing.zero], [CCommRing.one])`) at the carrier `α = DenseFrac ℚ`, over `RatFunc ℚ`. -/
theorem cHermiteReduceTowerG_telescope_seed_qfunNZG (Dt : DensePoly (DenseFrac ℚ))
    (L₀ : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ))
    (rest glocs : List (DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)))
    (hmem : ∀ g ∈ glocs, toPoly g.2 ≠ 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDeriv Dt (am (DenseFrac ℚ) (toPoly g.1) / am (DenseFrac ℚ) (toPoly g.2))
          = am (DenseFrac ℚ) (toPoly (Prod.fst p).1) / am (DenseFrac ℚ) (toPoly (Prod.fst p).2)
            - am (DenseFrac ℚ) (toPoly (Prod.snd p).1) / am (DenseFrac ℚ) (toPoly (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDeriv Dt
        (am (DenseFrac ℚ) (toPoly (glocs.foldl
            (fun (gAcc : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) gloc =>
              (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
            (([CCommRing.zero] : DensePoly (DenseFrac ℚ)), ([CCommRing.one] : DensePoly (DenseFrac ℚ)))).1)
          / am (DenseFrac ℚ) (toPoly (glocs.foldl
            (fun (gAcc : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) gloc =>
              (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
            (([CCommRing.zero] : DensePoly (DenseFrac ℚ)), ([CCommRing.one] : DensePoly (DenseFrac ℚ)))).2))
        + am (DenseFrac ℚ) (toPoly (rest.getLastD L₀).1)
          / am (DenseFrac ℚ) (toPoly (rest.getLastD L₀).2)
      = am (DenseFrac ℚ) (toPoly L₀.1) / am (DenseFrac ℚ) (toPoly L₀.2) :=
  cHermiteReduceTowerG_telescope_seed Dt L₀ rest glocs hmem hstep

end DeepWiki.SymbolicIntegration
