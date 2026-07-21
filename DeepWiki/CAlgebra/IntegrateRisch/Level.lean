import DeepWiki.CAlgebra.IntegrateRisch.Results
import DeepWiki.CAlgebra.Integrate.DerivDataSpec

/-! # Risch level packs

`RischLevel` — one level of the Risch tower as a single record in the house
ops-with-contract pattern: the level data `(d, Dt)`, the integrator, and its data-level
sound/complete contracts. `RischOracles` — the sub-level services (limited integration,
the Risch differential equation) the *next* extension consumes, with their contracts.
`baseLevel` is `R(x)` with `d/dx`, integrated by the complete rational pipeline. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable (K : Type u) [Field K] [DecidableEq K] [DensePolyGcd K]

/-- **One Risch level**: the coefficient derivation `d`, the variable's prescribed
derivative `Dt` (so the level derivation is `DenseFrac.extendDeriv d Dt` on the carrier
`K(t) = DenseFrac K`), the integrator, and its data-level contracts — soundness on the
produced record's computable derivative, and record-shape completeness for `none`. -/
structure RischLevel where
  /-- The coefficient derivation. -/
  d : K → K
  /-- The prescribed derivative of the level variable. -/
  Dt : DensePoly K
  /-- `d` is a derivation. -/
  isDerivation : IsDerivation d
  /-- Full integration at the level: an antiderivative record, or `none`. -/
  integrate : DenseFrac K → Option (ResultRisch K d)
  /-- Produced records differentiate back to the integrand. -/
  integrate_sound : ∀ f res, integrate f = some res → res.deriv Dt = f
  /-- `none` only when no record-shaped antiderivative exists. -/
  integrate_complete : ∀ f, integrate f = none →
    ∀ res : ResultRisch K d, res.deriv Dt ≠ f

variable {K}

/-- **Sub-level services** consumed by the next tower extension, over the level
derivation `DenseFrac.extendDeriv d Dt`: limited integration (`f = Dv + ∑ cᵢ·wᵢ` with
constant `cᵢ`) and the Risch differential equation (`Dy + f·y = g`), with their
data-level sound/complete contracts. -/
structure RischOracles (d : K → K) (Dt : DensePoly K) where
  /-- Limited integration: a principal part and constant coefficients for the given
  logarithmic derivatives. -/
  limitedIntegrate : DenseFrac K → List (DenseFrac K) →
    Option (DenseFrac K × List (DenseFrac K))
  /-- The Risch differential equation `Dy + f·y = g`. -/
  rdeSolve : DenseFrac K → DenseFrac K → Option (DenseFrac K)
  /-- Produced limited integrals decompose the integrand with constant coefficients. -/
  limitedIntegrate_sound : ∀ (f : DenseFrac K) (ws : List (DenseFrac K))
      (v : DenseFrac K) (cs : List (DenseFrac K)), limitedIntegrate f ws = some (v, cs) →
    cs.length = ws.length
      ∧ (∀ c ∈ cs, DenseFrac.extendDeriv d Dt c = 0)
      ∧ DenseFrac.extendDeriv d Dt v
          + ((cs.zip ws).map (fun p => p.1 * p.2)).sum = f
  /-- `none` only when no such decomposition exists. -/
  limitedIntegrate_complete : ∀ f ws, limitedIntegrate f ws = none →
    ∀ (v : DenseFrac K) (cs : List (DenseFrac K)), cs.length = ws.length →
      (∀ c ∈ cs, DenseFrac.extendDeriv d Dt c = 0) →
      DenseFrac.extendDeriv d Dt v
        + ((cs.zip ws).map (fun p => p.1 * p.2)).sum ≠ f
  /-- Produced solutions satisfy the differential equation. -/
  rdeSolve_sound : ∀ f g y, rdeSolve f g = some y →
    DenseFrac.extendDeriv d Dt y + f * y = g
  /-- `none` only when the equation has no solution. -/
  rdeSolve_complete : ∀ f g, rdeSolve f g = none →
    ∀ y, DenseFrac.extendDeriv d Dt y + f * y ≠ g

section Base

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]
  [DensePolySquarefree R] [IsAlgClosed R]

/-- **The base level** `R(x)` with `d/dx`: coefficient derivation `0`, `Dt = 1`,
integrated by the complete rational pipeline — soundness is `ratIntegrate_sound`, and
completeness is vacuous because rational integration never fails. -/
def baseLevel : RischLevel R where
  d := fun _ => 0
  Dt := 1
  isDerivation := isDerivation_zero
  integrate := fun f => some (ResultRisch.ofRatIntegral (ratIntegrate f))
  integrate_sound := fun f res h => by
    obtain rfl := Option.some.inj h
    rw [ResultRisch.ofRatIntegral_deriv, ratIntegrate_sound]
  integrate_complete := fun _ h => absurd h (Option.some_ne_none _)

end Base

end DensePoly

end DeepWiki.CAlgebra
