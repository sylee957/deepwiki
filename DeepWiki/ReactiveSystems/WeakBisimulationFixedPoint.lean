import DeepWiki.ReactiveSystems.BisimulationWeak
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteLattice.Basic

/-! # Observational equivalence as a greatest fixed point
The weak analogue of `bisimFunctional`/`bisimilar_eq_gfp`: a monotone functional
`G` on the lattice of relations whose post-fixed points are exactly the weak
bisimulations, with weak bisimilarity `≈` its greatest fixed point. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*} (L : LTS Proc Act) (tau : Act)

/-- The *weak* bisimulation functional `G`: `G R` relates `p, q` when each concrete
move of one is answered by a *weak* move of the other into `R`. Monotone in `R`
(`R` occurs only positively). -/
def weakBisimFunctional : (Proc → Proc → Prop) →o (Proc → Proc → Prop) where
  toFun R := fun p q =>
    (∀ a p', L.step p a p' → ∃ q', WeakStep L tau q a q' ∧ R p' q') ∧
    (∀ a q', L.step q a q' → ∃ p', WeakStep L tau p a p' ∧ R p' q')
  monotone' R S hRS := by
    rintro p q ⟨h1, h2⟩
    refine ⟨fun a p' hp => ?_, fun a q' hq => ?_⟩
    · obtain ⟨q', hq', hr⟩ := h1 a p' hp; exact ⟨q', hq', hRS _ _ hr⟩
    · obtain ⟨p', hp', hr⟩ := h2 a q' hq; exact ⟨p', hp', hRS _ _ hr⟩

variable {L tau}

/-- A relation is a weak bisimulation exactly when it
is a post-fixed point of `G`: `R` is a weak bisimulation iff `R ≤ G R`. -/
theorem isWeakBisimulation_iff_le_weakBisimFunctional (R : Proc → Proc → Prop) :
    IsWeakBisimulation L tau R ↔ R ≤ weakBisimFunctional L tau R := Iff.rfl

/-- Weak bisimilarity (observational equivalence) `≈`
is the greatest fixed point of the weak bisimulation functional `G`. -/
theorem weaklyBisimilar_eq_gfp :
    WeaklyBisimilar L tau = (weakBisimFunctional L tau).gfp := by
  apply le_antisymm
  · exact (weakBisimFunctional L tau).le_gfp
      ((isWeakBisimulation_iff_le_weakBisimFunctional _).mp isWeakBisimulation_weaklyBisimilar)
  · have hg : IsWeakBisimulation L tau (weakBisimFunctional L tau).gfp :=
      (isWeakBisimulation_iff_le_weakBisimFunctional _).mpr
        ((weakBisimFunctional L tau).gfp_le_map le_rfl)
    exact hg.le_weaklyBisimilar

end LTS

end DeepWiki.ReactiveSystems
