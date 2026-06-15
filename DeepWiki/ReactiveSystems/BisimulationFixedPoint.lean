import DeepWiki.ReactiveSystems.Bisimulation
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteLattice.Basic

/-! # Bisimulation as a fixed point
The relations over the states of an LTS form a complete lattice, on which the
bisimulation functional `F` is monotone. A relation is a strong bisimulation
exactly when it is a post-fixed point `R ≤ F R`, and strong bisimilarity is the
greatest fixed point of `F` — the fixed-point view of Tarski's theorem applied
to behavioural equivalence. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*} (L : LTS Proc Act)

/-- The bisimulation functional `F` on the complete lattice of relations:
`F R` relates `p, q` when each `a`-move of one is answered by an `a`-move of the
other into `R`. Monotone in `R`. -/
def bisimFunctional : (Proc → Proc → Prop) →o (Proc → Proc → Prop) where
  toFun R := fun p q =>
    (∀ a p', L.step p a p' → ∃ q', L.step q a q' ∧ R p' q') ∧
    (∀ a q', L.step q a q' → ∃ p', L.step p a p' ∧ R p' q')
  monotone' R S hRS := by
    rintro p q ⟨h1, h2⟩
    refine ⟨fun a p' hp => ?_, fun a q' hq => ?_⟩
    · obtain ⟨q', hq', hr⟩ := h1 a p' hp; exact ⟨q', hq', hRS _ _ hr⟩
    · obtain ⟨p', hp', hr⟩ := h2 a q' hq; exact ⟨p', hp', hRS _ _ hr⟩

variable {L}

/-- A relation is a strong bisimulation exactly when it is a post-fixed point of
the bisimulation functional: `R` is a bisimulation iff `R ≤ F R`. -/
theorem isBisimulation_iff_le_bisimFunctional (R : Proc → Proc → Prop) :
    IsBisimulation L R ↔ R ≤ bisimFunctional L R := Iff.rfl

/-- Strong bisimilarity is the greatest fixed point of the bisimulation
functional (Tarski's fixed-point view of `~`). -/
theorem bisimilar_eq_gfp : Bisimilar L = (bisimFunctional L).gfp := by
  apply le_antisymm
  · exact (bisimFunctional L).le_gfp
      ((isBisimulation_iff_le_bisimFunctional _).mp isBisimulation_bisimilar)
  · have hg : IsBisimulation L (bisimFunctional L).gfp :=
      (isBisimulation_iff_le_bisimFunctional _).mpr ((bisimFunctional L).gfp_le_map le_rfl)
    exact hg.le_bisimilar

end LTS

end DeepWiki.ReactiveSystems
