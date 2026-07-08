import DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial.Core

/-! # Unit intersection for normal and special elements

Facts identifying the elements that are both normal and special.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- An element that is both normal and special is a unit. -/
theorem isUnit_of_isNormal_of_isSpecial {R : Type*} [CommRing R] [Differential R] {p : R}
    (hn : IsNormal p) (hs : IsSpecial p) : IsUnit p := by
  obtain ⟨w, hw⟩ := hs
  obtain ⟨u, v, huv⟩ := hn
  rw [hw] at huv
  have h : p * (u + v * w) = 1 := by linear_combination huv
  exact isUnit_of_dvd_one ⟨u + v * w, h.symm⟩

/-- A unit is normal. -/
theorem isNormal_of_isUnit {R : Type*} [CommRing R] [Differential R] {p : R} (hu : IsUnit p) :
    IsNormal p := by
  obtain ⟨u, rfl⟩ := hu
  exact ⟨↑u⁻¹, 0, by simp⟩

/-- `p` is both normal and special iff it is a unit. -/
theorem isNormal_and_isSpecial_iff_isUnit {R : Type*} [CommRing R] [Differential R] {p : R} :
    (IsNormal p ∧ IsSpecial p) ↔ IsUnit p :=
  ⟨fun ⟨hn, hs⟩ => isUnit_of_isNormal_of_isSpecial hn hs,
   fun hu => ⟨isNormal_of_isUnit hu, hu.dvd⟩⟩

end DeepWiki.SymbolicIntegration
