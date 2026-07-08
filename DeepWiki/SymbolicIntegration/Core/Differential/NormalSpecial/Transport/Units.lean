import DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial.Core

/-! # Unit and associate transport for normal and special elements

Unit, associate, and unit-intersection facts for normal and special elements.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- A polynomial that is both normal and special is a unit. -/
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

/-- Specialness is unit-invariant: `IsSpecial (u * p) ↔ IsSpecial p`. -/
theorem IsSpecial.unit_mul_iff {R : Type*} [CommRing R] [Differential R] {u : R} (hu : IsUnit u)
    (p : R) : IsSpecial (u * p) ↔ IsSpecial p := by
  unfold IsSpecial
  rw [deriv_mul_eq, hu.mul_left_dvd, add_comm, dvd_add_right (dvd_mul_right p u′),
    hu.dvd_mul_left]

/-- Normality is unit-invariant: `IsNormal (u * p) ↔ IsNormal p`. -/
theorem IsNormal.unit_mul_iff {R : Type*} [CommRing R] [Differential R] {u : R} (hu : IsUnit u)
    (p : R) : IsNormal (u * p) ↔ IsNormal p := by
  unfold IsNormal
  rw [deriv_mul_eq, isCoprime_mul_unit_left_left hu, IsCoprime.add_mul_left_right_iff,
    isCoprime_mul_unit_left_right hu]

/-- Specialness is an associate invariant: `Associated p q → IsSpecial p → IsSpecial q`. -/
theorem IsSpecial.of_associated {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : Associated p q) (hp : IsSpecial p) : IsSpecial q := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  exact (IsSpecial.unit_mul_iff u.isUnit p).mpr hp

/-- Normality is an associate invariant: `Associated p q → IsNormal p → IsNormal q`. -/
theorem IsNormal.of_associated {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : Associated p q) (hp : IsNormal p) : IsNormal q := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  exact (IsNormal.unit_mul_iff u.isUnit p).mpr hp

end DeepWiki.SymbolicIntegration
