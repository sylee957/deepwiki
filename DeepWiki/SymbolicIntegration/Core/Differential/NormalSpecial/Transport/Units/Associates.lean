import DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial.Transport.Units.Intersection

/-! # Unit and associate transport for normal and special elements

Transport of normality and specialness across unit multiples and associated elements.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

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
