import DeepWiki.CAlgebra.Poly.Euclid

/-! # Monic dense polynomials (`DensePolyMonic`)

The bundled sub-carrier of monic dense polynomials: closed under multiplication with unit `1`,
never zero, and rigid up to association (`eq_of_associated`: associated monic polynomials are
equal — monicity pins the unit). This rigidity is what makes monic denominators canonical. -/

namespace DeepWiki.CAlgebra

universe u

/-- A dense polynomial bundled with monicity of its leading coefficient. -/
structure DensePolyMonic (R : Type u) [CommRing R] [DecidableEq R] where
  /-- The underlying polynomial. -/
  toPoly : DensePoly R
  /-- The leading coefficient is `1`. -/
  monic : toPoly.leadingCoeff = 1

namespace DensePolyMonic

section CommRing

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- Monic wrappers are equal when the underlying polynomials are. -/
@[ext] theorem ext {p q : DensePolyMonic R} (h : p.toPoly = q.toPoly) : p = q := by
  cases p; cases q; cases h; rfl

/-- Structural equality of monic polynomials is decidable. -/
instance : DecidableEq (DensePolyMonic R) := fun a b =>
  match decEq a.toPoly b.toPoly with
  | isTrue h => isTrue (ext h)
  | isFalse h => isFalse fun hh => h (congrArg toPoly hh)

/-- A monic polynomial is nonzero (in a nontrivial ring). -/
theorem ne_zero [Nontrivial R] (p : DensePolyMonic R) : p.toPoly ≠ 0 := fun h0 => by
  have h := p.monic
  rw [h0, DensePoly.leadingCoeff_zero] at h
  exact zero_ne_one h

end CommRing

section Field

variable {R : Type u} [Field R] [DecidableEq R]

/-- The unit polynomial is monic. -/
instance : One (DensePolyMonic R) := ⟨1, DensePoly.leadingCoeff_one⟩

@[simp] theorem toPoly_one : (1 : DensePolyMonic R).toPoly = 1 := rfl

/-- Monic polynomials are closed under multiplication. -/
instance : Mul (DensePolyMonic R) :=
  ⟨fun p q => ⟨p.toPoly * q.toPoly, by
    rw [DensePoly.leadingCoeff_mul p.ne_zero q.ne_zero, p.monic, q.monic, one_mul]⟩⟩

@[simp] theorem toPoly_mul (p q : DensePolyMonic R) :
    (p * q).toPoly = p.toPoly * q.toPoly := rfl

/-- Associated monic polynomials are equal: the associating unit is a constant, and monicity
pins it to `1`. -/
theorem eq_of_associated {p q : DensePolyMonic R} (h : Associated p.toPoly q.toPoly) : p = q := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, hc0, hcu⟩ := DensePoly.exists_C_of_isUnit u.isUnit
  have hc1 : c = 1 := by
    have hlc := congrArg DensePoly.leadingCoeff hu
    rw [hcu, mul_comm, DensePoly.leadingCoeff_C_mul hc0, p.monic, mul_one, q.monic] at hlc
    exact hlc
  refine ext ?_
  rw [← hu, hcu, hc1, ← DensePoly.one_def, mul_one]

end Field

end DensePolyMonic

end DeepWiki.CAlgebra
