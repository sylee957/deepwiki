import DeepWiki.CAlgebra.Frac.Canonical

/-! # The canonical fraction field and its isomorphism with `RatFunc`

`CanonicalFrac R` is the subtype of canonical fractions (monic denominator, coprime parts).
Arithmetic renormalizes through `reduce`, so structural equality is semantic equality
(`toRatFunc_eq_iff`, with decidable equality), the carrier is a computable `Field`, and the
denotation is a ring isomorphism `equivRatFunc : CanonicalFrac R ≃+* RatFunc R`. -/

namespace DeepWiki.CAlgebra

universe u

/-- The canonical-fraction carrier: gcd-reduced, monic-denominator fractions. -/
def CanonicalFrac (R : Type u) [Field R] [DecidableEq R] : Type u :=
  {f : DenseFrac R // f.IsCanonical}

variable {R : Type u} [Field R] [DecidableEq R]

namespace CanonicalFrac

instance : DecidableEq (CanonicalFrac R) :=
  inferInstanceAs (DecidableEq {f : DenseFrac R // f.IsCanonical})

instance : Zero (CanonicalFrac R) :=
  ⟨⟨⟨0, 1⟩, DensePoly.leadingCoeff_one, isCoprime_zero_left.mpr isUnit_one⟩⟩

instance : One (CanonicalFrac R) :=
  ⟨⟨⟨1, 1⟩, DensePoly.leadingCoeff_one, isCoprime_one_left⟩⟩

instance : Add (CanonicalFrac R) :=
  ⟨fun a b => ⟨DenseFrac.reduce (a.val + b.val), DenseFrac.isCanonical_reduce _⟩⟩

instance : Mul (CanonicalFrac R) :=
  ⟨fun a b => ⟨DenseFrac.reduce (a.val * b.val), DenseFrac.isCanonical_reduce _⟩⟩

instance : Neg (CanonicalFrac R) :=
  ⟨fun a => ⟨DenseFrac.reduce (-a.val), DenseFrac.isCanonical_reduce _⟩⟩

instance : Inv (CanonicalFrac R) :=
  ⟨fun a => ⟨DenseFrac.reduce a.val⁻¹, DenseFrac.isCanonical_reduce _⟩⟩

/-- Canonicalize any raw fraction into the carrier (the computable section of the quotient). -/
def ofFrac (f : DenseFrac R) : CanonicalFrac R :=
  ⟨DenseFrac.reduce f, DenseFrac.isCanonical_reduce f⟩

/-- Denotation of a canonical fraction into the rational-function field. -/
noncomputable def toRatFunc (f : CanonicalFrac R) : RatFunc R := f.val.toRatFunc

/-- `ofFrac` preserves the denotation. -/
theorem toRatFunc_ofFrac (f : DenseFrac R) : toRatFunc (ofFrac f) = f.toRatFunc :=
  DenseFrac.toRatFunc_reduce f

/-- The denotation is injective: canonical representatives are unique. -/
theorem toRatFunc_injective : Function.Injective (toRatFunc (R := R)) := fun a b h =>
  Subtype.ext (DenseFrac.eq_of_toRatFunc_eq a.prop b.prop h)

/-- Structural equality of canonical fractions is semantic equality in `RatFunc` (and structural
equality is decidable, so semantic equality is too). -/
theorem toRatFunc_eq_iff {a b : CanonicalFrac R} : toRatFunc a = toRatFunc b ↔ a = b :=
  ⟨fun h => toRatFunc_injective h, fun h => h ▸ rfl⟩

@[simp] theorem toRatFunc_zero : toRatFunc (0 : CanonicalFrac R) = 0 := by
  show DenseFrac.toRatFunc ⟨0, 1⟩ = 0
  simp [DenseFrac.toRatFunc]

@[simp] theorem toRatFunc_one : toRatFunc (1 : CanonicalFrac R) = 1 := by
  show DenseFrac.toRatFunc ⟨1, 1⟩ = 1
  simp [DenseFrac.toRatFunc]

@[simp] theorem toRatFunc_add (a b : CanonicalFrac R) :
    toRatFunc (a + b) = toRatFunc a + toRatFunc b := by
  show DenseFrac.toRatFunc (DenseFrac.reduce _) = _
  rw [DenseFrac.toRatFunc_reduce]
  exact DenseFrac.toRatFunc_add _ _ a.prop.den_ne_zero b.prop.den_ne_zero

@[simp] theorem toRatFunc_mul (a b : CanonicalFrac R) :
    toRatFunc (a * b) = toRatFunc a * toRatFunc b := by
  show DenseFrac.toRatFunc (DenseFrac.reduce _) = _
  rw [DenseFrac.toRatFunc_reduce]
  exact DenseFrac.toRatFunc_mul _ _

@[simp] theorem toRatFunc_neg (a : CanonicalFrac R) : toRatFunc (-a) = -toRatFunc a := by
  show DenseFrac.toRatFunc (DenseFrac.reduce _) = _
  rw [DenseFrac.toRatFunc_reduce]
  exact DenseFrac.toRatFunc_neg _

@[simp] theorem toRatFunc_inv (a : CanonicalFrac R) : toRatFunc a⁻¹ = (toRatFunc a)⁻¹ := by
  show DenseFrac.toRatFunc (DenseFrac.reduce _) = _
  rw [DenseFrac.toRatFunc_reduce]
  exact DenseFrac.toRatFunc_inv _

/-- The canonical fractions form a computable commutative ring: arithmetic renormalizes through
`reduce`, laws transport through the injective denotation. -/
instance : CommRing (CanonicalFrac R) where
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  sub a b := a + (-b)
  zero := 0
  one := 1
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := toRatFunc_injective (by simp only [toRatFunc_add]; ring)
  zero_add a := toRatFunc_injective (by simp only [toRatFunc_add, toRatFunc_zero]; ring)
  add_zero a := toRatFunc_injective (by simp only [toRatFunc_add, toRatFunc_zero]; ring)
  add_comm a b := toRatFunc_injective (by simp only [toRatFunc_add]; ring)
  mul_assoc a b c := toRatFunc_injective (by simp only [toRatFunc_mul]; ring)
  one_mul a := toRatFunc_injective (by simp only [toRatFunc_mul, toRatFunc_one]; ring)
  mul_one a := toRatFunc_injective (by simp only [toRatFunc_mul, toRatFunc_one]; ring)
  left_distrib a b c :=
    toRatFunc_injective (by simp only [toRatFunc_mul, toRatFunc_add]; ring)
  right_distrib a b c :=
    toRatFunc_injective (by simp only [toRatFunc_mul, toRatFunc_add]; ring)
  mul_comm a b := toRatFunc_injective (by simp only [toRatFunc_mul]; ring)
  neg_add_cancel a :=
    toRatFunc_injective (by simp only [toRatFunc_add, toRatFunc_neg, toRatFunc_zero]; ring)
  zero_mul a := toRatFunc_injective (by simp only [toRatFunc_mul, toRatFunc_zero]; ring)
  mul_zero a := toRatFunc_injective (by simp only [toRatFunc_mul, toRatFunc_zero]; ring)
  sub_eq_add_neg a b := rfl

/-- The canonical fractions form a computable field: inversion swaps the pair and renormalizes. -/
instance : Field (CanonicalFrac R) :=
  { (inferInstance : CommRing (CanonicalFrac R)) with
    inv := (·⁻¹)
    div := fun a b => a * b⁻¹
    div_eq_mul_inv := fun _ _ => rfl
    nnqsmul := _
    qsmul := _
    exists_pair_ne := ⟨0, 1, fun h => by
      have h' := congrArg toRatFunc h
      rw [toRatFunc_zero, toRatFunc_one] at h'
      exact zero_ne_one h'⟩
    mul_inv_cancel := fun a ha => toRatFunc_injective (by
      have ha' : toRatFunc a ≠ 0 := fun h0 =>
        ha (toRatFunc_injective (by rw [h0, toRatFunc_zero]))
      simp only [toRatFunc_mul, toRatFunc_inv, toRatFunc_one]
      exact mul_inv_cancel₀ ha')
    inv_zero := Subtype.ext (by
      show DenseFrac.reduce ⟨1, 0⟩ = (⟨0, 1⟩ : DenseFrac R)
      rw [DenseFrac.reduce, if_pos rfl]) }

/-! ### The ring isomorphism with `RatFunc` -/

/-- Read a rational function back as its canonical fraction. -/
noncomputable def ofRatFunc (x : RatFunc R) : CanonicalFrac R :=
  ⟨DenseFrac.reduce ⟨ofPolynomial x.num, ofPolynomial x.denom⟩, DenseFrac.isCanonical_reduce _⟩

/-- `ofRatFunc` is a right inverse of the denotation. -/
theorem toRatFunc_ofRatFunc (x : RatFunc R) : toRatFunc (ofRatFunc x) = x := by
  show DenseFrac.toRatFunc (DenseFrac.reduce _) = x
  rw [DenseFrac.toRatFunc_reduce]
  simp only [DenseFrac.toRatFunc]
  rw [toPolynomial_ofPolynomial, toPolynomial_ofPolynomial]
  exact RatFunc.num_div_denom x

/-- The canonical fraction field is ring-isomorphic to Mathlib's rational-function field. -/
noncomputable def equivRatFunc : CanonicalFrac R ≃+* RatFunc R where
  toFun := toRatFunc
  invFun := ofRatFunc
  left_inv f := toRatFunc_injective (toRatFunc_ofRatFunc (toRatFunc f))
  right_inv := toRatFunc_ofRatFunc
  map_mul' := toRatFunc_mul
  map_add' := toRatFunc_add

end CanonicalFrac

end DeepWiki.CAlgebra
