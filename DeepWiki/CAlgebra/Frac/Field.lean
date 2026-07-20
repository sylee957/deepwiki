import DeepWiki.CAlgebra.Frac.Basic

/-! # The computable rational-function field and its isomorphism with `RatFunc`

The canonical fractions form a computable `Field` (laws transported through the injective
denotation), and the denotation upgrades to a ring isomorphism
`equivRatFunc : DenseFrac R ≃+* RatFunc R`. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R]

namespace DenseFrac

/-- The canonical fractions form a computable commutative ring: arithmetic renormalizes through
`normalize`, laws transport through the injective denotation. -/
instance : CommRing (DenseFrac R) where
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
instance : Field (DenseFrac R) :=
  { (inferInstance : CommRing (DenseFrac R)) with
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
    inv_zero := by
      show normalize (1 : DensePoly R) 0 = 0
      exact normalize_den_zero 1 }

/-! ### The ring isomorphism with `RatFunc` -/

/-- Read a rational function back as its canonical fraction. -/
noncomputable def ofRatFunc (x : RatFunc R) : DenseFrac R :=
  normalize (ofPolynomial x.num) (ofPolynomial x.denom)

/-- `ofRatFunc` is a right inverse of the denotation. -/
theorem toRatFunc_ofRatFunc (x : RatFunc R) : toRatFunc (ofRatFunc x) = x := by
  rw [ofRatFunc, toRatFunc_normalize, toPolynomial_ofPolynomial, toPolynomial_ofPolynomial]
  exact RatFunc.num_div_denom x

/-- The computable canonical fraction field is ring-isomorphic to Mathlib's rational-function
field. -/
noncomputable def equivRatFunc : DenseFrac R ≃+* RatFunc R where
  toFun := toRatFunc
  invFun := ofRatFunc
  left_inv f := toRatFunc_injective (toRatFunc_ofRatFunc (toRatFunc f))
  right_inv := toRatFunc_ofRatFunc
  map_mul' := toRatFunc_mul
  map_add' := toRatFunc_add

end DenseFrac

end DeepWiki.CAlgebra
