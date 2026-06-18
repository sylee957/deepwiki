import DeepWiki.TimeSeries.BackshiftOperator
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-! # Lag polynomials
The backshift `B` as a linear endomorphism of the sequence space `ℤ → M`, and the
**lag polynomials** `p(B)` obtained by evaluating a polynomial `p` (the AR/MA
polynomials `φ`, `θ` of an ARMA model) at `B`. Lag polynomials form the
commutative algebra `K[B]` acting on sequences: `p(B) q(B) = (pq)(B)` and `(p+q)(B)
= p(B) + q(B)` come for free from `Polynomial.aeval` being an algebra
homomorphism. The difference operators of §1.4 are the lag polynomials `1 − z` and
`1 − zᵈ`. -/

namespace DeepWiki.TimeSeries

open Polynomial

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- The backshift operator `B` as a `K`-linear endomorphism of the sequence space
`ℤ → M`. -/
def backshiftL : Module.End K (ℤ → M) where
  toFun := backshift
  map_add' x y := backshift_add x y
  map_smul' c x := by funext t; simp [Pi.smul_apply]

@[simp] theorem backshiftL_coe : ⇑(backshiftL : Module.End K (ℤ → M)) = backshift := rfl

@[simp] theorem backshiftL_apply (x : ℤ → M) (t : ℤ) :
    (backshiftL : Module.End K (ℤ → M)) x t = x (t - 1) := rfl

/-- A **lag polynomial** `p(B)`: the polynomial `p` evaluated at the backshift, a
`K`-linear endomorphism of `ℤ → M`. -/
noncomputable def lagPoly (p : K[X]) : Module.End K (ℤ → M) := aeval backshiftL p

@[simp] theorem lagPoly_X : lagPoly (X : K[X]) = (backshiftL : Module.End K (ℤ → M)) := by
  simp [lagPoly]

@[simp] theorem lagPoly_one : lagPoly (1 : K[X]) = (1 : Module.End K (ℤ → M)) := by
  simp [lagPoly]

/-- `(C c)(B) = c • id`: a constant polynomial acts by scalar multiplication. -/
@[simp] theorem lagPoly_C_apply (c : K) (x : ℤ → M) : lagPoly (C c) x = c • x := by
  rw [lagPoly, aeval_C, Module.algebraMap_end_apply]

/-- Addition of polynomials becomes addition of lag operators: `(p+q)(B) = p(B) + q(B)`. -/
theorem lagPoly_add (p q : K[X]) :
    lagPoly (p + q) = (lagPoly p : Module.End K (ℤ → M)) + lagPoly q := by
  simp [lagPoly, map_add]

/-- Multiplication of polynomials becomes composition of lag operators:
`(pq)(B) = p(B) ∘ q(B)`. -/
theorem lagPoly_mul (p q : K[X]) :
    lagPoly (p * q) = (lagPoly p : Module.End K (ℤ → M)) * lagPoly q := by
  simp [lagPoly, map_mul]

/-- `(pq)(B) x = p(B) (q(B) x)`: the composition reading of `lagPoly_mul`. -/
theorem lagPoly_mul_apply (p q : K[X]) (x : ℤ → M) :
    lagPoly (p * q) x = lagPoly p (lagPoly q x) := by
  rw [lagPoly_mul]; rfl

/-! ## The difference operators as lag polynomials (§1.4) -/

/-- The lag polynomial `1 − z` is the difference operator `∇ = 1 − B`. -/
theorem lagPoly_one_sub_X :
    lagPoly (1 - X : K[X]) = 1 - (backshiftL : Module.End K (ℤ → M)) := by
  simp only [lagPoly, map_sub, map_one, aeval_X]

/-- `(1 − z)(B) x = ∇ x`: the lag polynomial `1 − z` acts as `∇`. -/
theorem lagPoly_one_sub_X_apply (x : ℤ → M) :
    lagPoly (1 - X : K[X]) x = difference x := by
  rw [lagPoly_one_sub_X, LinearMap.sub_apply, Module.End.one_apply, backshiftL_coe,
    difference_eq_sub_backshift]

/-- The lag polynomial `1 − zᵈ` is the lag-`d` difference operator `∇_d = 1 − Bᵈ`. -/
theorem lagPoly_one_sub_X_pow (d : ℕ) :
    lagPoly (1 - X ^ d : K[X]) = 1 - (backshiftL : Module.End K (ℤ → M)) ^ d := by
  simp only [lagPoly, map_sub, map_one, map_pow, aeval_X]

/-- `(1 − zᵈ)(B) x = ∇_d x`: the lag polynomial `1 − zᵈ` acts as `∇_d`. -/
theorem lagPoly_one_sub_X_pow_apply (d : ℕ) (x : ℤ → M) :
    lagPoly (1 - X ^ d : K[X]) x = seasonalDifference d x := by
  rw [lagPoly_one_sub_X_pow, LinearMap.sub_apply, Module.End.one_apply, Module.End.pow_apply,
    backshiftL_coe, seasonalDifference_eq_sub_backshift_iterate]

end DeepWiki.TimeSeries
