import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing

/-! # The derivative on rational functions

`RatFunc.deriv`: the unique extension of `Polynomial.derivative` to `RatFunc K` by the
quotient rule, packaged as a `Derivation ℤ` and a `Differential (RatFunc K)` instance.
The workhorse is representation independence (`RatFunc.deriv_div`): the quotient-rule
formula evaluated on any fraction representation `p/q` agrees with its value on the
canonical `num/denom` pair, by differentiating the cross-multiplication identity.
Mathlib lacks these; upstream candidates. -/

universe u

open Polynomial

namespace RatFunc

variable {K : Type u} [Field K]

/-- The derivative of a rational function: the quotient rule on the canonical
`num`/`denom` representation. -/
noncomputable def deriv (f : RatFunc K) : RatFunc K :=
  (algebraMap K[X] (RatFunc K) (derivative f.num) * algebraMap K[X] (RatFunc K) f.denom
    - algebraMap K[X] (RatFunc K) f.num * algebraMap K[X] (RatFunc K) (derivative f.denom))
    / algebraMap K[X] (RatFunc K) f.denom ^ 2

/-- **Representation independence**: the quotient rule computes on any fraction
representation, not just the canonical one. -/
theorem deriv_div {p q : K[X]} (hq : q ≠ 0) :
    deriv (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q)
      = (algebraMap K[X] (RatFunc K) (derivative p) * algebraMap K[X] (RatFunc K) q
          - algebraMap K[X] (RatFunc K) p * algebraMap K[X] (RatFunc K) (derivative q))
        / algebraMap K[X] (RatFunc K) q ^ 2 := by
  set f := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q with hf
  have hd : f.denom ≠ 0 := denom_ne_zero f
  have hAq : algebraMap K[X] (RatFunc K) q ≠ 0 := algebraMap_ne_zero hq
  have hAd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := algebraMap_ne_zero hd
  -- the cross identity between the two representations
  have hcross : f.num * q = p * f.denom := by
    have hrep : algebraMap K[X] (RatFunc K) f.num / algebraMap K[X] (RatFunc K) f.denom
        = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q :=
      (num_div_denom f).trans hf
    rw [div_eq_div_iff hAd hAq, ← map_mul, ← map_mul] at hrep
    exact algebraMap_injective K hrep
  have hcross' : derivative f.num * q + f.num * derivative q
      = derivative p * f.denom + p * derivative f.denom := by
    have := congrArg derivative hcross
    rwa [derivative_mul, derivative_mul] at this
  rw [deriv, div_eq_div_iff (pow_ne_zero 2 hAd) (pow_ne_zero 2 hAq)]
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_sub,
    ← map_mul, ← map_mul]
  congr 1
  linear_combination (f.denom * q) * hcross'
    - (derivative f.denom * q + derivative q * f.denom) * hcross

/-- The derivative restricts to the polynomial derivative on polynomials. -/
theorem deriv_algebraMap (p : K[X]) :
    deriv (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (derivative p) := by
  have h := deriv_div (K := K) (p := p) (q := 1) one_ne_zero
  simpa using h

/-- The derivative of `0` vanishes. -/
@[simp] theorem deriv_zero : deriv (0 : RatFunc K) = 0 := by
  have h := deriv_algebraMap (K := K) 0
  simpa using h

/-- The derivative is additive. -/
theorem deriv_add (f g : RatFunc K) : deriv (f + g) = deriv f + deriv g := by
  have hfd : f.denom ≠ 0 := denom_ne_zero f
  have hgd : g.denom ≠ 0 := denom_ne_zero g
  have hAfd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := algebraMap_ne_zero hfd
  have hAgd : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := algebraMap_ne_zero hgd
  have hsum : f + g = algebraMap K[X] (RatFunc K) (f.num * g.denom + f.denom * g.num)
      / algebraMap K[X] (RatFunc K) (f.denom * g.denom) := by
    conv_lhs => rw [← num_div_denom f, ← num_div_denom g]
    rw [div_add_div _ _ hAfd hAgd, map_add, map_mul, map_mul, map_mul]
  rw [hsum, deriv_div (mul_ne_zero hfd hgd)]
  conv_rhs => rw [← num_div_denom f, ← num_div_denom g, deriv_div hfd, deriv_div hgd]
  simp only [derivative_mul, map_add, map_mul]
  field_simp
  ring

/-- The derivative satisfies the Leibniz rule. -/
theorem deriv_mul (f g : RatFunc K) : deriv (f * g) = f * deriv g + g * deriv f := by
  have hfd : f.denom ≠ 0 := denom_ne_zero f
  have hgd : g.denom ≠ 0 := denom_ne_zero g
  have hAfd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := algebraMap_ne_zero hfd
  have hAgd : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := algebraMap_ne_zero hgd
  have hprod : f * g = algebraMap K[X] (RatFunc K) (f.num * g.num)
      / algebraMap K[X] (RatFunc K) (f.denom * g.denom) := by
    conv_lhs => rw [← num_div_denom f, ← num_div_denom g]
    rw [div_mul_div_comm, map_mul, map_mul]
  rw [hprod, deriv_div (mul_ne_zero hfd hgd)]
  conv_rhs => rw [← num_div_denom f, ← num_div_denom g, deriv_div hfd, deriv_div hgd]
  simp only [derivative_mul, map_add, map_mul]
  field_simp
  ring

/-- Derivatives of constants (integer casts) vanish. -/
theorem deriv_intCast (n : ℤ) : deriv ((n : RatFunc K)) = 0 := by
  have h : ((n : RatFunc K)) = algebraMap K[X] (RatFunc K) ((n : K[X])) := by
    rw [map_intCast]
  rw [h, deriv_algebraMap]
  simp

/-- The derivative commutes with integer scalar multiplication. -/
theorem deriv_zsmul (n : ℤ) (f : RatFunc K) : deriv (n • f) = n • deriv f := by
  rw [zsmul_eq_mul, zsmul_eq_mul, deriv_mul, deriv_intCast, mul_zero, add_zero]

/-- `RatFunc K` is a differential field: the quotient-rule derivative as a `ℤ`-derivation.
The `letI` pins the `ℤ`-algebra structure to `Ring.toIntAlgebra` (the one `Differential`
expects), overriding RatFunc's polynomial-lift `Algebra ℤ` instance. -/
noncomputable instance : Differential (RatFunc K) where
  deriv :=
    letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
    { toFun := deriv
      map_add' := deriv_add
      map_smul' := fun n f => by
        show deriv (n • f) = n • deriv f
        rw [zsmul_eq_mul, zsmul_eq_mul, deriv_mul, deriv_intCast, mul_zero, add_zero]
      map_one_eq_zero' := by
        show deriv 1 = 0
        have h := deriv_algebraMap (K := K) 1
        simpa using h
      leibniz' := fun a b => by
        show deriv (a * b) = a • deriv b + b • deriv a
        rw [deriv_mul, smul_eq_mul, smul_eq_mul] }

open scoped Differential in
/-- The `′` of the `Differential` instance is `RatFunc.deriv`. -/
@[simp] theorem differential_apply (f : RatFunc K) : f′ = deriv f := rfl

end RatFunc
