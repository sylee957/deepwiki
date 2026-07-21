import DeepWiki.CAlgebra.Frac.Field

/-! # The expression frontend: rational-function syntax

An abstract syntax tree for univariate rational-function expressions, with its
denotation into `RatFunc R` and a computable, **verified** normalization into the
canonical fraction field `DenseFrac R` — the entry point of the integration pipeline. -/

namespace DeepWiki.CAlgebra

universe u

/-- Syntax of univariate rational-function expressions over `R`. -/
inductive Expr (R : Type u) where
  /-- A scalar constant. -/
  | const (c : R)
  /-- The variable. -/
  | X
  /-- Addition. -/
  | add (a b : Expr R)
  /-- Multiplication. -/
  | mul (a b : Expr R)
  /-- Negation. -/
  | neg (a : Expr R)
  /-- Subtraction. -/
  | sub (a b : Expr R)
  /-- Division. -/
  | div (a b : Expr R)
  /-- Inversion. -/
  | inv (a : Expr R)
  /-- Power by a natural exponent. -/
  | pow (a : Expr R) (n : ℕ)
  deriving DecidableEq

namespace Expr

open DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- Denotation of an expression in Mathlib's rational-function field. -/
noncomputable def eval : Expr R → RatFunc R
  | const c => algebraMap (Polynomial R) (RatFunc R) (Polynomial.C c)
  | X => algebraMap (Polynomial R) (RatFunc R) Polynomial.X
  | add a b => a.eval + b.eval
  | mul a b => a.eval * b.eval
  | neg a => -a.eval
  | sub a b => a.eval - b.eval
  | div a b => a.eval / b.eval
  | inv a => (a.eval)⁻¹
  | pow a n => a.eval ^ n

/-- Computable normalization into the canonical fraction field. -/
def toFrac : Expr R → DenseFrac R
  | const c => DenseFrac.ofPoly (DensePoly.C c)
  | X => DenseFrac.ofPoly (DensePoly.ofList [0, 1])
  | add a b => a.toFrac + b.toFrac
  | mul a b => a.toFrac * b.toFrac
  | neg a => -a.toFrac
  | sub a b => a.toFrac - b.toFrac
  | div a b => a.toFrac / b.toFrac
  | inv a => (a.toFrac)⁻¹
  | pow a n => a.toFrac ^ n

omit [DensePolyGcd R] in
/-- The engine's variable polynomial reads as `Polynomial.X`. -/
theorem toPolynomial_X :
    toPolynomial (DensePoly.ofList [0, 1] : DensePoly R) = Polynomial.X := by
  refine Polynomial.ext fun n => ?_
  rw [coeff_toPolynomial]
  rcases n with _ | _ | n <;> simp [coeff_ofList, Polynomial.coeff_X]

/-- **Frontend soundness**: the computable normalization agrees with the denotation. -/
theorem toRatFunc_toFrac (e : Expr R) : DenseFrac.toRatFunc e.toFrac = e.eval := by
  induction e with
  | const c => rw [toFrac, eval, DenseFrac.toRatFunc_ofPoly, toPolynomial_C]
  | X => rw [toFrac, eval, DenseFrac.toRatFunc_ofPoly, toPolynomial_X]
  | add a b iha ihb => rw [toFrac, eval, DenseFrac.toRatFunc_add, iha, ihb]
  | mul a b iha ihb => rw [toFrac, eval, DenseFrac.toRatFunc_mul, iha, ihb]
  | neg a iha => rw [toFrac, eval, DenseFrac.toRatFunc_neg, iha]
  | sub a b iha ihb =>
      rw [toFrac, eval, sub_eq_add_neg, sub_eq_add_neg, DenseFrac.toRatFunc_add,
        DenseFrac.toRatFunc_neg, iha, ihb]
  | div a b iha ihb =>
      rw [toFrac, eval, div_eq_mul_inv, div_eq_mul_inv, DenseFrac.toRatFunc_mul,
        DenseFrac.toRatFunc_inv, iha, ihb]
  | inv a iha => rw [toFrac, eval, DenseFrac.toRatFunc_inv, iha]
  | pow a n iha => rw [toFrac, eval, ← iha]; exact map_pow (DenseFrac.equivRatFunc) _ n

end Expr

end DeepWiki.CAlgebra
