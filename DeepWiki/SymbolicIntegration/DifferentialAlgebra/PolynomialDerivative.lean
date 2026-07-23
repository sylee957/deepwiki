import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Tactic

/-! # Formal polynomial derivatives

The formal derivative as an opt-in differential structure and reusable polynomial-calculus identities.
-/

universe u

namespace FormalDiff

/-- The formal derivative as an opt-in differential structure on `Polynomial R`. -/
noncomputable scoped instance {R : Type u} [CommRing R] : Differential (Polynomial R) :=
  ⟨(Polynomial.derivative' (R := R)).restrictScalars ℤ⟩

end FormalDiff

namespace DeepWiki.SymbolicIntegration

open scoped Differential FormalDiff

/-- Under `FormalDiff`, `q′` is `Polynomial.derivative q`. -/
@[simp] theorem polynomial_differential_apply {R : Type u} [CommRing R] (q : Polynomial R) :
    q′ = Polynomial.derivative q := rfl

open Polynomial

variable {K : Type*} [Field K]

/-- Leibniz for iterated derivatives of `(X - C α) * p`. -/
theorem iterate_derivative_X_sub_C_mul (α : K) (p : K[X]) (k : ℕ) :
    derivative^[k + 1] ((Polynomial.X - Polynomial.C α) * p)
      = (Polynomial.X - Polynomial.C α) * derivative^[k + 1] p
        + ((k + 1 : ℕ)) • derivative^[k] p := by
  induction k with
  | zero =>
    simp only [Function.iterate_one, Function.iterate_zero_apply, zero_add, derivative_mul,
      derivative_sub, derivative_X, Polynomial.derivative_C, sub_zero, one_mul, one_smul]
    ring
  | succ n ih =>
    have e1 : derivative^[n + 2] ((Polynomial.X - Polynomial.C α) * p)
        = derivative (derivative^[n + 1] ((Polynomial.X - Polynomial.C α) * p)) :=
      Function.iterate_succ_apply' derivative (n + 1) _
    have e2 : derivative (derivative^[n + 1] p) = derivative^[n + 2] p :=
      (Function.iterate_succ_apply' derivative (n + 1) p).symm
    have e3 : derivative (derivative^[n] p) = derivative^[n + 1] p :=
      (Function.iterate_succ_apply' derivative n p).symm
    rw [e1, ih, map_add, derivative_mul, derivative_sub, derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul, derivative_smul, e2, e3, succ_nsmul]
    ring_nf

/-- Evaluating the iterated derivative of `(X - C α) * p` at `α`. -/
theorem eval_iterate_derivative_X_sub_C_mul (α : K) (p : K[X]) (k : ℕ) :
    (derivative^[k + 1] ((Polynomial.X - Polynomial.C α) * p)).eval α
      = ((k : K) + 1) * (derivative^[k] p).eval α := by
  rw [iterate_derivative_X_sub_C_mul, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, zero_add,
    Polynomial.eval_smul, nsmul_eq_mul]
  push_cast
  ring

/-- The cofactor at a simple root: if `f = (X - C α) * g`, then `f'.eval α = g.eval α`. -/
theorem eval_derivative_of_X_sub_C_mul {f g : K[X]} {α : K}
    (hfac : f = (Polynomial.X - Polynomial.C α) * g) :
    (derivative f).eval α = g.eval α := by
  subst hfac
  rw [derivative_mul, derivative_sub, derivative_X, Polynomial.derivative_C, sub_zero, one_mul,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_mul, add_zero]

end DeepWiki.SymbolicIntegration
