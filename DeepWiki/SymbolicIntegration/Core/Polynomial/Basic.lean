import Mathlib.Algebra.Polynomial.Div
import DeepWiki.SymbolicIntegration.Core.Polynomial.PolynomialNormalization
import DeepWiki.SymbolicIntegration.Core.Polynomial.ResultantRoots

/-! # Basic polynomial support

Aggregator for normalization, root evaluation, and resultants.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- `(P %ₘ D).eval α = P.eval α` at a root `α` of a monic polynomial `D`. -/
theorem eval_modByMonic_of_root {P D : K[X]} {α : K} (_hD : D.Monic) (hα : D.eval α = 0) :
    (P %ₘ D).eval α = P.eval α := by
  conv_rhs => rw [← modByMonic_add_div P D]
  rw [Polynomial.eval_add, Polynomial.eval_mul, hα, zero_mul, add_zero]

end DeepWiki.SymbolicIntegration
