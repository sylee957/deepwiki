import DeepWiki.SymbolicIntegration.Engine.RatFuncValuation.Basic

/-! # The `K(t)`-valuation calculus

Aggregator for the `p`-adic valuation `ratFuncOrd p x = νₚ(x)` on `RatFunc K` and its basic
algebraic laws (`Basic`).
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ### Restatements -/

-- Restatement: `νₚ` reads through any nonzero representation.
example (p : K[X]) (hp : Prime p) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ratFuncOrd p (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b)
      = (multiplicity p a : ℤ) - (multiplicity p b : ℤ) :=
  ratFuncOrd_mk p hp ha hb

end DeepWiki.SymbolicIntegration
