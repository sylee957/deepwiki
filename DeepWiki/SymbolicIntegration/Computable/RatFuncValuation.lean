import DeepWiki.SymbolicIntegration.Computable.RatFuncValuation.Basic
import DeepWiki.SymbolicIntegration.Computable.RatFuncValuation.NormalPole
import DeepWiki.SymbolicIntegration.Computable.RatFuncValuation.DenominatorBound

/-! # The `K(t)`-valuation calculus for normal poles

Aggregator for the `p`-adic valuation `ratFuncOrd p x = νₚ(x)` on `RatFunc K`, its
basic algebraic laws, normal-pole derivative consequences, and denominator divisibility bounds.
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

-- Restatement of the lift: `νₚ(D y) = νₚ(y) − 1` at a normal pole, `D = extendDeriv d`.
example [CharZero K] (d : Derivation ℤ K[X] K[X]) {p : K[X]} (hp : Prime p) (hnormal : ¬ p ∣ d p)
    {y : RatFunc K} (hpole : ratFuncOrd p y < 0) :
    ratFuncOrd p (extendDeriv d y) = ratFuncOrd p y - 1 :=
  ratFuncOrd_extendDeriv_eq_sub_one_of_normal d hp hnormal hpole

end DeepWiki.SymbolicIntegration
