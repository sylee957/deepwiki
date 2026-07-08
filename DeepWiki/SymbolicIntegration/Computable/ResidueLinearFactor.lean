import DeepWiki.SymbolicIntegration.Computable.FractionFieldDeriv
import DeepWiki.SymbolicIntegration.Core.Differential.LinearRootEvaluation
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors

/-! # Linear-factor support for residue matching

Reusable facts about the linear factor `X - C α`: its monomial log-derivative, root evaluation of
`implicitDeriv`, and the `divByMonic` quotient formulas used by residue-match decompositions. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

namespace ResidueMatchTower

variable {K : Type*} [Field K] [Differential K]

/-- The monomial log-derivative of a linear factor: over `extendDeriv (implicitDeriv v)`,
`D(t−α)/(t−α) = algebraMap(v − C α′) / algebraMap(t − α)` in `RatFunc K`. -/
theorem extendDeriv_implicitDeriv_logDeriv_X_sub_C [Algebra ℚ K] (v : K[X]) (α : K) :
    extendDeriv (Differential.implicitDeriv v) (algebraMap K[X] (RatFunc K) (X - C α))
        / algebraMap K[X] (RatFunc K) (X - C α)
      = algebraMap K[X] (RatFunc K) (v - C (α′)) / algebraMap K[X] (RatFunc K) (X - C α) := by
  rw [extendDeriv_logDeriv, implicitDeriv_X_sub_C]

/-- The primitive-monomial log-derivative of a linear factor has constant numerator `C(w - α′)`. -/
theorem extendDeriv_implicitDeriv_C_logDeriv_X_sub_C [Algebra ℚ K] (w α : K) :
    extendDeriv (Differential.implicitDeriv (C w)) (algebraMap K[X] (RatFunc K) (X - C α))
        / algebraMap K[X] (RatFunc K) (X - C α)
      = algebraMap K[X] (RatFunc K) (C (w - α′)) / algebraMap K[X] (RatFunc K) (X - C α) := by
  rw [extendDeriv_implicitDeriv_logDeriv_X_sub_C, ← C_sub]

/-! ### Axiom audit -/

#print axioms ResidueMatchTower.extendDeriv_implicitDeriv_logDeriv_X_sub_C
#print axioms ResidueMatchTower.extendDeriv_implicitDeriv_C_logDeriv_X_sub_C

end ResidueMatchTower

end DeepWiki.SymbolicIntegration
