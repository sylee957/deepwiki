import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate

/-! # `CDiffFieldSpec (QFunNZ ℚ)` differential-spec bridge for the `ℚ(x)` carrier.
Noncomputable base derivation `baseDerivQ` on `ℚ[X]` and its fraction-field extension on `RatFunc ℚ`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZ

/-! ### The differential-spec bridge `CDiffFieldSpec (QFunNZ ℚ)` -/

/-- The base derivation `implicitDeriv (toPoly 1)` whose fraction-field extension realizes `towerDerivQFunNZ [1]`. -/
noncomputable def baseDerivQ : Derivation ℤ (CFieldSpec.K ℚ)[X] (CFieldSpec.K ℚ)[X] :=
  Differential.implicitDeriv (CPoly.toPoly ([CField.one] : CPoly ℚ))

/-- `CDiffFieldSpec (QFunNZ ℚ)` using `fractionFieldDifferential baseDerivQ` and `toQFunNZG_towerDerivQFunNZG [1]`. -/
noncomputable instance instCDiffFieldSpecQFunNZ : CDiffFieldSpec (QFunNZ ℚ) where
  diffK := fractionFieldDifferential baseDerivQ
  toK_cderiv a := by
    show toQFunNZ (towerDerivQFunNZ [CField.one] a)
      = @Differential.deriv _ _ (fractionFieldDifferential baseDerivQ) (toQFunNZ a)
    rw [toQFunNZG_towerDerivQFunNZG [CField.one] a]
    rfl


end DeepWiki.SymbolicIntegration
