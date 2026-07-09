import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate

/-! # `CDiffFieldSpec (CFrac ℚ)` differential-spec bridge for the `ℚ(x)` carrier.
Noncomputable base derivation `baseDerivQ` on `ℚ[X]` and its fraction-field extension on `RatFunc ℚ`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-! ### The differential-spec bridge `CDiffFieldSpec (CFrac ℚ)` -/

/-- The base derivation `implicitDeriv (toPoly 1)` whose fraction-field extension realizes `towerDerivCFrac [1]`. -/
noncomputable def baseDerivQ : Derivation ℤ (CFieldSpec.K ℚ)[X] (CFieldSpec.K ℚ)[X] :=
  Differential.implicitDeriv (DensePoly.toPoly ([CField.one] : DensePoly ℚ))

/-- `CDiffFieldSpec (CFrac ℚ)` using `fractionFieldDifferential baseDerivQ` and `toCFracG_towerDerivCFracG [1]`. -/
noncomputable instance instCDiffFieldSpecCFrac : CDiffFieldSpec (CFrac ℚ) where
  diffK := fractionFieldDifferential baseDerivQ
  toK_cderiv a := by
    show toCFrac (towerDerivCFrac [CField.one] a)
      = @Differential.deriv _ _ (fractionFieldDifferential baseDerivQ) (toCFrac a)
    rw [toCFracG_towerDerivCFracG [CField.one] a]
    rfl


end DeepWiki.SymbolicIntegration
