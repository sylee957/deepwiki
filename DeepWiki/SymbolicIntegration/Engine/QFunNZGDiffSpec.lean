import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate

/-! # `CDiffFieldSpec (QFunNZG ℚ)` differential-spec bridge for the `ℚ(x)` carrier.
Noncomputable base derivation `baseDerivQ` on `ℚ[X]` and its fraction-field extension on `RatFunc ℚ`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The differential-spec bridge `CDiffFieldSpec (QFunNZG ℚ)` -/

/-- The base derivation `implicitDeriv (toPolyG 1)` whose fraction-field extension realizes `towerDerivQFunNZG [1]`. -/
noncomputable def baseDerivQ : Derivation ℤ (CFieldSpec.K ℚ)[X] (CFieldSpec.K ℚ)[X] :=
  Differential.implicitDeriv (CPolyG.toPolyG ([CField.one] : CPolyG ℚ))

/-- `CDiffFieldSpec (QFunNZG ℚ)` using `fractionFieldDifferential baseDerivQ` and `toQFunNZG_towerDerivQFunNZG [1]`. -/
noncomputable instance instCDiffFieldSpecQFunNZG : CDiffFieldSpec (QFunNZG ℚ) where
  diffK := fractionFieldDifferential baseDerivQ
  toK_cderiv a := by
    show toQFunNZG (towerDerivQFunNZG [CField.one] a)
      = @Differential.deriv _ _ (fractionFieldDifferential baseDerivQ) (toQFunNZG a)
    rw [toQFunNZG_towerDerivQFunNZG [CField.one] a]
    rfl


end DeepWiki.SymbolicIntegration
