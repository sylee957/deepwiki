import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFFCorrect
import DeepWiki.SymbolicIntegration.Computable.Tower.Integrate
import DeepWiki.SymbolicIntegration.Computable.CanonicalFieldIdentity

/-! # `CDiffFieldSpec (QFunNZG ℚ)` differential-spec bridge for the `ℚ(x)` carrier.
Noncomputable base derivation `baseDerivQ` on `ℚ[X]` and its fraction-field extension on `RatFunc ℚ`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The differential-spec bridge `CDiffFieldSpec (QFunNZG ℚ)` -/

/-- The base derivation `implicitDeriv (toPolyG 1) : Derivation ℤ ℚ[X] ℚ[X]` (`d/dx`), whose
fraction-field extension realizes `towerDerivQFunNZG [1]` on `RatFunc ℚ`. -/
noncomputable def baseDerivQ : Derivation ℤ (CFieldSpec.K ℚ)[X] (CFieldSpec.K ℚ)[X] :=
  Differential.implicitDeriv (CPolyG.toPolyG ([CField.one] : CPolyG ℚ))

/-- `CDiffFieldSpec (QFunNZG ℚ)`: the differential-spec bridge for the `ℚ(x)` carrier, with Mathlib
derivation `fractionFieldDifferential baseDerivQ` on `RatFunc ℚ` and intertwining `toK_cderiv` from
`toQFunNZG_towerDerivQFunNZG [1]`. Noncomputable. -/
noncomputable instance instCDiffFieldSpecQFunNZG : CDiffFieldSpec (QFunNZG ℚ) where
  diffK := fractionFieldDifferential baseDerivQ
  toK_cderiv a := by
    show toQFunNZG (towerDerivQFunNZG [CField.one] a)
      = @Differential.deriv _ _ (fractionFieldDifferential baseDerivQ) (toQFunNZG a)
    rw [toQFunNZG_towerDerivQFunNZG [CField.one] a]
    rfl


end DeepWiki.SymbolicIntegration
