import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFFCorrect
import DeepWiki.SymbolicIntegration.Computable.Tower.Integrate
import DeepWiki.SymbolicIntegration.Computable.CanonicalFieldIdentity

/-! # The differential-spec bridge `CDiffFieldSpec (QFunNZG ℚ)` at the level-1 carrier

The level-1 differential-spec bridge for the generic ℚ(x) carrier `QFunNZG ℚ = Frac(ℚ[x])`: the base
derivation `baseDerivQ = implicitDeriv (toPolyG 1)` on `ℚ[X]` and the `CDiffFieldSpec (QFunNZG ℚ)` instance
whose Mathlib derivation on `RatFunc ℚ` is `fractionFieldDifferential baseDerivQ`, with the intertwining
`toK_cderiv` supplied by the abstract `toQFunNZG_towerDerivQFunNZG [1]`. Noncomputable (routes through
`RatFunc`); only the correctness layer depends on it, the engine stays computable. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The differential-spec bridge `CDiffFieldSpec (QFunNZG ℚ)` (the genuine new ingredient)

The step proof identifies the second argument of `cgcdFFCore p (cmonomialDeriv Dt p)` with `implicitDeriv
(toPolyG Dt) (toPolyG p)` through `toPolyG_cmonomialDeriv`, which needs `[CDiffFieldSpec α]`. No
`CDiffFieldSpec (QFunNZG ℚ)` instance existed (the tower derivation's *spec* bridge — that the computable
`towerDerivQFunNZG [1]` agrees with a Mathlib `Differential` on `RatFunc ℚ` — was never built). We build it
here: the genuine Mathlib derivation is `fractionFieldDifferential (implicitDeriv (toPolyG 1))` — the
fraction-field derivation of the base `implicitDeriv (toPolyG ([1] : CPolyG ℚ))` on `ℚ[X]` — and
`toK_cderiv` is *exactly* the existing abstract bridge `toQFunNZG_towerDerivQFunNZG [1]` (no extra
agreement proof). This is the level-1 `CDiffFieldSpec (QFunNZG ℚ)` differential-spec bridge. -/

/-- **The base derivation `implicitDeriv (toPolyG 1)` on `(CFieldSpec.K ℚ)[X] = ℚ[X]`** (`= d/dx`, since
the base `Differential ℚ` is the zero derivation of constants): the `Derivation ℤ ℚ[X] ℚ[X]` whose
fraction-field extension is the `d/dx` derivation realizing the level-1 tower derivation
`towerDerivQFunNZG [1]` on `RatFunc ℚ`. -/
noncomputable def baseDerivQ : Derivation ℤ (CFieldSpec.K ℚ)[X] (CFieldSpec.K ℚ)[X] :=
  Differential.implicitDeriv (CPolyG.toPolyG ([CField.one] : CPolyG ℚ))

/-- **`CDiffFieldSpec (QFunNZG ℚ)`** (the genuine new ingredient): the differential-spec bridge for the
generic ℚ(x) carrier. The Mathlib derivation on `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ` is
`fractionFieldDifferential baseDerivQ` (the fraction-field extension of `implicitDeriv (toPolyG 1)` on
`ℚ[X]`), and the intertwining `toK_cderiv` — `toQFunNZG (towerDerivQFunNZG [1] a) = (toQFunNZG a)′` — is
exactly the abstract bridge `toQFunNZG_towerDerivQFunNZG [1]` (`ComputableTowerDeriv`). Noncomputable
(routes through `RatFunc`), but only the correctness layer depends on it; the engine stays computable. The
level-1 ℚ(x) differential-spec bridge. -/
noncomputable instance instCDiffFieldSpecQFunNZG : CDiffFieldSpec (QFunNZG ℚ) where
  diffK := fractionFieldDifferential baseDerivQ
  toK_cderiv a := by
    show toQFunNZG (towerDerivQFunNZG [CField.one] a)
      = @Differential.deriv _ _ (fractionFieldDifferential baseDerivQ) (toQFunNZG a)
    rw [toQFunNZG_towerDerivQFunNZG [CField.one] a]
    rfl


end DeepWiki.SymbolicIntegration
