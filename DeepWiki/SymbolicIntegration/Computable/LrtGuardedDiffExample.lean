import DeepWiki.SymbolicIntegration.Computable.LrtGuarded
import DeepWiki.SymbolicIntegration.Computable.LiouvilleCompleteness
import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFF

/-! # The integrability guard, validated non-trivially over a differential tower

Over `ℚ` the guard `cResidueConstantGuardG` passes vacuously (`D ≡ 0`, so every residue is a constant). These
`native_decide` checks run it over `ℚ(x)(log x)` — base derivation `d/dx`, monomial `t = log x` with
`Dt = 1/x` (`gcInvX`) — where it genuinely *discriminates* integrable from non-integrable reduced parts by
residue-constancy. The two examples are the decisive validation that the decision procedure works. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-- **The guard DECLINES `∫1/log x`.** For the reduced part `1/t` (`a = 1`, `d = t`) over `ℚ(x)(log x)`, the
residue is `x` — non-constant (`d/dx x = 1 ≠ 0`) — so the monic residue resultant has a non-constant
coefficient and the guard returns `false`, correctly refusing the non-elementary logarithmic integral
`∫1/log x = Li(x)`. -/
theorem cResidueConstantGuardG_declines_invLog :
    cResidueConstantGuardG ([BenchG.gcInvX] : CPolyG (QFunNZG ℚ))
      [CField.one] [CField.zero, CField.one] = false := by native_decide

/-- **The guard ACCEPTS `∫(1/x)/log x = log(log x)`.** Same tower, but `a = 1/x`: the residue is the constant
`1`. The raw resultant carries a non-constant `1/x` scaling factor, which is exactly why the guard
monic-normalizes before testing `D = 0`; after normalization the residue polynomial is `z − 1` (constant
coefficients), so the guard returns `true`, correctly accepting the elementary integral. -/
theorem cResidueConstantGuardG_accepts_invXinvLog :
    cResidueConstantGuardG ([BenchG.gcInvX] : CPolyG (QFunNZG ℚ))
      [BenchG.gcInvX] [CField.zero, CField.one] = true := by native_decide

/-- **End-to-end completeness on a concrete integrand (modulo the Liouville frontier): `∫1/log x` is not
genuinely elementary integrable.** Feeds the guard demo `cResidueConstantGuardG_declines_invLog` into the
completeness certificate `not_isElementaryIntegrableGenuine`: over `ℚ(x)(log x)`, since the root-free guard
declines `1/t` (residue `x` non-constant), any `LiouvilleFrontier` instance certifies it non-integrable. The
whole pipeline — decision procedure ⟹ non-integrability — realized on the non-elementary `Li(x)`. -/
theorem not_genuinelyIntegrable_invLog [Algebra ℚ (CFieldSpec.K (QFunNZG ℚ))]
    [LiouvilleFrontier (QFunNZG ℚ)] :
    ¬ IsElementaryIntegrableGenuineG ([BenchG.gcInvX] : CPolyG (QFunNZG ℚ))
      [CField.one] [CField.zero, CField.one] :=
  not_isElementaryIntegrableGenuine _ _ _
    (fun h => absurd ((cisZeroG_iff _).mpr h) (by native_decide))
    cResidueConstantGuardG_declines_invLog

end DeepWiki.SymbolicIntegration
