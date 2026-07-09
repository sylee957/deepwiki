import DeepWiki.SymbolicIntegration.Engine.LrtGuarded
import DeepWiki.SymbolicIntegration.Engine.LrtCompleteness
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFF

/-! # The integrability guard over a differential tower

Over `ℚ` the guard `cResidueConstantGuard` passes vacuously (`D ≡ 0`, so every residue is a constant). These
`native_decide` checks run it over `ℚ(x)(log x)`, with base derivation `d/dx` and monomial `t = log x`,
where it discriminates integrable from non-integrable reduced parts by residue-constancy. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

/-- The residue-constant guard declines the reduced part `1/t` over `ℚ(x)(log x)`. -/
theorem cResidueConstantGuardG_declines_invLog :
    cResidueConstantGuard ([BenchG.gcInvX] : CPoly (CFrac ℚ))
      [CField.one] [CField.zero, CField.one] = false := by native_decide

/-- The residue-constant guard accepts `(1/x)/t` over `ℚ(x)(log x)`. -/
theorem cResidueConstantGuardG_accepts_invXinvLog :
    cResidueConstantGuard ([BenchG.gcInvX] : CPoly (CFrac ℚ))
      [BenchG.gcInvX] [CField.zero, CField.one] = true := by native_decide

/-- If the LRT Liouville frontier holds, `1/t` over `ℚ(x)(log x)` is not genuinely elementary integrable. -/
theorem not_genuinelyIntegrableLrt_invLog [Algebra ℚ (CFieldSpec.K (CFrac ℚ))]
    [LrtLiouvilleFrontier (CFrac ℚ)] :
    ¬ IsElementaryIntegrableGenuineLrt ([BenchG.gcInvX] : CPoly (CFrac ℚ))
      [CField.one] [CField.zero, CField.one] :=
  not_isElementaryIntegrableGenuineLrt _ _ _
    (fun h => absurd ((cisZeroG_iff _).mpr h) (by native_decide))
    cResidueConstantGuardG_declines_invLog

end DeepWiki.SymbolicIntegration
