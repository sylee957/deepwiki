import DeepWiki.SymbolicIntegration.Engine.LrtGuarded
import DeepWiki.SymbolicIntegration.Engine.LrtCompleteness

/-! # The integrability guard over a differential tower

Over `ℚ` the guard `cResidueConstantGuard` passes vacuously (`D ≡ 0`, so every residue is a constant). These
`native_decide` checks run it over `ℚ(x)(log x)`, with base derivation `d/dx` and monomial `t = log x`,
where it discriminates integrable from non-integrable reduced parts by residue-constancy. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- The ℚ(x) coefficient `1/x` (numerator `1`, denominator `x`) as a `CFrac ℚ`, the test coefficient
for the guard checks below. -/
def gcInvX : CFrac ℚ := CFrac.ofFraction [1] [(0 : ℚ), 1]

/-- The residue-constant guard declines the reduced part `1/t` over `ℚ(x)(log x)`. -/
theorem cResidueConstantGuardG_declines_invLog :
    cResidueConstantGuard ([gcInvX] : DensePoly (CFrac ℚ))
      [CCommRing.one] [CCommRing.zero, CCommRing.one] = false := by native_decide

/-- The residue-constant guard accepts `(1/x)/t` over `ℚ(x)(log x)`. -/
theorem cResidueConstantGuardG_accepts_invXinvLog :
    cResidueConstantGuard ([gcInvX] : DensePoly (CFrac ℚ))
      [gcInvX] [CCommRing.zero, CCommRing.one] = true := by native_decide

/-- If the LRT Liouville frontier holds, `1/t` over `ℚ(x)(log x)` is not genuinely elementary integrable. -/
theorem not_genuinelyIntegrableLrt_invLog [Algebra ℚ (CFieldSpec.K (CFrac ℚ))]
    [LrtLiouvilleFrontier (CFrac ℚ)] :
    ¬ IsElementaryIntegrableGenuineLrt ([gcInvX] : DensePoly (CFrac ℚ))
      [CCommRing.one] [CCommRing.zero, CCommRing.one] :=
  not_isElementaryIntegrableGenuineLrt _ _ _
    (fun h => absurd ((cisZeroG_iff _).mpr h) (by native_decide))
    cResidueConstantGuardG_declines_invLog

end DeepWiki.SymbolicIntegration
