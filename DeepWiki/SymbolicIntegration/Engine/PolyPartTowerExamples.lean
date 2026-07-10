import DeepWiki.SymbolicIntegration.Engine.PolyPartTower

/-! # Polynomial-part tower examples

Executable checks for polynomial reduction and primitive-case integration over `ℚ(x)[t]`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-! ### Primitive case `t = log x`, `Dt = 1/x` -/

/-- Example monomial derivative for the primitive case: `Dt = 1/x`. -/
def primitivePolyIntegrateExampleDt : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofFraction [1] [0, 1] (by ccompute)]

/-- The polynomial part `p = (1/x)·t²` over `ℚ(x)[t]`. -/
def primitivePolyIntegrateExampleP : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofScalar 0, CFrac.ofScalar 0, CFrac.ofFraction [1] [0, 1] (by ccompute)]

/-- `cPrimitivePolyIntegrate` satisfies `D(q) + rem = p` for the primitive monomial `t = log x`. -/
theorem primitivePolyIntegrate_example :
    (let res := DensePoly.cPrimitivePolyIntegrate primitivePolyIntegrateExampleDt 8
        primitivePolyIntegrateExampleP
      let q := res.1
      let rem := res.2
      let Dq := DensePoly.cmonomialDeriv primitivePolyIntegrateExampleDt q
      DensePoly.cisZero (DensePoly.csub (DensePoly.cadd Dq rem) primitivePolyIntegrateExampleP)) = true := by
  native_decide

/-! ### Nonlinear case `t = tan x`, `Dt = t² + 1` -/

/-- Example monomial derivative for the nonlinear case: `Dt = t² + 1`. -/
def polyReduceTowerExampleDt : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]

/-- The polynomial part `p = t³` over `ℚ(x)[t]`. -/
def polyReduceTowerExampleP : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 0, CFrac.ofScalar 0, CFrac.ofScalar 1]

/-- `cPolyReduceTower` satisfies `D(q) + r = p` for the nonlinear monomial `t = tan x`. -/
theorem polyReduceTower_example :
    (let res := DensePoly.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP
      let q := res.1
      let r := res.2
      let Dq := DensePoly.cmonomialDeriv polyReduceTowerExampleDt q
      DensePoly.cisZero (DensePoly.csub (DensePoly.cadd Dq r) polyReduceTowerExampleP)) = true := by
  native_decide

/-- The reduced remainder has `t`-degree `< δ(t)` in the nonlinear example. -/
theorem polyReduceTower_example_remainder_degree :
    DensePoly.cdeg (DensePoly.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP).2 = 1 := by
  native_decide

end DeepWiki.SymbolicIntegration
