import DeepWiki.SymbolicIntegration.Engine.PolyPartTower

/-! # Polynomial-part tower examples

Executable checks for polynomial reduction and primitive-case integration over `ℚ(x)[t]`. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

/-! ### Example helpers -/

/-- A ℚ constant `n` as a `QFunNZG ℚ` element. -/
def qConstG (n : ℚ) : QFunNZG ℚ := ⟨([n], [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩

/-- A ℚ(x) fraction `num/den` as a `QFunNZG ℚ` element. -/
def qFracG (num den : List ℚ) (h : CPoly.cisZeroG den = false := by native_decide) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-! ### Primitive case `t = log x`, `Dt = 1/x` -/

/-- Example monomial derivative for the primitive case: `Dt = 1/x`. -/
def primitivePolyIntegrateExampleDt : CPoly (QFunNZG ℚ) :=
  [qFracG [1] [0, 1]]

/-- The polynomial part `p = (1/x)·t²` over `ℚ(x)[t]`. -/
def primitivePolyIntegrateExampleP : CPoly (QFunNZG ℚ) :=
  [qConstG 0, qConstG 0, qFracG [1] [0, 1]]

/-- `cPrimitivePolyIntegrate` satisfies `D(q) + rem = p` for the primitive monomial `t = log x`. -/
theorem primitivePolyIntegrate_example :
    (let res := CPoly.cPrimitivePolyIntegrate primitivePolyIntegrateExampleDt 8
        primitivePolyIntegrateExampleP
      let q := res.1
      let rem := res.2
      let Dq := CPoly.cmonomialDeriv primitivePolyIntegrateExampleDt q
      CPoly.cisZeroG (CPoly.csubG (CPoly.caddG Dq rem) primitivePolyIntegrateExampleP)) = true := by
  native_decide

/-! ### Nonlinear case `t = tan x`, `Dt = t² + 1` -/

/-- Example monomial derivative for the nonlinear case: `Dt = t² + 1`. -/
def polyReduceTowerExampleDt : CPoly (QFunNZG ℚ) := [qConstG 1, qConstG 0, qConstG 1]

/-- The polynomial part `p = t³` over `ℚ(x)[t]`. -/
def polyReduceTowerExampleP : CPoly (QFunNZG ℚ) := [qConstG 0, qConstG 0, qConstG 0, qConstG 1]

/-- `cPolyReduceTower` satisfies `D(q) + r = p` for the nonlinear monomial `t = tan x`. -/
theorem polyReduceTower_example :
    (let res := CPoly.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP
      let q := res.1
      let r := res.2
      let Dq := CPoly.cmonomialDeriv polyReduceTowerExampleDt q
      CPoly.cisZeroG (CPoly.csubG (CPoly.caddG Dq r) polyReduceTowerExampleP)) = true := by
  native_decide

/-- The reduced remainder has `t`-degree `< δ(t)` in the nonlinear example. -/
theorem polyReduceTower_example_remainder_degree :
    CPoly.cdegG (CPoly.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP).2 = 1 := by
  native_decide

end DeepWiki.SymbolicIntegration
