import DeepWiki.SymbolicIntegration.Computable.PolyPartTower

/-! # Polynomial-part tower examples

Executable checks for polynomial reduction and primitive-case integration over `ℚ(x)[t]`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Validation helpers -/

/-- A ℚ constant `n` as a `QFunNZG ℚ` element. -/
def qConstG (n : ℚ) : QFunNZG ℚ := ⟨([n], [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩

/-- A ℚ(x) fraction `num/den` as a `QFunNZG ℚ` element. -/
def qFracG (num den : List ℚ) (h : CPolyG.cisZeroG den = false := by native_decide) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-! ### Primitive case `t = log x`, `Dt = 1/x` -/

/-- Validation monomial derivative for the primitive case: `Dt = 1/x`. -/
def primitivePolyIntegrateExampleDt : CPolyG (QFunNZG ℚ) :=
  [qFracG [1] [0, 1]]

/-- The polynomial part `p = (1/x)·t²` over `ℚ(x)[t]`. -/
def primitivePolyIntegrateExampleP : CPolyG (QFunNZG ℚ) :=
  [qConstG 0, qConstG 0, qFracG [1] [0, 1]]

/-- `cPrimitivePolyIntegrate` satisfies `D(q) + rem = p` for the primitive monomial `t = log x`. -/
theorem primitivePolyIntegrate_example :
    (let res := CPolyG.cPrimitivePolyIntegrate primitivePolyIntegrateExampleDt 8
        primitivePolyIntegrateExampleP
      let q := res.1
      let rem := res.2
      let Dq := CPolyG.cmonomialDeriv primitivePolyIntegrateExampleDt q
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.caddG Dq rem) primitivePolyIntegrateExampleP)) = true := by
  native_decide

/-! ### Nonlinear case `t = tan x`, `Dt = t² + 1` -/

/-- Validation monomial derivative for the nonlinear case: `Dt = t² + 1`. -/
def polyReduceTowerExampleDt : CPolyG (QFunNZG ℚ) := [qConstG 1, qConstG 0, qConstG 1]

/-- The polynomial part `p = t³` over `ℚ(x)[t]`. -/
def polyReduceTowerExampleP : CPolyG (QFunNZG ℚ) := [qConstG 0, qConstG 0, qConstG 0, qConstG 1]

/-- `cPolyReduceTower` satisfies `D(q) + r = p` for the nonlinear monomial `t = tan x`. -/
theorem polyReduceTower_example :
    (let res := CPolyG.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP
      let q := res.1
      let r := res.2
      let Dq := CPolyG.cmonomialDeriv polyReduceTowerExampleDt q
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.caddG Dq r) polyReduceTowerExampleP)) = true := by
  native_decide

/-- The reduced remainder has `t`-degree `< δ(t)` in the nonlinear example. -/
theorem polyReduceTower_example_remainder_degree :
    CPolyG.cdegG (CPolyG.cPolyReduceTower polyReduceTowerExampleDt 8 polyReduceTowerExampleP).2 = 1 := by
  native_decide

#print axioms polyReduceTower_example

end DeepWiki.SymbolicIntegration
