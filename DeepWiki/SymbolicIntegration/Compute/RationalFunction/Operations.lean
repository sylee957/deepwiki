import DeepWiki.SymbolicIntegration.Compute.Hermite
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative

/-! # Computable rational-function operations

Executable operations on `QFun = DensePoly ℚ × DensePoly ℚ` representing rational functions over `ℚ(x)`.
-/

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Lowest-terms normalization on `QFun` -/

/-- Lowest-terms reduction `qnorm (a, b) = (a/q, b/q)` (`q = gcd(a, b)`) scaled so the
denominator is monic; the zero fraction stays `QFun.qzero`. -/
def qnorm (x : QFun ℚ) : QFun ℚ :=
  let (a, b) := x
  if cisZero a then QFun.qzero
  else
    let q := (DensePoly.cgcdWf a b).1
    let a' := DensePoly.cdivWf a q
    let b' := DensePoly.cdivWf b q
    let s := (clead b')⁻¹
    (cscale s a', cscale s b')

end DeepWiki.SymbolicIntegration.Compute
