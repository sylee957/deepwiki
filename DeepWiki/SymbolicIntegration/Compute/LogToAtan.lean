import DeepWiki.SymbolicIntegration.RiobooLogToAtan
import DeepWiki.ComputableAlgebra.PolyReprDense
import DeepWiki.ComputableAlgebra.PolyReprDivision
import DeepWiki.ComputableAlgebra.PolyEuclideanDense

/-! # Computable `LogToAtan` over `ℚ`
An executable rendering of the `LogToAtan` algorithm on the dense coefficient carrier
`DensePoly ℚ := List ℚ`, reusing its canonical operations and denotation into `ℚ[X]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

-- The concrete `ℚ` engine re-exports the canonical dense operations and denotation; polynomial
-- division and extended gcd come from the representation-independent `CPoly` interface.
export DensePoly
  (cnorm cadd cneg csub cscale cshift cmul clead cisZero cdeg cderiv cmonic toPoly)

/-- Computable `LogToAtan` over `DensePoly ℚ`, fuel-bounded: `logToAtanCompute fuel A B` returns the
arctangent arguments as `(numerator, denominator)` pairs. -/
def logToAtanCompute : ℕ → DensePoly ℚ → DensePoly ℚ → List (DensePoly ℚ × DensePoly ℚ)
  | 0, _, _ => []
  | fuel + 1, A, B =>
    let A := cnorm A
    let B := cnorm B
    let divmod := CPoly.cdivmod A B
    if CPoly.cisZero divmod.2 then
      [(cnorm divmod.1, [1])]
    else if A.length < B.length then
      logToAtanCompute fuel (cneg B) A
    else
      -- `CPoly.cgcdExt B (−A) = (G, D, C)` gives `D·B + C·(−A) = G`; normalize the
      -- generic representation at the concrete list-valued boundary.
      let (g, s, t) := CPoly.cgcdExt B (cneg A)
      let D := cnorm s
      let C := cnorm t
      let G := cnorm g
      (cadd (cmul A D) (cmul B C), G) :: logToAtanCompute fuel D C

/-- `x³ − 3x` as a `DensePoly ℚ`: coefficients `[0, −3, 0, 1]`. -/
def cX3m3X : DensePoly ℚ := [0, -3, 0, 1]

/-- `x² − 2` as a `DensePoly ℚ`: coefficients `[-2, 0, 1]`. -/
def cX2m2 : DensePoly ℚ := [-2, 0, 1]

/-- `logToAtanCompute` on `(x³−3x, x²−2)` evaluates to the three `(numerator, denominator)` arctan
arguments `[((−x+3x³−x⁵), −2), ((−x³), −1), ((x), 1)]`. -/
theorem logToAtanCompute_ex281 :
    logToAtanCompute 20 cX3m3X cX2m2
      = [([0, -1, 0, 3, 0, -1], [-2]), ([0, 0, 0, -1], [-1]), ([0, 1], [1])] := by
  ccompute

/-! ### Agreement with the `ℚ[X]`-level `logToAtanAux`
The cofactor Bézout identity `B·D − A·C = G` is the specialization of
`CPoly.toPoly_cgcdExt` to the dense representation, so the arctan argument fractions
`(A·D + B·C)/G` are well-defined without a concrete duplicate Euclidean layer. -/

end Compute

end DeepWiki.SymbolicIntegration
