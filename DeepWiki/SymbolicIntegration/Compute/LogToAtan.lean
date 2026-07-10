import DeepWiki.SymbolicIntegration.RiobooLogToAtan
import DeepWiki.ComputableAlgebra.PolyReprDense
import DeepWiki.ComputableAlgebra.PolyReprDivision
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Computable `LogToAtan` over `ℚ`
An executable rendering of the `LogToAtan` algorithm on the dense coefficient carrier
`DensePoly ℚ := List ℚ`, reusing its canonical operations and `toPoly` bridge to the `ℚ[X]` theory. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

-- The concrete `ℚ` engine re-exports the canonical dense operations and denotation; only the
-- genuinely `LogToAtan`-specific fuel-bounded algorithms are defined here.
export DensePoly
  (cnorm cadd cneg csub cscale cshift cmul clead cisZero cdeg cderiv cmonic)

/-- The canonical dense denotation with the concrete codomain fixed to `ℚ[X]`. -/
noncomputable def toPoly (p : DensePoly ℚ) : ℚ[X] := DensePoly.toPoly p

/-- The concrete-codomain denotation agrees with the canonical dense denotation. -/
@[simp] theorem toPoly_eq_dense (p : DensePoly ℚ) : toPoly p = DensePoly.toPoly p := rfl

/-- Euclidean division of `DensePoly ℚ`s, fuel-bounded: `cdivmod fuel p q = (quotient, remainder)` with
`p = quotient · q + remainder`, `deg remainder < deg q`. -/
def cdivmod : ℕ → DensePoly ℚ → DensePoly ℚ → DensePoly ℚ × DensePoly ℚ
  | 0, p, _ => ([], cnorm p)
  | fuel + 1, p, q =>
    let p := cnorm p
    let q := cnorm q
    if cisZero q then ([], [])
    else if p.length < q.length then ([], p)
    else
      let c := clead p / clead q
      let k := p.length - q.length
      let term := cshift k [c]
      let p' := cnorm (csub p (cmul term q))
      let (quo, rem) := cdivmod fuel p' q
      (cadd term quo, rem)

/-- Quotient of `DensePoly ℚ` Euclidean division (`cdivmod`'s first component). -/
def cdiv (fuel : ℕ) (p q : DensePoly ℚ) : DensePoly ℚ := (cdivmod fuel p q).1

/-- Remainder of `DensePoly ℚ` Euclidean division (`cdivmod`'s second component). -/
def cmod (fuel : ℕ) (p q : DensePoly ℚ) : DensePoly ℚ := (cdivmod fuel p q).2

/-- Extended Euclidean algorithm on `DensePoly ℚ`s, fuel-bounded: `cgcdExt fuel a b = (g, s, t)` with
`s · a + t · b = g` and `g = gcd(a, b)`. -/
def cgcdExt : ℕ → DensePoly ℚ → DensePoly ℚ → DensePoly ℚ × DensePoly ℚ × DensePoly ℚ
  | 0, a, _ => (cnorm a, [1], [])
  | fuel + 1, a, b =>
    if cisZero b then (cnorm a, [1], [])
    else
      let (q, r) := cdivmod (fuel + 1) a b
      let (g, s, t) := cgcdExt fuel b r
      -- `s·b + t·r = g`, `r = a − q·b` ⇒ `t·a + (s − t·q)·b = g`
      (g, t, csub s (cmul t q))

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
  native_decide

/-! ### Agreement with the `ℚ[X]`-level `logToAtanAux`
The cofactor Bézout identity `B·D − A·C = G` under `DensePoly.toPoly` is proven in
`logToAtan_cofactor_bezout` (`Correctness`), so the arctan argument fractions
`(A·D + B·C)/G` are well-defined. -/

end Compute

end DeepWiki.SymbolicIntegration
