import DeepWiki.SymbolicIntegration.Compute.Hermite
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative

/-! # Computable rational-function operations

Executable operations on `QFun = CPolyQ × CPolyQ` representing rational functions over `ℚ(x)`.
-/

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Computable field operations on `QFun` -/

/-- One rational function `1/1`. -/
def qone : QFun := ([1], [1])

/-- Negation of a rational function `−(a/b) = (−a)/b`. -/
def qneg (x : QFun) : QFun := (cneg x.1, x.2)

/-- Subtraction of rational functions `a/b − c/d = (a·d − c·b)/(b·d)`. -/
def qsub (x y : QFun) : QFun := qadd x (qneg y)

/-- Multiplication of rational functions `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def qmul (x y : QFun) : QFun := (cmul x.1 y.1, cmul x.2 y.2)

/-- Inverse of a rational function `(a/b)⁻¹ = b/a`; the zero fraction inverts to `qzero` (`0⁻¹ = 0`). -/
def qinv (x : QFun) : QFun := if cisZero x.1 then qzero else (x.2, x.1)

/-- Division of rational functions `(a/b)/(c/d) = (a·d)/(b·c)`. -/
def qdiv (x y : QFun) : QFun := qmul x (qinv y)

/-- Power of a rational function `(a/b)^n` by `ℕ`-recursion. -/
def qpow (x : QFun) : ℕ → QFun
  | 0 => qone
  | n + 1 => qmul x (qpow x n)

/-- Derivative `d/dx` of a rational function `D(a/b) = (a'·b − a·b')/b²` (quotient rule). -/
def qderiv (x : QFun) : QFun :=
  let (a, b) := x
  (csub (cmul (cderiv a) b) (cmul a (cderiv b)), cmul b b)

/-- Decidable equality of rational functions by cross-multiplication: `true` iff
`a₁·b₂ − a₂·b₁ = 0`. -/
def qeq (x y : QFun) : Bool :=
  cisZero (csub (cmul x.1 y.2) (cmul y.1 x.2))

/-- Lowest-terms reduction `qnorm fuel (a, b) = (a/q, b/q)` (`q = gcd(a, b)`) scaled so the
denominator is monic; the zero fraction stays `qzero`. -/
def qnorm (fuel : ℕ) (x : QFun) : QFun :=
  let (a, b) := x
  if cisZero a then qzero
  else
    let q := (cgcdExt fuel a b).1
    let a' := cdiv fuel a q
    let b' := cdiv fuel b q
    let s := (clead b')⁻¹
    (cscale s a', cscale s b')

end DeepWiki.SymbolicIntegration.Compute
