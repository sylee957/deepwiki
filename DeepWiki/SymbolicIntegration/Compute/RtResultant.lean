import DeepWiki.SymbolicIntegration.Compute.LogToAtan
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtResultant
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # Computable Rothstein–Trager resultant over `ℚ`
A `#eval`-able rendering of the resultant `R(t) = res_x(D, A − t·D')` on the carrier
`DensePoly ℚ := List ℚ`: a univariate `cresultant` via the Euclidean polynomial-remainder-sequence, then
`R(t)` recovered by evaluation and Lagrange interpolation (`cinterpolate`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### Computable univariate resultant on `DensePoly ℚ` (Euclidean-PRS route) -/

/-- Computable univariate resultant `cresultant fuel p q = res_x(p, q) ∈ ℚ`, fuel-bounded, via the
Euclidean polynomial-remainder-sequence identity
`res(p,q) = (−1)^(deg p·deg q)·lc(q)^(deg p − deg r)·res(q, r)` with `r = p mod q`. -/
def cresultant (_fuel : ℕ) (p q : DensePoly ℚ) : ℚ := DensePoly.cresultantWf p q

/-! ### Computable Lagrange interpolation on `DensePoly ℚ` -/

/-- Constant `DensePoly ℚ` `cC c = [c]`, normalized to `[]` when `c = 0`. -/
def cC (c : ℚ) : DensePoly ℚ := cnorm [c]

/-- Lagrange basis numerator `∏_{j} (x − xⱼ)` over the sample abscissas `xs`. -/
def clagNum : List ℚ → DensePoly ℚ
  | [] => [1]
  | x :: xs => cmul [(-x), 1] (clagNum xs)

/-- Lagrange interpolation `cinterpolate pts = R(t)` with `R(xₖ) = yₖ` for each `(xₖ, yₖ) ∈ pts`
(distinct abscissas over `ℚ`): `∑ₖ yₖ · ∏_{j≠k}(t − xⱼ)/(xₖ − xⱼ)`. -/
def cinterpolate (pts : List (ℚ × ℚ)) : DensePoly ℚ :=
  let xs := pts.map Prod.fst
  let term : ℚ × ℚ → DensePoly ℚ := fun (xk, yk) =>
    let others := xs.filter (· != xk)
    let num := clagNum others
    let denom := others.foldl (fun acc xj => acc * (xk - xj)) 1
    cscale (yk / denom) num
  cnorm (pts.foldl (fun acc p => cadd acc (term p)) [])

/-! ### The Rothstein–Trager resultant `R(t) = res_x(D, A − t·D')` -/

/-- Computable Rothstein–Trager resultant `rtResultantCompute fuel A D = R(t) = res_x(D, A − t·D')`,
returned as a `DensePoly ℚ` in `t`, computed by sampling and Lagrange interpolation. -/
def rtResultantCompute (fuel : ℕ) (A D : DensePoly ℚ) : DensePoly ℚ :=
  let D' := cderiv D
  let n := cdeg D  -- `deg_t R ≤ deg_x D = n`, so `n + 1` sample points determine `R`.
  let pts : List (ℚ × ℚ) := (List.range (n + 1)).map (fun k =>
    let a : ℚ := (k : ℚ)
    let Aa := csub A (cscale a D')
    (a, cresultant fuel D Aa))
  cinterpolate pts

/-! ### Squarefree (primitive) part -/

/-- Squarefree part of a `DensePoly ℚ` over `ℚ`, made monic: `csqfreePart fuel p = monic(p / gcd(p, p'))`,
the radical of `p`. -/
def csqfreePart (_fuel : ℕ) (p : DensePoly ℚ) : DensePoly ℚ :=
  let p := cnorm p
  let (g, _, _) := DensePoly.cgcdWf p (cderiv p)
  cmonic (DensePoly.cdivWf p g)

/-! ### Bridge back to `ℚ[X]`

`toPoly (cresultant …)` agrees with Mathlib's `Polynomial.resultant`, and
`toPoly (rtResultantCompute …)` agrees with the noncomputable `rtResultant`, in the correctness
files for those algorithms. -/

end Compute

end DeepWiki.SymbolicIntegration
