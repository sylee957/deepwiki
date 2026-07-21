import DeepWiki.CAlgebra.Integrate.Results
import DeepWiki.CAlgebra.Resultant
import DeepWiki.CAlgebra.Diff.Frac

/-! # The computable derivative of the integral records

The records' `deriv` — a computable, `DenseFrac`-valued derivative. The root-sum
derivative `∑_{Q(α)=0} α · Sₓ(α,x)/S(α,x)` is computed by **resultant deformation**:
for `F(t) = Res_z(Q, S + t·z·Sₓ)` the product formula gives
`F(t) = c·∏_α (S(α) + t·α·Sₓ(α))`, so the sum is `F.coeff 1 / F.coeff 0`. The `RatFunc`
reading is `toRatFunc res.deriv`, characterized by the squares in the spec files; see
`docs/derivdata-rootsum-derivative.md`. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

open scoped Differential FormalDiff

/-- **The root-sum derivative** `∑_{Q(α)=0} α · Sₓ(α,x)/S(α,x)`, by resultant
deformation: `F(t) = Res_z(Q, S + t·z·Sₓ)` over `K[x][t]`, answer `F₁/F₀`. -/
def rootSumDeriv (Q : DensePoly R) (S : DensePoly (DensePoly R)) : DenseFrac R :=
  -- coefficient ring `C = K[x][t]` (outer `t`, inner `x`); resultant args are `z`-polys
  let Sz := zSwap S
  let Sxz := zSwap (S′)
  let QC : DensePoly (DensePoly (DensePoly R)) :=
    DensePoly.ofList (Q.coeffs.map fun r => DensePoly.C (DensePoly.C r))
  let SzC : DensePoly (DensePoly (DensePoly R)) :=
    DensePoly.ofList (Sz.coeffs.map fun c => DensePoly.C c)
  let SxzT : DensePoly (DensePoly (DensePoly R)) :=
    DensePoly.ofList (Sxz.coeffs.map fun c => DensePoly.ofList [0, c])
  let A := SzC + DensePoly.ofList [0, 1] * SxzT
  let F := DensePolyResultant.resultant QC A
  DenseFrac.normalize (F.coeff 1) (F.coeff 0)

end DensePoly

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

open scoped Differential FormalDiff

/-- The computable derivative of the log data: the sum of the pair root-sum
derivatives. -/
def ResultLrt.deriv (res : ResultLrt R) : DenseFrac R :=
  (res.terms.map (fun QS => rootSumDeriv QS.1 QS.2)).sum

/-- **The computable derivative of a rational integral**: engine derivatives of the
rational and polynomial parts plus the root-sum derivatives of the log data — a
canonical fraction, so `(ratIntegrate f).deriv = f` is decidable. -/
def ResultRatIntegral.deriv (res : ResultRatIntegral R) : DenseFrac R :=
  res.rational′ + DenseFrac.ofPoly (res.poly′) + res.logs.deriv

end DensePoly

end DeepWiki.CAlgebra
