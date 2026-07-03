import DeepWiki.SymbolicIntegration.Computable.GenericPolyEngine

/-! # Generic Bézout cofactors, resultant, and Lagrange interpolation

Bézout cofactors (`cbezoutOne`), natural-number casts (`cnatCastG`), field powers (`cfpow`), the
Euclidean-PRS resultant (`cresultantG`), and Lagrange interpolation (`clagNumG`/`cinterpolateG`),
all generic over `[CField α]` so the tower engine and `native_decide` validations can reuse them at
any carrier level. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The computable extended-Euclidean Bézout split

`cbezoutOne` extracts the rescaled cofactors from `cgcdExtG`. -/

/-- Natural number as a field element: `cnatCastG k = 1 + 1 + … + 1` (`k` times), built only from
`CField.add`/`CField.one`. Needs only `[CField α]`, so it reduces under `native_decide`; used to
form the `−a/j` scaling in the Hermite inner loop. (`ComputableFieldGcd.nsmulG` carries a
`[CFieldSpec α]` binder and so does not reduce in the bridge-free engine context.) -/
def cnatCastG : ℕ → α
  | 0 => CField.zero
  | k + 1 => CField.add CField.one (cnatCastG k)

/-! ### Generic univariate resultant over a `CField` (Euclidean-PRS route)

`cresultantG fuel p q = res(p, q) ∈ α`, the generic mirror of `Compute.cresultant` over any
`[CField α]` (ℚ-arithmetic replaced by `CField`/`CPolyG` ops): the Euclidean polynomial-remainder
sequence identity `res(p, q) = (−1)^(deg p·deg q)·lc(q)^(deg p − deg r)·res(q, r)` with `r = p mod q`,
bottoming out at `res(p, c) = c^(deg p)` for a constant `q = c`. Reduces over the tower
(`native_decide`); `fuel ≥ deg p + deg q` is safe. -/

/-- Generic power of a field element: `cfpow c n = cⁿ` over `[CField α]` (by `ℕ`-recursion). -/
def cfpow (c : α) : ℕ → α
  | 0 => CField.one
  | n + 1 => CField.mul c (cfpow c n)

/-! ### Generic Lagrange interpolation over a `CField`

`cinterpolateG pts = R(z) ∈ CPolyG α` with `R(zₖ) = yₖ`, over a field `α`
(distinct abscissas `zₖ`). `∑ₖ yₖ · ∏_{j≠k}(z − zⱼ)/(zₖ − zⱼ)` built with
`cmulG`/`caddG`/`cscaleG` and the `CField.div`/`CField.inv` scalar `1/∏(zₖ − zⱼ)`. -/

/-- Generic Lagrange basis numerator `clagNumG zs = ∏ⱼ (z − zⱼ)` over abscissas `zs` (call with the
`k`-th abscissa removed). Built from the degree-1 factors `[−zⱼ, 1]` via `cmulG`. -/
def clagNumG : List α → CPolyG α
  | [] => [CField.one]
  | z :: zs => cmulG [CField.neg z, CField.one] (clagNumG zs)

/-- Generic Lagrange interpolation `cinterpolateG pts = R(z)` with `R(zₖ) = yₖ` for each
`(zₖ, yₖ) ∈ pts` (distinct abscissas, over the field `α`): `∑ₖ yₖ · ∏_{j≠k}(z − zⱼ)/(zₖ − zⱼ)`. The
scalar `1/∏(zₖ − zⱼ)` is a `CField.inv`; the per-term polynomial uses `cmulG`/`cscaleG`/`caddG`. -/
def cinterpolateG (pts : List (α × α)) : CPolyG α :=
  let zs := pts.map Prod.fst
  let term : α × α → CPolyG α := fun (zk, yk) =>
    let others := zs.filter (fun zj => CField.isZero (CField.sub zj zk) = false)
    let num := clagNumG others
    let denom := others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one
    cscaleG (CField.div yk denom) num
  cnormG (pts.foldl (fun acc p => caddG acc (term p)) [])

end CPolyG

end DeepWiki.SymbolicIntegration
