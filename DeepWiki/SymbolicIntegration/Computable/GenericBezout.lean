import DeepWiki.SymbolicIntegration.Computable.GenericPolyEngine

/-! # Generic Bézout cofactors, resultant, and Lagrange interpolation

Natural-number casts (`cnatCastG`), field powers (`cfpow`), and Lagrange interpolation
(`clagNumG`/`cinterpolateG`), all generic over `[CField α]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-- Natural number as a field element: `cnatCastG k = 1 + 1 + … + 1` (`k` times), built from
`CField.add`/`CField.one`; `[CField α]`-only. -/
def cnatCastG : ℕ → α
  | 0 => CField.zero
  | k + 1 => CField.add CField.one (cnatCastG k)

/-- Generic power of a field element: `cfpow c n = cⁿ` over `[CField α]` (by `ℕ`-recursion). -/
def cfpow (c : α) : ℕ → α
  | 0 => CField.one
  | n + 1 => CField.mul c (cfpow c n)

/-- Generic Lagrange basis numerator `clagNumG zs = ∏ⱼ (z − zⱼ)` over abscissas `zs`, built from the
degree-1 factors `[−zⱼ, 1]` via `cmulG`. -/
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
