import DeepWiki.SymbolicIntegration.Computable.GenericPolyEngine

/-! # Generic Bézout cofactors, resultant, and Lagrange interpolation

Natural-number casts (`cnatCastG`) and Lagrange interpolation
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

/-- `toK (cnatCastG k) = (k : K)`: the computable natural cast reads as the genuine one. -/
@[denote] theorem toK_cnatCastG [CFieldSpec α] (k : ℕ) :
    CFieldSpec.toK (cnatCastG k : α) = (k : CFieldSpec.K α) := by
  induction k with
  | zero => rw [cnatCastG, CFieldSpec.toK_zero, Nat.cast_zero]
  | succ n ih => rw [cnatCastG, CFieldSpec.toK_add, CFieldSpec.toK_one, ih, Nat.cast_succ, add_comm]

/-- Generic Lagrange basis numerator `clagNumG zs = ∏ⱼ (z − zⱼ)` over abscissas `zs`, built from the
degree-1 factors `[−zⱼ, 1]` via `cmulG`. -/
def clagNumG : List α → CPolyG α
  | [] => [CField.one]
  | z :: zs => cmulG [CField.neg z, CField.one] (clagNumG zs)

/-- `toPolyG (clagNumG zs) = ∏ (X − C (toK zⱼ))`: the basis numerator as a product of linear factors. -/
theorem toPolyG_clagNumG [CFieldSpec α] (zs : List α) :
    toPolyG (clagNumG zs) = (zs.map (fun z => Polynomial.X - Polynomial.C (CFieldSpec.toK z))).prod := by
  induction zs with
  | nil => simp [clagNumG, toPolyG_cons, CFieldSpec.toK_one]
  | cons z zs ih =>
    rw [clagNumG]
    simp only [denote, ih, List.map_cons, List.prod_cons]
    simp only [map_neg, map_one, mul_zero, add_zero]
    ring

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
