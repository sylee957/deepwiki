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

/-- `toK (cnatCastG k) = (k : K)`: the computable natural cast reads as the genuine one. -/
@[denote] theorem toK_cnatCastG [CFieldSpec α] (k : ℕ) :
    CFieldSpec.toK (cnatCastG k : α) = (k : CFieldSpec.K α) := by
  induction k with
  | zero => rw [cnatCastG, CFieldSpec.toK_zero, Nat.cast_zero]
  | succ n ih => rw [cnatCastG, CFieldSpec.toK_add, CFieldSpec.toK_one, ih, Nat.cast_succ, add_comm]

/-- Generic power of a field element: `cfpow c n = cⁿ` over `[CField α]` (by `ℕ`-recursion). -/
def cfpow (c : α) : ℕ → α
  | 0 => CField.one
  | n + 1 => CField.mul c (cfpow c n)

/-- `toK (cfpow c n) = (toK c) ^ n`: generic constant power realizes the `K`-power. -/
@[denote] theorem toK_cfpow [CFieldSpec α] (c : α) (n : ℕ) :
    CFieldSpec.toK (cfpow c n) = (CFieldSpec.toK c) ^ n := by
  induction n with
  | zero => simp [cfpow, CFieldSpec.toK_one]
  | succ n ih => rw [cfpow, CFieldSpec.toK_mul, ih, pow_succ']

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
    rw [clagNumG, toPolyG_cmulG, ih, List.map_cons, List.prod_cons]
    have hfac : toPolyG ([CField.neg z, CField.one] : CPolyG α)
        = Polynomial.X - Polynomial.C (CFieldSpec.toK z) := by
      rw [toPolyG_cons, toPolyG_cons, toPolyG_nil, CFieldSpec.toK_neg, CFieldSpec.toK_one, map_neg,
        map_one]; ring
    rw [hfac]

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

/-- The generic denominator fold `∏ acc·(zk − zⱼ)` equals `toK init · ∏ (toK zk − toK zⱼ)` under `toK`. -/
theorem toK_foldl_csub_mul [CFieldSpec α] (zk : α) (others : List α) (init : α) :
    CFieldSpec.toK (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) init)
      = CFieldSpec.toK init
        * (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod := by
  induction others generalizing init with
  | nil => simp
  | cons z zs ih =>
    rw [List.foldl_cons, ih, CFieldSpec.toK_mul, CFieldSpec.toK_sub, List.map_cons, List.prod_cons]
    ring

end CPolyG

end DeepWiki.SymbolicIntegration
