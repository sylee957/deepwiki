import DeepWiki.ComputableAlgebra.PolyEngineCore
import DeepWiki.ComputableAlgebra.PolyReprDegree

/-! # Lawful computable-polynomial engines

`LawfulCPolyEngine` records denotation laws for the Prop-free `CPolyEngine` operations. The
interface is representation-neutral: list serialization is read through `CPoly.ofList`, not through
the dense list representation. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Denotation laws for a `CPolyEngine`, separated from its computable operations. -/
class LawfulCPolyEngine (P : Type u → Type u) [CPoly P] [CPolyEngine P] : Prop where
  /-- Addition realizes polynomial addition. -/
  toPoly_add : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p q : P α),
    CPoly.toPoly (CPolyEngine.add p q) = CPoly.toPoly p + CPoly.toPoly q
  /-- Multiplication realizes polynomial multiplication. -/
  toPoly_mul : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p q : P α),
    CPoly.toPoly (CPolyEngine.mul p q) = CPoly.toPoly p * CPoly.toPoly q
  /-- Negation realizes polynomial negation. -/
  toPoly_neg : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CPoly.toPoly (CPolyEngine.neg p) = - CPoly.toPoly p
  /-- Monomial construction realizes `C c * X^k`. -/
  toPoly_monomial : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (c : α) (k : ℕ),
    CPoly.toPoly (CPolyEngine.monomial (P := P) c k) =
      Polynomial.C (CRingSpec.toR c) * Polynomial.X ^ k
  /-- Enumerating then generically rebuilding coefficients preserves denotation. -/
  toPoly_coeffList : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CPoly.toPoly (CPoly.ofList (P := P) (CPolyEngine.coeffList p)) = CPoly.toPoly p
  /-- Engine coefficient-list construction realizes generic list construction. -/
  toPoly_ofCoeffList : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (xs : List α),
    CPoly.toPoly (CPolyEngine.ofCoeffList (P := P) xs) = CPoly.toPoly (CPoly.ofList (P := P) xs)
  /-- Coefficient mapping realizes coefficientwise mapping under denotation. -/
  toR_coeff_mapCoeffs : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α]
      (f : α → α) (_hzero : CRingSpec.toR (f CCommRing.zero) = 0) (p : P α) (i : ℕ),
    CRingSpec.toR (CPoly.coeff (CPolyEngine.mapCoeffs f p) i) =
      CRingSpec.toR (f (CPoly.coeff p i))
  /-- Formal derivative realizes polynomial differentiation. -/
  toPoly_deriv : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p : P α),
    CPoly.toPoly (CPolyEngine.deriv p) = (CPoly.toPoly p).derivative
  /-- Scaling realizes coefficient embedding and multiplication. -/
  toPoly_scale : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (c : α) (p : P α),
    CPoly.toPoly (CPolyEngine.scale c p) = Polynomial.C (CRingSpec.toR c) * CPoly.toPoly p
  /-- Normalization preserves denotation. -/
  toPoly_cnorm : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CPoly.toPoly (CPolyEngine.cnorm p) = CPoly.toPoly p
  /-- The engine zero test exactly recognizes zero denotation. -/
  cisZero_iff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CPolyEngine.cisZero p = true ↔ CPoly.toPoly p = 0
  /-- The engine degree is the denoted polynomial's natural degree. -/
  cdeg_eq_natDegree : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CPolyEngine.cdeg p = (CPoly.toPoly p).natDegree
  /-- The engine leading coefficient denotes the polynomial leading coefficient. -/
  toR_clead_eq_leadingCoeff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CRingSpec.toR (CPolyEngine.clead p) = (CPoly.toPoly p).leadingCoeff
  /-- Engine evaluation realizes polynomial evaluation. -/
  toR_eval : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α) (x : α),
    CRingSpec.toR (CPolyEngine.eval p x) = (CPoly.toPoly p).eval (CRingSpec.toR x)

namespace CPolyEngine

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
  {α : Type u} [CCommRing α]

/-- Subtraction derived from the engine's addition and negation. -/
def sub (p q : P α) : P α := add p (neg q)

/-- Product of a list of engine polynomials, folded from `1`. -/
def prod (ps : List (P α)) : P α :=
  ps.foldl (fun acc p => mul acc p) CPoly.one

/-- Monic normalization derived from the representation's engine operations. -/
def cmonic {β : Type u} [CField β] (p : P β) : P β :=
  let q := cnorm p
  if cisZero q then CPoly.czero else scale (CField.inv (clead q)) q

/-- Bundle engine operations as a local computable ring; use with `letI` to avoid global instance overlap. -/
@[reducible] def toCCommRing : CCommRing (P α) where
  zero := CPoly.czero
  one := CPoly.one
  add := add
  mul := mul
  neg := neg
  isZero := cisZero

/-- Engine subtraction denotes polynomial subtraction. -/
theorem toPoly_sub [LawfulCPolyEngine.{u,v} P] [CRingSpec.{u,v} α] (p q : P α) :
    CPoly.toPoly (sub p q) = CPoly.toPoly p - CPoly.toPoly q := by
  rw [sub, LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_neg, sub_eq_add_neg]

/-- A false engine zero test certifies that the represented polynomial denotes a nonzero polynomial. -/
theorem toPoly_ne_zero_of_cisZero_eq_false [LawfulCPolyEngine.{u,v} P] [CRingSpec.{u,v} α]
    {p : P α} (h : cisZero p = false) : CPoly.toPoly p ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, LawfulCPolyEngine.cisZero_iff] at h
  exact h

/-- An engine polynomial product denotes the product of the denoted factors. -/
theorem toPoly_prod [LawfulCPolyEngine.{u,v} P] [CRingSpec.{u,v} α] (ps : List (P α)) :
    CPoly.toPoly (prod ps) = (ps.map CPoly.toPoly).prod := by
  have hfold : ∀ (xs : List (P α)) (init : P α),
      CPoly.toPoly (xs.foldl (fun acc p => mul acc p) init) =
        CPoly.toPoly init * (xs.map CPoly.toPoly).prod := by
    intro xs
    induction xs with
    | nil => intro init; simp
    | cons p ps ih =>
      intro init
      rw [List.foldl_cons, ih, LawfulCPolyEngine.toPoly_mul]
      simp only [List.map_cons, List.prod_cons]
      ring
  rw [prod, hfold, CPoly.toPoly_one, one_mul]

/-- Engine monic normalization denotes zero on a zero polynomial. -/
theorem toPoly_cmonic_of_eq_zero [LawfulCPolyEngine.{u,v} P]
    {β : Type u} [CField β] [CFieldSpec.{u,v} β] (p : P β) (hp : CPoly.toPoly p = 0) :
    CPoly.toPoly (cmonic p) = 0 := by
  rw [cmonic]
  have hzero : CPolyEngine.cisZero (CPolyEngine.cnorm p) = true ↔ CPoly.toPoly p = 0 := by
    rw [LawfulCPolyEngine.cisZero_iff, LawfulCPolyEngine.toPoly_cnorm]
  rw [if_pos (hzero.mpr hp), CPoly.toPoly_czero]

/-- Engine monic normalization denotes inverse-leading-coefficient scaling on a nonzero polynomial. -/
theorem toPoly_cmonic_of_ne_zero [LawfulCPolyEngine.{u,v} P]
    {β : Type u} [CField β] [CFieldSpec.{u,v} β] (p : P β) (hp : CPoly.toPoly p ≠ 0) :
    CPoly.toPoly (cmonic p) =
      Polynomial.C (CPoly.toPoly p).leadingCoeff⁻¹ * CPoly.toPoly p := by
  rw [cmonic]
  have hzero : CPolyEngine.cisZero (CPolyEngine.cnorm p) = true ↔ CPoly.toPoly p = 0 := by
    rw [LawfulCPolyEngine.cisZero_iff, LawfulCPolyEngine.toPoly_cnorm]
  have hz : ¬ CPolyEngine.cisZero (CPolyEngine.cnorm p) = true := fun h => hp (hzero.mp h)
  rw [if_neg hz, LawfulCPolyEngine.toPoly_scale, LawfulCPolyEngine.toPoly_cnorm]
  congr 2
  change CFieldSpec.toK (CField.inv (CPolyEngine.clead (CPolyEngine.cnorm p))) = _
  rw [CFieldSpec.toK_inv]
  change (CRingSpec.toR (CPolyEngine.clead (CPolyEngine.cnorm p)))⁻¹ = _
  rw [LawfulCPolyEngine.toR_clead_eq_leadingCoeff, LawfulCPolyEngine.toPoly_cnorm]

end CPolyEngine

end DeepWiki.SymbolicIntegration
