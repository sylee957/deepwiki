import DeepWiki.ComputableAlgebra.PolyReprBridge
import DeepWiki.ComputableAlgebra.PolyReprSparse

/-! # `CPolyEngine` — a migration-ready polynomial interface

`CPoly` is the thin representation interface (`coeff`/`degBound`/`ofFn`). `CPolyEngine` carries the
polynomial *operations as class fields*, while `LawfulCPolyEngine` carries their denotation squares.
Crucially the `List` instance supplies the **existing engine ops**
(`DensePoly.cadd`/`cmul`/`cnorm`/…), so `CPolyEngine.add (p : List α) = DensePoly.cadd p` **definitionally**
— a declaration re-parametrised over `[CPoly P] [CPolyEngine P]` computes *exactly* the engine's list output at the
`List` instance, so `native_decide` is preserved. This is what makes the engine call-site migration a
behaviour-preserving, defeq-safe re-point (module by module). The `SparsePoly` instance supplies the
generic `ofFn`-based ops, so a migrated module also runs on the sparse carrier. See
`docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- The Prop-free polynomial-engine operations supplied by a concrete representation. -/
class CPolyEngine (P : Type u → Type u) where
  /-- Addition. -/
  add : {α : Type u} → [CCommRing α] → P α → P α → P α
  /-- Multiplication. -/
  mul : {α : Type u} → [CCommRing α] → P α → P α → P α
  /-- Negation. -/
  neg : {α : Type u} → [CCommRing α] → P α → P α
  /-- Monomial construction. -/
  monomial : {α : Type u} → [CCommRing α] → α → ℕ → P α
  /-- Enumerate the represented coefficients from degree zero through the representation bound. -/
  coeffList : {α : Type u} → [CCommRing α] → P α → List α
  /-- Build a polynomial representation from a low-to-high coefficient list. -/
  ofCoeffList : {α : Type u} → [CCommRing α] → List α → P α
  /-- Apply a coefficient function without changing the represented degree bound. -/
  mapCoeffs : {α : Type u} → [CCommRing α] → (α → α) → P α → P α
  /-- Formal derivative. -/
  deriv : {α : Type u} → [CField α] → P α → P α
  /-- Scalar multiplication. -/
  scale : {α : Type u} → [CCommRing α] → α → P α → P α
  /-- Trailing-zero-free canonical form. -/
  cnorm : {α : Type u} → [CCommRing α] → P α → P α
  /-- Zero test. -/
  cisZero : {α : Type u} → [CCommRing α] → P α → Bool
  /-- Honest degree. -/
  cdeg : {α : Type u} → [CCommRing α] → P α → ℕ
  /-- Leading coefficient. -/
  clead : {α : Type u} → [CCommRing α] → P α → α
  /-- Evaluation at a coefficient-ring value. -/
  eval : {α : Type u} → [CCommRing α] → P α → α → α

/-- Denotation laws for a `CPolyEngine`, separated from its computable operations. -/
class LawfulCPolyEngine (P : Type u → Type u) [CPoly P] [CPolyEngine P] : Prop where
  toPoly_add : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p q : P α),
    CPoly.toPoly (CPolyEngine.add p q) = CPoly.toPoly p + CPoly.toPoly q
  toPoly_mul : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p q : P α),
    CPoly.toPoly (CPolyEngine.mul p q) = CPoly.toPoly p * CPoly.toPoly q
  toPoly_neg : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CPoly.toPoly (CPolyEngine.neg p) = - CPoly.toPoly p
  toPoly_monomial : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (c : α) (k : ℕ),
    CPoly.toPoly (CPolyEngine.monomial (P := P) c k) =
      Polynomial.C (CRingSpec.toR c) * Polynomial.X ^ k
  toPoly_coeffList : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    DensePoly.toPoly (CPolyEngine.coeffList p) = CPoly.toPoly p
  toPoly_ofCoeffList : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (xs : List α),
    CPoly.toPoly (CPolyEngine.ofCoeffList (P := P) xs) = DensePoly.toPoly xs
  toR_coeff_mapCoeffs : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α]
      (f : α → α) (_hzero : CRingSpec.toR (f CCommRing.zero) = 0) (p : P α) (i : ℕ),
    CRingSpec.toR (CPoly.coeff (CPolyEngine.mapCoeffs f p) i) =
      CRingSpec.toR (f (CPoly.coeff p i))
  toPoly_deriv : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p : P α),
    CPoly.toPoly (CPolyEngine.deriv p) = (CPoly.toPoly p).derivative
  toPoly_scale : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (c : α) (p : P α),
    CPoly.toPoly (CPolyEngine.scale c p) = Polynomial.C (CRingSpec.toR c) * CPoly.toPoly p
  toPoly_cnorm : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CPoly.toPoly (CPolyEngine.cnorm p) = CPoly.toPoly p
  cisZero_iff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CPolyEngine.cisZero p = true ↔ CPoly.toPoly p = 0
  cdeg_eq_natDegree : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CPolyEngine.cdeg p = (CPoly.toPoly p).natDegree
  toR_clead_eq_leadingCoeff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α),
    CRingSpec.toR (CPolyEngine.clead p) = (CPoly.toPoly p).leadingCoeff
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

end CPolyEngine

/-- **The `List` instance IS the concrete engine** — its ops are `DensePoly.c*`, defeq to the engine's,
so a migrated declaration computes the same list output (⇒ `native_decide`-preserving). -/
instance instEngineList : CPolyEngine List where
  add := DensePoly.cadd
  mul := DensePoly.cmul
  neg := DensePoly.cneg
  monomial := DensePoly.cMonomial
  coeffList p := p
  ofCoeffList xs := xs
  mapCoeffs f p := (p : List _).map f
  deriv := DensePoly.cderiv
  scale := DensePoly.cscale
  cnorm := DensePoly.cnorm
  cisZero := DensePoly.cisZero
  cdeg := DensePoly.cdeg
  clead := DensePoly.clead
  eval := DensePoly.ceval

/-- The concrete dense engine operations satisfy the generic denotation laws. -/
instance instLawfulEngineList : LawfulCPolyEngine List where
  toPoly_add p q := by
    change CPoly.toPoly (DensePoly.cadd p q) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_caddG, ← toPoly_list_eq, ← toPoly_list_eq]
  toPoly_mul p q := by
    change CPoly.toPoly (DensePoly.cmul p q) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cmulG, ← toPoly_list_eq, ← toPoly_list_eq]
  toPoly_neg p := by
    change CPoly.toPoly (DensePoly.cneg p) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cnegG, ← toPoly_list_eq]
  toPoly_monomial c k := by
    change CPoly.toPoly (DensePoly.cMonomial c k) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cMonomial]
  toPoly_coeffList p := (toPoly_list_eq p).symm
  toPoly_ofCoeffList xs := toPoly_list_eq xs
  toR_coeff_mapCoeffs f hzero p i := by
    change CRingSpec.toR (((p : List _).map f).getD i CCommRing.zero) =
      CRingSpec.toR (f ((p : List _).getD i CCommRing.zero))
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (p : List _)[i]? <;> simp [hzero, CRingSpec.toR_zero]
  toPoly_deriv p := by
    change CPoly.toPoly (DensePoly.cderiv p) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cderivG, ← toPoly_list_eq]
  toPoly_scale c p := by
    change CPoly.toPoly (DensePoly.cscale c p) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cscaleG, ← toPoly_list_eq]
  toPoly_cnorm p := by
    change CPoly.toPoly (DensePoly.cnorm p) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cnormG, ← toPoly_list_eq]
  cisZero_iff p := by
    change DensePoly.cisZero p = true ↔ _
    rw [toPoly_list_eq]; exact DensePoly.cisZeroG_iff p
  cdeg_eq_natDegree p := by
    change DensePoly.cdeg p = _
    rw [toPoly_list_eq]; exact DensePoly.cdegG_eq_natDegree p
  toR_clead_eq_leadingCoeff p := by
    change CRingSpec.toR (DensePoly.clead p) = _
    rw [toPoly_list_eq]; exact DensePoly.toR_cleadG_eq_leadingCoeff p
  toR_eval p x := by
    change CRingSpec.toR (DensePoly.ceval p x) = (CPoly.toPoly p).eval (CRingSpec.toR x)
    rw [toPoly_list_eq]
    induction p with
    | nil => simp [DensePoly.ceval, CRingSpec.toR_zero]
    | cons a p ih =>
      simp only [DensePoly.ceval, List.foldr_cons]
      rw [CRingSpec.toR_add, CRingSpec.toR_mul,
        DensePoly.toPolyG_cons, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X]
      change CRingSpec.toR a + CRingSpec.toR x * CRingSpec.toR (DensePoly.ceval p x) = _
      rw [ih]

namespace CPolyEngine

/-- Engine addition on the dense representation is concrete dense addition. -/
@[simp] theorem add_dense_eq {α : Type u} [CCommRing α] (p q : DensePoly α) :
    CPolyEngine.add p q = DensePoly.cadd p q := rfl

/-- Engine multiplication on the dense representation is concrete dense multiplication. -/
@[simp] theorem mul_dense_eq {α : Type u} [CCommRing α] (p q : DensePoly α) :
    CPolyEngine.mul p q = DensePoly.cmul p q := rfl

/-- Engine negation on the dense representation is concrete dense negation. -/
@[simp] theorem neg_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) :
    CPolyEngine.neg p = DensePoly.cneg p := rfl

/-- Engine monomial construction on the dense representation is concrete dense construction. -/
@[simp] theorem monomial_dense_eq {α : Type u} [CCommRing α] (c : α) (k : ℕ) :
    CPolyEngine.monomial (P := DensePoly) c k = DensePoly.cMonomial c k := rfl

/-- Engine coefficient enumeration on the dense representation is the coefficient list itself. -/
@[simp] theorem coeffList_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) :
    CPolyEngine.coeffList p = p := rfl

/-- Engine coefficient-list construction on the dense representation is the identity. -/
@[simp] theorem ofCoeffList_dense_eq {α : Type u} [CCommRing α] (xs : List α) :
    CPolyEngine.ofCoeffList (P := DensePoly) xs = xs := rfl

/-- Engine coefficient mapping on the dense representation is concrete list mapping. -/
@[simp] theorem mapCoeffs_dense_eq {α : Type u} [CCommRing α] (f : α → α) (p : DensePoly α) :
    CPolyEngine.mapCoeffs f p = (p : List α).map f := rfl

/-- The engine degree on the dense representation is the concrete dense degree. -/
@[simp] theorem cdeg_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) :
    CPolyEngine.cdeg p = DensePoly.cdeg p := rfl

/-- The engine leading coefficient on the dense representation is the concrete dense leading coefficient. -/
@[simp] theorem clead_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) :
    CPolyEngine.clead p = DensePoly.clead p := rfl

/-- Engine scaling on the dense representation is concrete dense scaling. -/
@[simp] theorem scale_dense_eq {α : Type u} [CCommRing α] (c : α) (p : DensePoly α) :
    CPolyEngine.scale c p = DensePoly.cscale c p := rfl

/-- Engine normalization on the dense representation is concrete dense normalization. -/
@[simp] theorem cnorm_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) :
    CPolyEngine.cnorm p = DensePoly.cnorm p := rfl

/-- Engine differentiation on the dense representation is concrete dense differentiation. -/
@[simp] theorem deriv_dense_eq {α : Type u} [CField α] (p : DensePoly α) :
    CPolyEngine.deriv p = DensePoly.cderiv p := rfl

/-- Engine subtraction on the dense representation is concrete dense subtraction. -/
@[simp] theorem sub_dense_eq {α : Type u} [CCommRing α] (p q : DensePoly α) :
    CPolyEngine.sub p q = DensePoly.csub p q := rfl

/-- Engine zero testing on the dense representation is concrete dense zero testing. -/
@[simp] theorem cisZero_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) :
    CPolyEngine.cisZero p = DensePoly.cisZero p := rfl

/-- Generic zero specializes to the empty dense coefficient list. -/
@[simp] theorem czero_dense_eq {α : Type u} [CCommRing α] :
    (CPoly.czero : DensePoly α) = [] := rfl

/-- Generic one specializes to the dense singleton coefficient list. -/
@[simp] theorem one_dense_eq {α : Type u} [CCommRing α] :
    (CPoly.one : DensePoly α) = [CCommRing.one] := rfl

/-- Engine list products on the dense representation are concrete dense products. -/
@[simp] theorem prod_dense_eq {α : Type u} [CCommRing α] (ps : List (DensePoly α)) :
    CPolyEngine.prod ps = DensePoly.cprod ps := rfl

/-- Engine evaluation on the dense representation is concrete Horner evaluation. -/
@[simp] theorem eval_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) (x : α) :
    CPolyEngine.eval p x = DensePoly.ceval p x := rfl

end CPolyEngine

/-- **The `SparsePoly` instance** supplies the generic `ofFn`-based ops, so a migrated declaration also
runs on the sparse carrier — the representation-independence payoff at the engine level. -/
instance instEngineSparse : CPolyEngine CPoly.SparsePoly where
  add := CPoly.add
  mul := CPoly.mul
  neg := CPoly.neg
  monomial := CPoly.cmonomial
  coeffList p := (List.range (CPoly.degBound p)).map (CPoly.coeff p)
  ofCoeffList xs := CPoly.ofFn xs.length (fun i => xs.getD i CCommRing.zero)
  mapCoeffs f p := CPoly.ofFn (CPoly.degBound p) (fun i => f (CPoly.coeff p i))
  deriv := CPoly.cderiv
  scale := CPoly.scale
  cnorm := CPoly.cnorm
  cisZero := CPoly.cisZero
  cdeg := CPoly.cdeg
  clead := CPoly.clead
  eval p x := CPoly.ceval x p

/-- The generic sparse engine operations satisfy the generic denotation laws. -/
instance instLawfulEngineSparse : LawfulCPolyEngine CPoly.SparsePoly where
  toPoly_add p q := by change CPoly.toPoly (CPoly.add p q) = _; exact CPoly.toPoly_add p q
  toPoly_mul p q := by change CPoly.toPoly (CPoly.mul p q) = _; exact CPoly.toPoly_mul p q
  toPoly_neg p := by change CPoly.toPoly (CPoly.neg p) = _; exact CPoly.toPoly_neg p
  toPoly_monomial c k := by
    change CPoly.toPoly (CPoly.cmonomial c k) = _
    exact CPoly.toPoly_cmonomial c k
  toPoly_coeffList p := by
    change DensePoly.toPoly
        ((List.range (CPoly.degBound p)).map (CPoly.coeff p)) = CPoly.toPoly p
    apply Polynomial.ext
    intro i
    rw [DensePoly.toPolyG_coeff, CPoly.coeff_toPoly]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : i < CPoly.degBound p
    · rw [List.getElem?_range hi, Option.map_some, Option.getD_some]
    · rw [List.getElem?_eq_none (by simpa using hi), Option.map_none, Option.getD_none,
        CPoly.coeff_ge p i (Nat.le_of_not_gt hi), CRingSpec.toR_zero]
  toPoly_ofCoeffList xs := by
    apply Polynomial.ext
    intro i
    rw [CPoly.coeff_toPoly, DensePoly.toPolyG_coeff]
    change CRingSpec.toR
        (CPoly.coeff
          (CPoly.ofFn xs.length (fun j => xs.getD j CCommRing.zero)) i) = _
    rw [CPoly.coeff_ofFn]
    by_cases hi : i < xs.length
    · rw [if_pos hi]
    · rw [if_neg hi, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi), Option.getD_none]
  toR_coeff_mapCoeffs f hzero p i := by
    change CRingSpec.toR
        (CPoly.coeff
          (CPoly.ofFn (CPoly.degBound p) (fun j => f (CPoly.coeff p j))) i) = _
    rw [CPoly.coeff_ofFn]
    split
    · rfl
    · rename_i hi
      rw [CPoly.coeff_ge p i (Nat.le_of_not_gt hi), CRingSpec.toR_zero, hzero]
  toPoly_deriv p := by
    change CPoly.toPoly (CPoly.cderiv p) = (CPoly.toPoly p).derivative
    exact CPoly.toPoly_cderiv p
  toPoly_scale c p := by change CPoly.toPoly (CPoly.scale c p) = _; exact CPoly.toPoly_scale c p
  toPoly_cnorm p := by change CPoly.toPoly (CPoly.cnorm p) = _; exact CPoly.toPoly_cnorm p
  cisZero_iff p := by change CPoly.cisZero p = true ↔ _; exact CPoly.cisZero_iff p
  cdeg_eq_natDegree p := by change CPoly.cdeg p = _; exact CPoly.cdeg_eq_natDegree p
  toR_clead_eq_leadingCoeff p := by
    change CRingSpec.toR (CPoly.clead p) = _
    exact CPoly.toR_clead_eq_leadingCoeff p
  toR_eval p x := by
    change CRingSpec.toR (CPoly.ceval x p) = (CPoly.toPoly p).eval (CRingSpec.toR x)
    exact CPoly.toR_ceval x p

/-! ### The engine ops are the `List`-instance ops (defeq), so `native_decide` is preserved -/

/-- A declaration re-parametrised over `[CPoly P] [CPolyEngine P]` computes exactly the engine output at `List`. -/
example : (CPolyEngine.mul (CPolyEngine.add ([1,2] : List ℚ) [3,4]) [1])
    = DensePoly.cmul (DensePoly.cadd [1,2] [3,4]) [1] := by native_decide

end DeepWiki.SymbolicIntegration
